import time
import re
import z3

from sklearn.preprocessing import normalize

import utils
from solvers import *
from enum import Enum
from utils import *

instance_id = 0
new_trace_number = 0
unique_traces = set()
instance_groups = defaultdict()
solver = 'spacer'
output_dir = 'output/'


def set_solver(cur_solver: str):
    global solver
    solver = cur_solver


def set_output_dir(cur_output_dir: str):
    global output_dir
    output_dir = cur_output_dir


class Family(Enum):
    UNKNOWN = 0
    ARITH = 1
    ARRAY = 2


class InstanceGroup(object):

    def __init__(self, id: int, filename: str):
        instance_groups[id] = self
        self.id = id
        self.filename = filename
        self.instances = defaultdict(Instance)
        self.same_stats = 0
        self.same_stats_limit = 0
        self.is_linear = True
        self.upred_num = 0
        self.family = Family.UNKNOWN
        self.trace_number = 0
        self.mutation_number = 0

    def __getitem__(self, index: int):
        index = index % len(self.instances)
        return self.instances[index]

    def __setitem__(self, index: int, instance):
        index = index % len(self.instances)
        self.instances[index] = instance

    def __deepcopy__(self, memodict):
        group_id = len(instance_groups)
        result = InstanceGroup(group_id, self.filename)
        memodict[id(self)] = result
        for k, v in self.__dict__.items():
            setattr(result, k, deepcopy(v, memodict))
        return result

    def copy_info(self, src_group):
        for k, v in src_group.__dict__.items():
            if k not in {'id', 'filename', 'instances'}:
                setattr(self, k, deepcopy(v))

    def push(self, instance):
        """Add an instance to the group."""
        instance.group_id = self.id
        self.trace_number += new_trace_number
        self.mutation_number += 1

        group_len = len(self.instances)
        is_seed = group_len == 0

        if is_seed:
            instance.find_pred_info(is_seed)
            if self.family == Family.UNKNOWN and instance.chc:
                self.find_family(instance.chc)
            self.dump_declarations()
        else:
            prev_instance = self[-1]
            instance.mutation.add_after(prev_instance.mutation)

        self.instances[group_len] = instance

    def dump_declarations(self):
        filename = output_dir + 'decl/' + self.filename
        with open(self.filename, 'r') as seed_file:
            file = seed_file.read()
            formula = re.sub(r"\(set-info.*\"\)", "",
                             file, flags=re.DOTALL)
            declarations = formula.split('(assert')[0]
            with open(filename, 'w') as decl_file:
                decl_file.write(declarations)

    def pop(self):
        """Take an instance from the group."""
        length = len(self.instances)
        return self.instances.pop(length - 1)

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self[0]
        self.reset(1)
        self.instances = {0: seed}
        seed.get_chc(is_seed=True)

    def check_stats(self):
        """
        Increase the counter if the current trace is the same as the previous
        one. Reset the number of steps before sorting instances if their
        traces repeat long enough.
        """
        assert len(self.instances) >= 2, 'Not enough instances to compare'
        i = len(self.instances) - 1
        instance = self.instances[i]
        prev_instance = self.instances[i - 1]
        if instance.trace_stats.hash == prev_instance.trace_stats.hash:
            self.same_stats += 1
        else:
            self.same_stats = 0
        if self.same_stats >= self.same_stats_limit:
            probability = (self.same_stats_limit - 1) / self.same_stats
            choice = np.random.choice([False, True], 1,
                                      p=[probability, 1 - probability])
            if choice:
                self.roll_back()
                return 0

    def restore_seed(self):
        seed = parse_smt2_file(self.filename, ctx=ctx.current_ctx)
        instance = Instance(seed)
        self.push(instance)
        return instance

    def restore(self, mutations):
        instance = self.restore_seed()

        for mut in mutations:
            mut_instance = Instance()
            mut_instance.mutation.restore(mut)
            try:
                mut_instance.mutation.apply(instance, mut_instance)
                self.push(mut_instance)
                instance = mut_instance
            except (AssertionError, Z3Exception):
                print(self.filename)
                message = traceback.format_exc()
                print(message)
                continue

    def reset(self, start_ind: int = None):
        length = len(self.instances)
        if start_ind is None:
            start_ind = 0
        for i in range(length - 1, start_ind - 1, -1):
            self[i].reset_chc()

    def find_family(self, chc):
        assert chc is not None, "Empty chc-system"

        length = len(chc) if isinstance(chc, AstVector) else 1
        for i in range(length):
            clause = chc[i] if isinstance(chc, AstVector) else chc
            vars, _ = get_vars_and_body(clause)
            for var in vars:
                if is_arith(var):
                    self.family = Family.ARITH
                elif is_array(var):
                    self.family = Family.ARRAY
                    return


class MutTypeGroup(Enum):
    AUXILIARY = 0
    OWN = 1
    PARAMETERS = 2
    SIMPLIFICATIONS = 3


class MutType(object):

    def __init__(self, name, group: MutTypeGroup, weight=0.1,
                 default_value=None, upper_limit=None):
        self.name = name
        self.group = group
        self.weight = weight
        self.default_value = default_value
        self.upper_limit = upper_limit

    def is_solving_param(self):
        return self.group == MutTypeGroup.PARAMETERS

    def is_simplification(self):
        return self.group == MutTypeGroup.SIMPLIFICATIONS

    def is_remove(self):
        return self.name == 'REMOVE'


def copy_chc(chc_system: AstVector) -> AstVector:
    new_chc_system = AstVector(ctx=ctx.current_ctx)
    for clause in chc_system:
        new_chc_system.push(clause)
    return new_chc_system


class Instance(object):

    def __init__(self, chc: AstVector = None):
        global instance_id
        self.id = instance_id
        instance_id += 1
        self.group_id = -1
        self.chc = None
        if chc is not None:
            self.set_chc(chc)
        self.satis = unknown
        self.trace_stats = TraceStats()
        self.params = {}
        self.model = None
        self.model_info = (sat, 0)
        self.mutation = Mutation()
        self.solve_time = 0

    def set_chc(self, chc: AstVector):
        """Set the chc-system of the instance."""
        assert chc is not None, "Empty chc-system"

        self.chc = chc
        chc_len = len(self.chc)
        if self.group_id >= 0:
            group = self.get_group()
            group.same_stats_limit = 5 * chc_len
        self.info = ClauseInfo(chc_len)

    def __deepcopy__(self, memodict):
        result = Instance()
        memodict[id(self)] = result
        for k, v in self.__dict__.items():
            if k == 'chc':
                result.set_chc(copy_chc(self.chc))
            else:
                setattr(result, k, deepcopy(v, memodict))
        return result

    def get_chc(self, is_seed: bool):
        if self.chc is None:
            self.restore(is_seed=is_seed)
        return self.chc

    def add_param(self, mut_type: MutType):
        mut_name = mut_type.name
        param = mut_name.lower()
        upper_limit = mut_type.upper_limit
        if upper_limit is None:
            value = self.params[param] \
                if param in self.params \
                else mut_type.default_value
            self.params[param] = not value
        else:
            self.params[param] = random.randint(0, upper_limit + 1)

    def process_seed_info(self, info: dict):
        self.satis = CheckSatResult(info['satis'])
        _trace_states = [State.load(state_date) for state_date in info['trace_states']]
        self.trace_stats.load_states(_trace_states)
        return info['time']

    def reset_chc(self):
        self.chc = None
        self.model = None

    # @profile(immediate=True)
    def check(self, group: InstanceGroup, is_seed: bool = False):
        """Check the satisfiability of the instance."""
        timeout = SEED_SOLVE_TIME_LIMIT_MS if is_seed else MUT_SOLVE_TIME_LIMIT_MS

        if solver == 'spacer':
            cur_solver = SolverFor('HORN', ctx=ctx.current_ctx)
            cur_solver.set('engine', 'spacer')
            for param in self.params:
                value = self.params[param]
                cur_solver.set(param, value)
            self.trace_stats.reset_trace_offset()
            cur_solver.set('timeout', timeout)
            chc_system = self.get_chc(is_seed)
            cur_solver.add(chc_system)

            self.satis = cur_solver.check()
            if self.satis == sat:
                self.model = cur_solver.model()
            reason_unknown = cur_solver.reason_unknown()

        elif solver == 'eldarica':
            if not is_seed:
                self.dump(output_dir + 'last_mutants/',
                          group.filename,
                          clear=False)
                filename = output_dir + 'last_mutants/' + group.filename
            else:
                filename = group.filename

            state, reason_unknown = eldarica_check(filename, timeout/MS_IN_SEC)
            self.satis = globals()[state]

        assert self.satis != unknown, reason_unknown

    def check_model(self):
        if self.satis != sat:
            return None
        assert self.model is not None, "Empty model"

        solver = Solver(ctx=ctx.current_ctx)
        solver.set('timeout', MODEL_CHECK_TIME_LIMIT)
        for i, clause in enumerate(self.chc):
            inter_clause = self.model.eval(clause)
            solver.add(inter_clause)
            model_state = solver.check()
            if model_state != sat:
                self.model_info = (model_state, i)
                break

        if self.model_info[0] == unknown:
            return solver.reason_unknown()
        return None

    def update_traces_info(self, is_seed: bool = False):
        global new_trace_number

        prev_trace_number = len(unique_traces)
        unique_traces.add(self.trace_stats.hash)
        if not is_seed:
            cur_trace_number = len(unique_traces)
            new_trace_number = cur_trace_number - prev_trace_number
            self.inc_mutation_stats('new_traces', new_trace_number)

    def get_group(self):
        """Return the group of the instance."""
        return instance_groups[self.group_id]

    def get_log(self, group: InstanceGroup, is_mutant: bool = True) -> dict:
        """Create a log entry with information about the instance."""
        log = {'filename': group.filename, 'id': self.id}
        if is_mutant:
            log['prev_inst_id'] = group[-1].id
            log['mut_type'] = self.mutation.get_name()
        return log

    def find_system_info(self):
        if self.chc is None or mut_groups[0] != MutTypeGroup.OWN:
            return

        info = self.info
        info.expr_num = count_expr(self.chc, info_kinds)

    def find_clause_info(self, kind):
        info = self.info
        chc_len = len(self.chc)
        ind = list(range(chc_len))
        random.shuffle(ind)
        info_len = len(info.clause_expr_num[Z3_OP_UNINTERPRETED])
        if info_len < len(self.chc):
            info.clause_expr_num[kind].resize(chc_len)

        while ind:
            i = ind.pop()
            clause = self.chc[i]
            expr_num = count_expr(clause, info_kinds)
            info.clause_expr_num[kind][i] = expr_num[kind]
            if expr_num[kind]:
                return i

    def find_pred_info(self, is_seed: bool):
        """
        Find whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        if utils.heuristic not in {'difficulty', 'simplicity'}:
            return
        if self.chc is None:
            self.restore(is_seed=is_seed)
        chc_system = self.chc
        group = self.get_group()

        for i, clause in enumerate(chc_system):
            body = get_chc_body(clause)

            if body is not None:
                stats = count_expr(body, [Z3_OP_UNINTERPRETED], is_unique=True)
                upred_num = stats[Z3_OP_UNINTERPRETED]
                if upred_num > 1:
                    group.is_linear = False

        stats = count_expr(chc_system, [Z3_OP_UNINTERPRETED], is_unique=True)
        group.upred_num = stats[Z3_OP_UNINTERPRETED]

    def restore(self, is_seed: bool = False):
        group = self.get_group()
        filename = group.filename if is_seed else \
            output_dir + 'last_mutants/' + group.filename
        self.set_chc(z3.parse_smt2_file(filename, ctx=ctx.current_ctx))
        assert len(self.chc) > 0, "Empty chc-system"

    def dump(self, dir: str, filename: str, message: str = None,
             declarations: str = None, to_name=None, clear: bool = True):
        """Dump the instance to the specified directory."""
        if not declarations:
            decl_path = output_dir + 'decl/' + filename
            with open(decl_path, 'r') as decl_file:
                declarations = decl_file.read()
        cur_path = dir + '/' + filename
        if to_name:
            cur_path = cur_path[:-5] + '_' + str(to_name) + '.smt2'
        with open(cur_path, 'w') as file:
            mut_info = self.mutation.get_chain(format='log')
            file.write('; ' + json.dumps(mut_info) + '\n')
            if message:
                file.write('; ' + message + '\n')
            file.write(declarations)
            for clause in self.chc:
                file.write('(assert ' + clause.sexpr() + ')\n')
            file.write('(check-sat)\n(exit)\n\n')

        if clear:
            self.reset_chc()

    def inc_mutation_stats(self, stats_name: str, value: int = 1):
        global mut_stats

        mut_name = self.mutation.type.name
        current_mutation_stats = \
            mut_stats.setdefault(mut_name,
                                 {'applications': 0.0,
                                  'new_traces': 0.0,
                                  'new_transitions': 0.0,
                                  'changed_traces': 0.0})
        current_mutation_stats[stats_name] += value


class MutTypeEncoder(json.JSONEncoder):

    def default(self, obj):
        if isinstance(obj, MutType):
            return obj.__dict__
        return json.JSONEncoder.default(self, obj)


mut_types = {'ID': MutType('ID', MutTypeGroup.AUXILIARY),
             'REMOVE_EXPR': MutType('REMOVE_EXPR', MutTypeGroup.AUXILIARY)}
mut_stats = {}
with_weights = True
mut_groups = []


def get_mut_weights_dict():
    mut_weight_dict = dict()
    for mut_name in mut_types:
        mut_weight_dict[mut_name] = mut_types[mut_name].weight
    return mut_weight_dict


def init_mut_types(options: list = None, mutations: list = None):
    global mut_types, with_weights, mut_groups

    if 'without_mutation_weights' in options:
        with_weights = False

    if 'own' in mutations:
        mut_groups.append(MutTypeGroup.OWN)
        for name in {'SWAP_AND',
                     'DUP_AND',
                     'BREAK_AND',
                     'SWAP_OR',
                     'MIX_BOUND_VARS',
                     'ADD_INEQ'}:
            mut_types[name] = MutType(name, MutTypeGroup.OWN)

    if solver == 'spacer' and 'spacer_parameters' in mutations:
        mut_groups.append(MutTypeGroup.PARAMETERS)
        for name in DISABLED_SPACER_CORE_PARAMETERS | DISABLED_PARAMETERS:
            upper_name = name.upper()
            mut_types[upper_name] = MutType(upper_name, MutTypeGroup.PARAMETERS, default_value=False)

        for name in ENABLED_SPACER_CORE_PARAMETERS | ENABLED_PARAMETERS:
            upper_name = name.upper()
            mut_types[upper_name] = MutType(upper_name, MutTypeGroup.PARAMETERS, default_value=True)

        mut_types['SPACER.ORDER_CHILDREN'] = \
            MutType('SPACER.ORDER_CHILDREN',
                    MutTypeGroup.PARAMETERS,
                    default_value=0,
                    upper_limit=2)

        mut_types['SPACER.RANDOM_SEED'] = \
            MutType('SPACER.RANDOM_SEED',
                    MutTypeGroup.PARAMETERS,
                    default_value=0,
                    upper_limit=sys.maxsize)

    if 'simplifications' in mutations:
        mut_groups.append(MutTypeGroup.SIMPLIFICATIONS)
        name = 'EMPTY_SIMPLIFY'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Rewrite inequalities so that right-hand-side is a constant."""
        name = 'ARITH_INEQ_LHS'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        All monomials are moved to the left-hand-side, 
        and the right-hand-side is just a constant."""
        name = 'ARITH_LHS'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Expand a distinct predicate into a quadratic number of disequalities."""
        name = 'BLAST_DISTINCT'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Eagerly replace all (select (store ..) ..) term 
        by an if-then-else term."""
        name = 'BLAST_SELECT_STORE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Conjunctions are rewritten using negation and disjunctions."""
        name = 'ELIM_AND'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y)))."""
        name = 'ELIM_REM'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Eliminate to_real from arithmetic predicates 
        that contain only integers."""
        name = 'ELIM_TO_REAL'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Expand equalities into two inequalities."""
        name = 'EQ2INEQ'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Expand (^ t k) into (* t ... t) if  1 < k <= max_degree."""
        name = 'EXPAND_POWER'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Expand select over ite expressions."""
        name = 'EXPAND_SELECT_ITE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Conservatively replace a (select (store ...) ...) term 
        by an if-then-else term."""
        name = 'EXPAND_SELECT_STORE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Reduce (store ...) = (store ...) with a common base into selects."""
        name = 'EXPAND_STORE_EQ'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Replace (tan x) with (/ (sin x) (cos x))."""
        name = 'EXPAND_TAN'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Use gcd rounding on integer arithmetic atoms."""
        name = 'GCD_ROUNDING'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Hoist shared summands under ite expressions."""
        name = 'HOIST_ITE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Hoist multiplication over summation 
        to minimize number of multiplications."""
        name = 'HOIST_MUL'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Extra ite simplifications, these additional simplifications 
        may reduce size locally but increase globally."""
        name = 'ITE_EXTRA_RULES'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Perform local (i.e. cheap) context simplifications."""
        name = 'LOCAL_CTX'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Replace multiplication by a power of two into a concatenation."""
        name = 'MUL2CONCAT'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Collpase (* t ... t) into (^ t k), 
        it is ignored if expand_power is true."""
        name = 'MUL_TO_POWER'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Pull if-then-else terms when cheap."""
        name = 'PULL_CHEAP_ITE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Push if-then-else over arithmetic terms."""
        name = 'PUSH_ITE_ARITH'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Rewrite patterns."""
        name = 'REWRITE_PATTERNS'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Put polynomials in sum-of-monomials form."""
        name = 'SOM'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Sort nested stores when the indices are known to be different."""
        name = 'SORT_STORE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Sort the arguments of + application."""
        name = 'SORT_SUMS'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Split equalities of the form (= (concat t1 t2) t3)."""
        name = 'SPLIT_CONCAT_EQ'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)

        """
        Simplify/evaluate expressions containing 
        (algebraic) irrational numbers."""
        name = 'ALGEBRAIC_NUMBER_EVALUATOR'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Eliminate ite in favor of and/or."""
        name = 'ELIM_ITE'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Expand sign-ext operator using concat and extract."""
        name = 'ELIM_SIGN_EXT'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Create nary applications for and, or, +, *, 
        bvadd, bvmul, bvand, bvor, bvxor."""
        name = 'FLAT'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Ignores patterns on quantifiers that don't mention 
        their bound variables."""
        name = 'IGNORE_PATTERNS_ON_GROUND_QBODY'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)
        """
        Distribute to_real over * and +."""
        name = 'PUSH_TO_REAL'
        mut_types[name] = MutType(name, MutTypeGroup.SIMPLIFICATIONS)


own_mutations = {'SWAP_AND': Z3_OP_AND, 'DUP_AND': Z3_OP_AND,
                 'BREAK_AND': Z3_OP_AND, 'SWAP_OR': Z3_OP_OR,
                 'MIX_BOUND_VARS': Z3_QUANTIFIER_AST,
                 'ADD_INEQ': {Z3_OP_LE, Z3_OP_GE, Z3_OP_LT, Z3_OP_GT}}

default_simplify_options = {'algebraic_number_evaluator', 'bit2bool',
                            'elim_ite', 'elim_sign_ext', 'flat', 'hi_div0',
                            'ignore_patterns_on_ground_qbody', 'push_to_real'}

array_mutations = {'BLAST_SELECT_STORE', 'EXPAND_SELECT_STORE',
                   'EXPAND_STORE_EQ', 'SORT_STORE', 'XFORM.ARRAY_BLAST_FULL',
                   'XFORM.INSTANTIATE_ARRAYS', 'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
                   'XFORM.QUANTIFY_ARRAYS', 'XFORM.TRANSFORM_ARRAYS'}


def update_mutation_weights():
    global mut_types, mut_stats

    weights = []
    for mut_name in mut_types:
        current_mut_stats = mut_stats.get(mut_name)
        if current_mut_stats is None or mut_name == 'ID':
            continue
        trace_change_probability = current_mut_stats['changed_traces'] / current_mut_stats['applications']
        trace_discover_probability = current_mut_stats['new_traces'] / current_mut_stats['applications']
        new_transitions = current_mut_stats['new_transitions']
        coef = 0.62
        mut_types[mut_name].weight = coef * mut_types[mut_name].weight + \
                                     (1 - coef) * trace_discover_probability
        # weights.append(mut_types[mut_name].weight)

    # factor = 1 / sum(weights)
    # for key in mut_types:
    #     mut_types[key].weight = mut_types[key].weight * factor


class Mutation(object):

    def __init__(self):
        self.type = mut_types['ID']
        self.number = 0
        self.clause_i = None
        self.kind = None
        self.prev_mutation = None
        self.applied = False
        self.trans_num = None
        self.changed = False
        self.is_timeout = False
        self.exceptions = set()

    def add_after(self, prev_mutation):
        self.number = prev_mutation.number + 1
        self.prev_mutation = prev_mutation

    def clear(self):
        self.type = mut_types['ID']
        self.clause_i = None
        self.number = 0
        self.prev_mutation = None

    def apply(self, instance: Instance, new_instance: Instance):
        """Mutate instances."""
        new_instance.params = deepcopy(instance.params)
        self.next_mutation(instance)
        mut_name = self.type.name

        if mut_name == 'ID':
            assert False, 'No mutation can be applied'

        if instance.chc is None:
            print(mut_name)
        assert instance.chc is not None, "Empty chc-system"

        if self.type.is_solving_param():
            new_instance.set_chc(instance.chc)
            new_instance.add_param(self.type)

        st_time = time.perf_counter()
        if mut_name == 'EMPTY_SIMPLIFY':
            new_instance.set_chc(self.empty_simplify(instance.chc))

        elif mut_name in own_mutations:
            new_instance.set_chc(self.transform(instance))

        else:
            new_instance.set_chc(self.simplify_by_one(instance.chc))

        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            self.is_timeout = True

        if instance.chc.sexpr() != new_instance.chc.sexpr():
            self.changed = True

    def set_remove_mutation(self, trans_num):
        self.type = mut_types['REMOVE_EXPR']
        self.trans_num = trans_num
        self.kind = Z3_OP_TRUE

    def next_mutation(self, instance: Instance):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        mult_kinds = defaultdict(list)
        types_to_choose = set()
        group = instance.get_group()
        instance.find_system_info()
        info = instance.info

        mut_group = random.choice(mut_groups)
        mut_name = self.type.name

        if mut_name == 'ID' or \
                (mut_name in own_mutations and self.kind is None):
            if mut_group == MutTypeGroup.OWN:
                search_kind_dict = reverse_dict(own_mutations)
                for kind in info_kinds:
                    if info.expr_num[kind] > 0:
                        types_to_choose.update(search_kind_dict[kind])
                        if kind in own_mutations['ADD_INEQ']:
                            mult_kinds['ADD_INEQ'].append(kind)

        if mut_name == 'ID':
            for mut_name in mut_types:
                if mut_group != mut_types[mut_name].group:
                    continue
                elif mut_name in array_mutations and \
                        group.family != Family.ARRAY:
                    continue
                elif mut_name in instance.params:
                    continue
                elif mut_name not in own_mutations:
                    types_to_choose.add(mut_name)
                else:
                    pass
            types_to_choose = list(types_to_choose.difference(self.exceptions)) \
                if self.exceptions else list(types_to_choose)

            if with_weights:
                reverse_weights = random.choice([True, False]) \
                    if instance.mutation.number + 1 > 0.5 * ONE_INST_MUT_LIMIT \
                    else False
                weights = []
                for name in types_to_choose:
                    weight = mut_types[name].weight
                    if reverse_weights:
                        weight = 1 - weight
                    weights.append(weight)

                mut_name = random.choices(types_to_choose, weights)[0] if types_to_choose else 'ID'
            else:
                mut_name = random.choice(types_to_choose) if types_to_choose else 'ID'
            self.type = mut_types[mut_name]

        if mut_name in own_mutations and self.kind is None:
            if mut_name == 'ADD_INEQ':
                self.kind = random.choices(mult_kinds[mut_name])[0]
            else:
                self.kind = own_mutations[mut_name]
            self.clause_i = instance.find_clause_info(self.kind)

    def simplify_by_one(self, chc_system: AstVector) -> AstVector:
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq."""
        mut_system = AstVector(ctx=ctx.current_ctx)

        mut_name = self.type.name.lower()
        params = [mut_name, True]
        for key in default_simplify_options:
            if key != mut_name:
                params += [key, False]

        ind = range(0, len(chc_system)) if not self.clause_i else {self.clause_i}
        for i in range(len(chc_system)):
            if i in ind:
                cur_clause = AstVector(ctx=ctx.current_ctx)
                cur_clause.push(chc_system[i])
                rewritten_clause = self.empty_simplify(cur_clause)[0]

                clause = simplify(rewritten_clause, *params)

                del cur_clause, rewritten_clause
            else:
                clause = chc_system[i]
            mut_system.push(clause)

        return mut_system

    def empty_simplify(self, chc_system: AstVector) -> AstVector:
        mut_system = AstVector(ctx=ctx.current_ctx)

        for i in range(len(chc_system)):
            clause = simplify(chc_system[i],
                              algebraic_number_evaluator=False,
                              bit2bool=False,
                              elim_ite=False,
                              elim_sign_ext=False,
                              flat=False,
                              hi_div0=False,
                              ignore_patterns_on_ground_qbody=False,
                              push_to_real=False)
            mut_system.push(clause)

        return mut_system

    def add_lin_rule(self, instance: Instance) -> AstVector:
        mut_system = copy_chc(instance.chc)
        _, clause = self.get_clause_info(instance)
        head, vars = take_pred_from_clause(clause)

        body_files = os.listdir('false_formulas')
        body_files.remove('README.md')
        filename = 'false_formulas/' + random.choice(body_files)
        body = parse_smt2_file(filename, ctx=ctx.current_ctx)[0]
        implication = Implies(body, head, ctx=ctx.current_ctx)
        rule = ForAll(vars, implication) if vars else implication
        mut_system.push(rule)

        group = instance.get_group()
        group.find_family(rule)

        return mut_system

    def add_nonlin_rule(self, instance: Instance) -> AstVector:
        mut_system = copy_chc(instance.chc)
        _, clause = self.get_clause_info(instance)
        head_upred, head_vars, upred = take_pred_from_clause(clause, with_term=True)

        body_vars = head_vars
        pred_vars_num = len(body_vars)
        num = random.randint(1, 10)
        var = Int('v' + str(0), ctx=ctx.current_ctx)
        body_vars.append(var)
        vars = [var]
        and_exprs = []
        for i in range(1, num + 1):
            var = FreshConst(IntSort(ctx=ctx.current_ctx), prefix='v')
            vars.append(var)
            body_vars.append(var)
            shuffle_vars(body_vars)
            upred_vars = body_vars[:pred_vars_num] \
                if pred_vars_num else []
            new_upred = upred.__call__(upred_vars)

            expr = var < vars[i - 1]
            and_exprs.append(And(new_upred, expr))

        expr = vars[0] < vars[num]
        and_exprs.append(And(head_upred, expr))
        body = And(and_exprs)
        body = Exists(vars, body)
        implication = Implies(body, head_upred, ctx=ctx.current_ctx)
        rule = ForAll(head_vars, implication) if head_vars else implication

        mut_system.push(rule)
        group = instance.get_group()
        group.find_family(rule)

        return mut_system

    def get_clause_info(self, instance: Instance) -> (int, AstVector):
        info = instance.info
        chc_system = instance.chc

        i = self.clause_i
        if self.trans_num is None:
            expr_num = info.clause_expr_num[self.kind][i]
            self.trans_num = random.randint(0, expr_num - 1) \
                if expr_num > 1 else 0

        system_length = len(chc_system)
        if i < system_length:
            clause = chc_system[i]
            if not self.clause_i:
                self.clause_i = i
        else:
            print(f'IndexError in clause = chc_system[i]: len(chc_system) = {system_length}, i = {i}.')
            self.clear()
            clause = chc_system[0]
        return i, clause

    def transform(self, instance: Instance) -> AstVector:
        """Transform an expression of the specific kind."""
        chc_system = instance.chc
        mut_system = AstVector(ctx=ctx.current_ctx)

        clause_i, clause = self.get_clause_info(instance)
        if self.type.name == 'ID':
            return chc_system

        mut_clause = self.transform_nth(clause)
        if not self.applied:
            assert False, 'Mutation ' + \
                          self.type.name + \
                          ' wasn\'t applied'

        for j, clause in enumerate(chc_system):
            if j == clause_i:
                if mut_clause is not None:
                    mut_system.push(mut_clause)
            else:
                mut_system.push(chc_system[j])
        return mut_system

    def transform_nth(self, clause):
        """Transform nth expression of the specific kind in dfs-order."""
        expr_kind = self.kind
        if expr_kind is Z3_QUANTIFIER_AST:
            expr, path = find_term(clause, Z3_OP_TRUE, self.trans_num, False, True)
        else:
            expr, path = find_term(clause, expr_kind, self.trans_num, self.type.is_remove(), False)
        assert not is_false(expr), 'Subexpression not found: ' + str(self.get_chain(format='log'))
        mut_expr = None
        mut_name = self.type.name
        children = expr.children()

        if mut_name in {'SWAP_AND', 'SWAP_OR'}:
            children = children[1:] + children[:1]
        elif mut_name == 'DUP_AND':
            child = children[0]
            children.append(child)
        elif mut_name == 'BREAK_AND':
            children = mut_break(children)
        elif mut_name == 'ADD_INEQ':
            new_ineq = create_add_ineq(children, expr_kind)
            mut_expr = And([expr, new_ineq])
        else:
            pass

        if expr_kind == Z3_OP_AND:
            mut_expr = And(children)
        elif expr_kind == Z3_OP_OR:
            mut_expr = Or(children)
        elif expr_kind == Z3_QUANTIFIER_AST:
            vars, _ = get_vars_and_body(expr)
            shuffle_vars(vars)
            mut_expr = update_quantifier(expr, children, vars)
        else:
            pass

        mut_clause = set_term(clause, mut_expr, path)
        self.applied = True
        return mut_clause

    def get_chain(self, format='list'):
        """Return the full mutation chain."""
        if format == 'log':
            chain = [self.get_log()]
        elif format == 'list':
            chain = [self.get_name()]
        else:
            assert False, "Unknown output format"
        cur_mutation = self
        for i in range(self.number, 1, -1):
            cur_mutation = cur_mutation.prev_mutation
            if format == 'log':
                cur_log = [cur_mutation.get_log()]
                chain = cur_log + chain
            elif format == 'list':
                mut_name = [cur_mutation.get_name()]
                chain = mut_name + chain
            else:
                assert False, "Unknown output format"
        return chain

    def same_chain_start(self, other) -> bool:
        fst_chain = self.get_chain()
        snd_chain = other.get_chain()
        fst_len = len(fst_chain)
        snd_len = len(snd_chain)
        length = fst_len if fst_len < snd_len else snd_len
        for i, mut in enumerate(fst_chain[:(length // 2)]):
            if mut != snd_chain[i]:
                return False
        return True

    def get_name(self):
        """Get mutation name with some information about it."""
        mut_name = self.type.name

        if mut_name == 'ADD_INEQ':
            return mut_name + '(' + \
                str(self.kind) + ', ' + \
                str(self.clause_i) + ', ' + \
                str(self.trans_num) + ')'

        elif mut_name in own_mutations:
            return mut_name + '(' + \
                str(self.clause_i) + ', ' + \
                str(self.trans_num) + ')'

        else:
            return mut_name

    def debug_print(self, chc_system: AstVector, mut_system: AstVector):
        print(chc_system[self.clause_i], '\n->\n', mut_system[self.clause_i])

    def get_log(self) -> dict:
        """Create a log entry with information about the mutation."""
        log = {'type': self.type.name,
               'clause_i': self.clause_i,
               'kind': self.kind,
               'trans_num': self.trans_num,
               }
        return log

    def restore(self, mut_entry):
        """Restore mutations by log or chain."""
        if type(mut_entry) == dict:
            for field in mut_entry:
                if field == 'type':
                    mut_name = mut_entry[field]
                    self.type = mut_types[mut_name]
                else:
                    setattr(self, field, mut_entry[field])

        elif type(mut_entry) == str and mut_entry != 'nan':
            mut_info = re.findall(r"[\w.]+|[0-9]", mut_entry)
            mut_name = mut_info[0]
            self.type = mut_types[mut_name]

            if mut_name == 'ADD_INEQ':
                self.kind = int(mut_info[1])
                self.clause_i = int(mut_info[2])
                self.trans_num = int(mut_info[3])
            elif mut_name in own_mutations:
                self.clause_i = int(mut_info[1])
                self.trans_num = int(mut_info[2])
        else:
            assert False, 'Incorrect mutation entry'


def mut_break(children):
    """
    Return the children of the expression
    after applying the mutation BREAK_AND
    """

    children_part = children[-2:]
    if len(children) == 2:
        mut_children = children[:-1]
    else:
        mut_children = children[:-2]
    mut_children.append(And(children_part))
    return mut_children


def create_add_ineq(children, expr_kind: int) -> BoolRef:
    """Return a stronger inequality than given."""

    if expr_kind in {Z3_OP_LE, Z3_OP_LT}:
        new_child = children[1] + 1
        new_ineq = children[0] < new_child
    elif expr_kind in {Z3_OP_GE, Z3_OP_GT}:
        new_child = children[1] - 1
        new_ineq = children[0] > new_child
    else:
        assert False, 'Incorrect kind of expression'
    return new_ineq
