import time
import re
import utils
from utils import *

MUT_APPLY_TIME_LIMIT = 10
SEED_SOLVE_TIME_LIMIT_MS = int(2 * 1e3)
MUT_SOLVE_TIME_LIMIT_MS = int(1e5)

MODEL_CHECK_TIME_LIMIT = 100
INSTANCE_ID = 0
ONE_INST_MUT_LIMIT = 100

unique_traces = set()
instance_groups = defaultdict()
current_ctx = None


def set_ctx(ctx):
    global current_ctx
    current_ctx = ctx
    utils.set_ctx(ctx)


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

        if self.upred_num == 0:
            instance.find_pred_info()
            if self.family == Family.UNKNOWN and instance.chc:
                self.find_family(instance.chc)

        group_len = len(self.instances)
        if group_len == 0:
            self.dump_declarations()
        else:
            prev_instance = self[-1]
            instance.mutation.add_after(prev_instance.mutation)

        self.instances[group_len] = instance

    def dump_declarations(self):
        filename = 'output/decl/' + self.filename
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

    def restore(self, id: int, mutations):
        seed = parse_smt2_file(self.filename, ctx=current_ctx)
        instance = Instance(seed)
        self.push(instance)

        for mut in mutations:
            mut_instance = Instance()
            mut_instance.mutation.restore(mut)
            try:
                mut_instance.mutation.apply(instance, mut_instance)
                self.push(mut_instance)
                instance = mut_instance
            except (AssertionError, Z3Exception):
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
    new_chc_system = AstVector(ctx=current_ctx)
    for clause in chc_system:
        new_chc_system.push(clause)
    return new_chc_system


class Instance(object):

    def __init__(self, chc: AstVector = None):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = -1
        self.chc = None
        if chc is not None:
            self.set_chc(chc)
        self.satis = unknown
        self.trace_stats = TraceStats()
        self.sort_key = 0
        self.params = {}
        self.model = None
        self.model_info = (sat, 0)
        self.mutation = Mutation()

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

    def check(self, solver: Solver, is_seed: bool = False,
              get_stats: bool = True):
        """Check the satisfiability of the instance."""
        solver.reset()
        self.trace_stats.reset_trace_offset()
        if is_seed:
            solver.set('timeout', SEED_SOLVE_TIME_LIMIT_MS)
        else:
            solver.set('timeout', MUT_SOLVE_TIME_LIMIT_MS)

        chc_system = self.get_chc(is_seed)
        solver.add(chc_system)

        self.satis = solver.check()
        if self.satis == sat:
            self.model = solver.model()

        if get_stats:
            self.trace_stats.read_from_trace(is_seed)
            self.update_traces_info()

        assert self.satis != unknown, solver.reason_unknown()

    def check_model(self):
        if self.satis != sat:
            return None
        assert self.model is not None, "Empty model"

        solver = Solver(ctx=current_ctx)
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

    def update_traces_info(self):
        unique_traces.add(self.trace_stats.hash)

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
        """
        Get information about the number of subexpressions of kind
        from info_kinds in the system and clauses.
        """
        if self.chc is None or mut_groups[0] != MutTypeGroup.OWN:
            return

        info = self.info
        info.expr_num = count_expr(self.chc, info_kinds)

        info_len = len(info.clause_expr_num[Z3_OP_UNINTERPRETED])
        if info_len < len(self.chc):
            for kind in info_kinds:
                info.clause_expr_num[kind].resize(len(self.chc))

        for i, clause in enumerate(self.chc):
            expr_num = count_expr(clause, info_kinds)
            for kind in info_kinds:
                info.clause_expr_num[kind][i] = expr_num[kind]

    def find_pred_info(self):
        """
        Find whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        if mut_groups[0] != MutTypeGroup.OWN and \
                heuristic not in {'difficulty', 'simplicity'}:
            return
        group = self.get_group()
        chc_system = self.chc
        if chc_system is None:
            return

        for i, clause in enumerate(chc_system):
            body = get_chc_body(clause)

            if body is not None:
                upred_num = count_expr(body,
                                       [Z3_OP_UNINTERPRETED],
                                       is_unique=True)[0]
                if upred_num > 1:
                    group.is_linear = False

        group.upred_num = count_expr(chc_system,
                                     [Z3_OP_UNINTERPRETED],
                                     is_unique=True)[0]

    def restore(self, is_seed: bool = False):
        """Restore the instance from output/last_mutants/."""
        group = self.get_group()
        filename = group.filename if is_seed else \
            'output/last_mutants/' + group.filename
        self.set_chc(z3.parse_smt2_file(filename, ctx=current_ctx))
        assert len(self.chc) > 0, "Empty chc-system"

    def dump(self, dir: str, filename: str, message: str = None,
             declarations: str = None, to_name=None, clear: bool = True):
        """Dump the instance to the specified directory."""
        if not declarations:
            decl_path = 'output/decl/' + filename
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

    def update_mutation_stats(self, new_application: bool = False, new_trace_found: bool = False):
        global mut_stats

        mut_name = self.mutation.type.name
        current_mutation_stats = \
            mut_stats.setdefault(mut_name,
                                 {'applications': 0.0, 'new_traces': 0.0})
        current_mutation_stats['applications'] += int(new_application)
        current_mutation_stats['new_traces'] += int(new_trace_found)


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

    if not mutations or 'own' in mutations:
        mut_groups.append(MutTypeGroup.OWN)
        for name in {'SWAP_AND',
                     'DUP_AND',
                     'BREAK_AND',
                     'SWAP_OR',
                     'MIX_BOUND_VARS',
                     'ADD_INEQ',
                     'ADD_LIN_RULE',
                     'ADD_NONLIN_RULE'}:
            mut_types[name] = MutType(name, MutTypeGroup.OWN)

    if not mutations or 'solving_parameters' in mutations:
        mut_groups.append(MutTypeGroup.PARAMETERS)
        for name in {'SPACER.GLOBAL',
                     'SPACER.P3.SHARE_INVARIANTS',
                     'SPACER.P3.SHARE_LEMMAS',
                     # 'SPACER.PUSH_POB', -- takes a long time
                     'SPACER.USE_LIM_NUM_GEN',
                     'SPACER.RESET_POB_QUEUE',
                     'SPACER.SIMPLIFY_LEMMAS_POST',
                     'SPACER.SIMPLIFY_LEMMAS_PRE',
                     'SPACER.SIMPLIFY_POB',
                     'SPACER.USE_BG_INVS',
                     'SPACER.USE_EUF_GEN',
                     'SPACER.USE_LEMMA_AS_CTI',
                     'XFORM.ARRAY_BLAST_FULL',
                     'XFORM.COALESCE_RULES',
                     'XFORM.ELIM_TERM_ITE',
                     # 'XFORM.FIX_UNBOUND_VARS', -- often causes unknown
                     'XFORM.INLINE_LINEAR_BRANCH',
                     'XFORM.INSTANTIATE_ARRAYS',
                     'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
                     'XFORM.INSTANTIATE_QUANTIFIERS',
                     # 'XFORM.MAGIC', -- often causes unknown
                     # 'XFORM.SCALE', -- often causes unknown
                     'XFORM.QUANTIFY_ARRAYS',
                     'XFORM.TRANSFORM_ARRAYS'}:
            mut_types[name] = MutType(name, MutTypeGroup.PARAMETERS, default_value=False)

        for name in {'SPACER.CTP',
                     'SPACER.ELIM_AUX',
                     'SPACER.EQ_PROP',
                     'SPACER.GG.CONCRETIZE',
                     'SPACER.GG.CONJECTURE',
                     'SPACER.GG.SUBSUME',
                     'SPACER.GROUND_POBS',
                     'SPACER.KEEP_PROXY',
                     'SPACER.MBQI',
                     'SPACER.PROPAGATE',
                     'SPACER.REACH_DNF',
                     'SPACER.USE_ARRAY_EQ_GENERALIZER',
                     'SPACER.USE_DERIVATIONS',
                     'SPACER.USE_INC_CLAUSE',
                     'SPACER.USE_INDUCTIVE_GENERALIZER',
                     'XFORM.COI',
                     'XFORM.COMPRESS_UNBOUND',
                     'XFORM.INLINE_EAGER',
                     'XFORM.INLINE_LINEAR',
                     'XFORM.SLICE',
                     'XFORM.TAIL_SIMPLIFIER_PVE'}:
            mut_types[name] = MutType(name, MutTypeGroup.PARAMETERS, default_value=True)

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

    if not mutations or 'simplifications' in mutations:
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
                        'ADD_INEQ': {Z3_OP_LE, Z3_OP_GE, Z3_OP_LT, Z3_OP_GT},
                        'ADD_LIN_RULE': Z3_OP_UNINTERPRETED,
                        'ADD_NONLIN_RULE': Z3_OP_UNINTERPRETED}

default_simplify_options = {'algebraic_number_evaluator', 'bit2bool',
                            'elim_ite', 'elim_sign_ext', 'flat', 'hi_div0',
                            'ignore_patterns_on_ground_qbody', 'push_to_real'}

array_mutations = {'BLAST_SELECT_STORE', 'EXPAND_SELECT_STORE',
                   'EXPAND_STORE_EQ', 'SORT_STORE', 'XFORM.ARRAY_BLAST_FULL',
                   'XFORM.INSTANTIATE_ARRAYS', 'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
                   'XFORM.QUANTIFY_ARRAYS', 'XFORM.TRANSFORM_ARRAYS'}


def update_mutation_weights():
    global mut_types, mut_stats

    for mut_name in mut_types:
        current_mut_stats = mut_stats.get(mut_name)
        if current_mut_stats is None or mut_name == 'ID':
            continue
        trace_discover_probability = current_mut_stats['new_traces'] / \
                                     current_mut_stats['applications']
        mut_types[mut_name].weight = 0.62 * mut_types[mut_name].weight + \
                                     0.38 * trace_discover_probability


class Mutation(object):

    def __init__(self):
        self.type = mut_types['ID']
        self.number = 0
        self.clause_i = None
        self.kind = None
        self.prev_mutation = None
        self.applied = False
        self.trans_num = None
        self.simplify_changed = True
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
        timeout = False
        changed = True
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
            return timeout, changed

        st_time = time.perf_counter()
        if mut_name == 'ADD_LIN_RULE':
            new_instance.set_chc(self.add_lin_rule(instance))

        elif mut_name == 'ADD_NONLIN_RULE':
            new_instance.set_chc(self.add_nonlin_rule(instance))

        elif mut_name == 'EMPTY_SIMPLIFY':
            new_instance.set_chc(empty_simplify(instance.chc))

        elif mut_name in own_mutations:
            new_instance.set_chc(self.transform(instance))

        else:
            new_instance.set_chc(self.simplify_by_one(instance.chc))

        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            timeout = True

        if not self.simplify_changed or \
                instance.chc.sexpr() == new_instance.chc.sexpr():
            self.simplify_changed = True
            changed = False

        return timeout, changed

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

    def simplify_by_one(self, chc_system: AstVector) -> AstVector:
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq."""
        mut_system = AstVector(ctx=current_ctx)

        mut_name = self.type.name.lower()
        params = [mut_name, True]
        for key in default_simplify_options:
            if key != mut_name:
                params += [key, False]

        ind = range(0, len(chc_system)) if not self.clause_i else {self.clause_i}
        for i in range(len(chc_system)):
            if i in ind:
                cur_clause = AstVector(ctx=current_ctx)
                cur_clause.push(chc_system[i])
                rewritten_clause = empty_simplify(cur_clause)[0]

                clause = simplify(rewritten_clause, *params)

                if rewritten_clause.sexpr() == clause.sexpr():
                    self.simplify_changed = False

                del cur_clause, rewritten_clause
            else:
                clause = chc_system[i]
            mut_system.push(clause)

        return mut_system

    def add_lin_rule(self, instance: Instance) -> AstVector:
        mut_system = copy_chc(instance.chc)
        _, clause = self.get_clause_info(instance)
        head, vars = take_pred_from_clause(clause)

        body_files = os.listdir('false_formulas')
        body_files.remove('README.md')
        filename = 'false_formulas/' + random.choice(body_files)
        body = parse_smt2_file(filename, ctx=current_ctx)[0]
        implication = Implies(body, head, ctx=current_ctx)
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
        var = Int('v' + str(0), ctx=current_ctx)
        body_vars.append(var)
        vars = [var]
        and_exprs = []
        for i in range(1, num + 1):
            var = FreshConst(IntSort(ctx=current_ctx), prefix='v')
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
        implication = Implies(body, head_upred, ctx=current_ctx)
        rule = ForAll(head_vars, implication) if head_vars else implication

        mut_system.push(rule)
        group = instance.get_group()
        group.find_family(rule)

        return mut_system

    def get_clause_info(self, instance: Instance) -> (int, AstVector):
        info = instance.info
        chc_system = instance.chc

        if self.trans_num is None and self.clause_i is None:
            ind = np.where(info.clause_expr_num[self.kind] > 0)[0]
            i = int(random.choice(ind))
            expr_num = info.clause_expr_num[self.kind][i]
            self.trans_num = random.randint(0, expr_num - 1) \
                if expr_num > 1 else 0
        else:
            i = self.clause_i

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
        mut_system = AstVector(ctx=current_ctx)

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

    def get_chain(self, format='pp'):
        """Return the full mutation chain."""
        if format == 'pp':
            chain = self.get_name()
        elif format == 'log':
            chain = [self.get_log()]
        elif format == 'list':
            chain = [self.get_name()]
        else:
            assert False, "Unknown output format"
        cur_mutation = self
        for i in range(self.number, 1, -1):
            cur_mutation = cur_mutation.prev_mutation
            if format == 'pp':
                mut_name = cur_mutation.get_name()
                chain = mut_name + '->' + chain
            elif format == 'log':
                cur_log = [cur_mutation.get_log()]
                chain = cur_log + chain
            elif format == 'list':
                mut_name = [cur_mutation.get_name()]
                chain = mut_name + chain
            else:
                assert False, "Unknown output format"
        return chain

    def same_chain_start(self, other) -> bool:
        fst_chain = self.get_chain(format='list')
        snd_chain = other.get_chain(format='list')
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


def empty_simplify(chc_system: AstVector) -> AstVector:
    mut_system = AstVector(ctx=current_ctx)

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
