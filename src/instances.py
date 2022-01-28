import time
import re
from utils import *

MUT_APPLY_TIME_LIMIT = 10
SEED_SOLVE_TIME_LIMIT_MS = int(2 * 1e3)
MUT_SOLVE_TIME_LIMIT_MS = int(1e5)
INSTANCE_ID = 0
ONE_INST_MUT_LIMIT = 1000

trans_n = 0
unique_traces = set()
instance_groups = defaultdict()


class InstanceGroup(object):

    def __init__(self, id: int, filename: str):
        instance_groups[id] = self
        self.filename = filename
        self.instances = defaultdict(Instance)
        self.same_stats = 0
        self.same_stats_limit = 0
        self.is_linear = True
        self.upred_num = 0
        self.has_array = False
        self.start_dump_ind = 0

    def __getitem__(self, index: int):
        index = index % len(self.instances)
        return self.instances[index]

    def __setitem__(self, index: int, instance):
        index = index % len(self.instances)
        self.instances[index] = instance

    def push(self, instance):
        """Add an instance to the group."""
        length = len(self.instances)
        self.instances[length] = instance
        if length == 0:
            self.dump_ctx()

    def dump_ctx(self):
        filename = 'output/ctx/' + self.filename
        with open(self.filename, 'r') as seed_file:
            file = seed_file.read()
            formula = re.sub(r"\(set-info.*\"\)", "",
                             file, flags=re.DOTALL)
            ctx = formula.split('(assert')[0]
            with open(filename, 'w') as ctx_file:
                ctx_file.write(ctx)

    def pop(self):
        """Take an instance from the group."""
        length = len(self.instances)
        return self.instances.pop(length - 1)

    def roll_back(self, ctx: Context):
        """Roll back the group to the seed."""
        seed = self[0]
        self.instances = {0: seed}
        if not seed.chc:
            seed.restore(ctx=ctx, is_seed=True)
        self.start_dump_ind = 0

    def check_stats(self, stats_limit: int) -> int:
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
                self.roll_back(ctx=self[0].chc.ctx)
                return 0
        return stats_limit

    def restore(self, id: int, mutations, ctx: Context):
        seed = parse_smt2_file(self.filename, ctx=ctx)
        instance = Instance(id, seed)
        self.push(instance)

        for mut in mutations:
            mut_instance = Instance(id)
            mut_instance.mutation.restore(mut)
            try:
                mut_instance.mutation.apply(instance, mut_instance)
                self.push(mut_instance)
                instance = mut_instance
            except AssertionError:
                message = traceback.format_exc()
                print(message)

    def reset(self, start_ind: int = None):
        length = len(self.instances)
        if start_ind is None:
            start_ind = self.start_dump_ind
            self.start_dump_ind = length - 1
        for i in range(length - 1, start_ind - 1, -1):
            self[i].reset_chc()


class Instance(object):

    def __init__(self, group_id: int, chc: AstVector = None):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = None
        if chc is not None:
            self.set_chc(chc)
        self.satis = unknown
        self.trace_stats = TraceStats()
        self.sort_key = 0
        self.params = ['validate', True]

        group = self.get_group()
        if not group.instances:
            self.mutation = Mutation()
        else:
            prev_instance = group[-1]
            self.mutation = Mutation(prev_instance.mutation)

    def set_chc(self, chc: AstVector):
        """Set the chc-system of the instance."""
        assert chc is not None, "Empty chc-system"

        self.chc = chc
        group = self.get_group()
        if group.upred_num == 0:
            self.find_pred_info()
            self.analyze_vars()

        chc_len = len(self.chc)
        group.same_stats_limit = 5 * chc_len
        self.info = ClauseInfo(chc_len)

    def process_seed_info(self, info: dict):
        self.satis = CheckSatResult(info['satis'])
        _trace_states = [State.load(state_date) for state_date in info['trace_states']]
        self.trace_stats.load_states(_trace_states)
        return info['time']

    def reset_chc(self):
        self.chc = None

    def analyze_vars(self):
        group = self.get_group()

        if group.has_array:
            return
        for i, clause in enumerate(self.chc):
            vars, _ = get_vars_and_body(clause)
            for var in vars:
                if is_array(var):
                    group.has_array = True
                    return

    def check(self, solver: Solver, is_seed: bool = False,
              get_stats: bool = True):
        """Check the satisfiability of the instance."""
        solver.reset()
        self.trace_stats.reset_trace_offset()
        if is_seed:
            solver.set('timeout', SEED_SOLVE_TIME_LIMIT_MS)
        else:
            solver.set('timeout', MUT_SOLVE_TIME_LIMIT_MS)
        solver.add(self.chc)

        file = open('.model_exception', 'w+')
        file.close()

        self.satis = solver.check()

        file = open('.model_exception', 'r')
        message = ''.join(file.readlines())
        file.close()

        if get_stats:
            self.trace_stats.read_from_trace(is_seed)
            self.update_traces_info()

        if not message:
            assert self.satis != unknown, solver.reason_unknown()
        else:
            message, _ = message.split("model:")
        return message

    def update_traces_info(self):
        unique_traces.add(self.trace_stats.hash)

    def get_group(self):
        """Return the group of the instance."""
        return instance_groups[self.group_id]

    def get_log(self, is_mutant: bool = True) -> dict:
        """Create a log entry with information about the instance."""
        group = self.get_group()
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
        if self.chc is None or not mut_group_flags[1]:
            return

        info = self.info
        info.expr_num = count_expr(self.chc, info_kinds)

        for i, clause in enumerate(self.chc):
            expr_num = count_expr(clause, info_kinds)
            for kind in info_kinds:
                info.clause_expr_num[kind][i] = expr_num[kind]
                
    def find_pred_info(self):
        """
        Find whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        if not mut_group_flags[1] and not with_difficulty_heur:
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

    def restore(self, ctx: Context, is_seed: bool = False):
        """Restore the instance from output/last_mutants/."""
        group = self.get_group()
        filename = group.filename if is_seed else \
            'output/last_mutants/' + group.filename
        self.set_chc(z3.parse_smt2_file(filename, ctx=ctx))
        assert len(self.chc) > 0, "Empty chc-system"

    def dump(self, dir: str, filename: str, message: str = None,
             to_name=None, clear: bool = True):
        """Dump the instance to the specified directory."""
        ctx_path = 'output/ctx/' + filename
        with open(ctx_path, 'r') as ctx_file:
            ctx = ctx_file.read()
        cur_path = dir + '/' + filename
        if to_name:
            cur_path = cur_path[:-5] + '_' + str(to_name) + '.smt2'
        with open(cur_path, 'w') as file:
            mut_info = self.mutation.get_chain(in_log_format=True)
            file.write('; ' + json.dumps(mut_info) + '\n')
            if message:
                file.write('; ' + message + '\n')
            file.write(ctx)
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


class MutType(object):

    def __init__(self, name, group_id, weight=0.1, default_value=None):
        self.name = name
        '''
        0 -- ID
        1 -- custom mutations
        2 -- solving parameters
        3 -- simplifications
        '''
        self.group_id = group_id
        self.weight = weight
        self.default_value = default_value

    def is_solving_param(self):
        return self.group_id == 2

    def is_simplification(self):
        return self.group_id == 3


class MutTypeEncoder(json.JSONEncoder):

    def default(self, obj):
        if isinstance(obj, MutType):
            return obj.__dict__
        return json.JSONEncoder.default(self, obj)


mut_types = {'ID': MutType('ID', 0)}
mut_stats = {}
with_weights = True
mut_group_flags = {0: False, 1: False, 2: False, 3: False}


def init_mut_types(options: list = None, mutations: list = None):
    global mut_types, with_weights, mut_group_flags

    if 'without_mutation_weights' in options:
        with_weights = False

    if not mutations or 'custom' in mutations:
        mut_group_flags[1] = True
    if not mutations or 'solving_parameters' in mutations:
        mut_group_flags[2] = True
    if not mutations or 'simplifications' in mutations:
        mut_group_flags[3] = True

    if mut_group_flags[1]:
        for name in {'SWAP_AND',
                     'DUP_AND',
                     'BREAK_AND',
                     'SWAP_OR',
                     'MIX_BOUND_VARS',
                     'ADD_INEQ',
                     'ADD_LIN_RULE',
                     'ADD_BV_RULE',
                     'ADD_NONLIN_RULE'}:
            mut_types[name] = MutType(name, 1)

    if mut_group_flags[2]:
        for name in {'XFORM.ARRAY_BLAST',
                     'XFORM.ARRAY_BLAST_FULL',
                     'XFORM.COALESCE_RULES',
                     'XFORM.ELIM_TERM_ITE',
                     'XFORM.FIX_UNBOUND_VARS',
                     'XFORM.INLINE_LINEAR_BRANCH',
                     'XFORM.INSTANTIATE_ARRAYS',
                     'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
                     'XFORM.INSTANTIATE_QUANTIFIERS',
                     'XFORM.QUANTIFY_ARRAYS',
                     'XFORM.TRANSFORM_ARRAYS'}:
            mut_types[name] = MutType(name, 2, default_value=False)

        for name in {'XFORM.COI',
                     'XFORM.COMPRESS_UNBOUND',
                     'XFORM.INLINE_EAGER',
                     'XFORM.INLINE_LINEAR',
                     'XFORM.SLICE',
                     'XFORM.TAIL_SIMPLIFIER_PVE'}:
            mut_types[name] = MutType(name, 2, default_value=True)

    if mut_group_flags[3]:
        name = 'EMPTY_SIMPLIFY'
        mut_types[name] = MutType(name, 3)
        """
        Rewrite inequalities so that right-hand-side is a constant."""
        name = 'ARITH_INEQ_LHS'
        mut_types[name] = MutType(name, 3)
        """
        All monomials are moved to the left-hand-side, 
        and the right-hand-side is just a constant."""
        name = 'ARITH_LHS'
        mut_types[name] = MutType(name, 3)
        """
        Expand a distinct predicate into a quadratic number of disequalities."""
        name = 'BLAST_DISTINCT'
        mut_types[name] = MutType(name, 3)
        """
        Eagerly replace all (select (store ..) ..) term 
        by an if-then-else term."""
        name = 'BLAST_SELECT_STORE'
        mut_types[name] = MutType(name, 3)
        """
        Conjunctions are rewritten using negation and disjunctions."""
        name = 'ELIM_AND'
        mut_types[name] = MutType(name, 3)
        """
        Replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y)))."""
        name = 'ELIM_REM'
        mut_types[name] = MutType(name, 3)
        """
        Eliminate to_real from arithmetic predicates 
        that contain only integers."""
        name = 'ELIM_TO_REAL'
        mut_types[name] = MutType(name, 3)
        """
        Expand equalities into two inequalities."""
        name = 'EQ2INEQ'
        mut_types[name] = MutType(name, 3)
        """
        Expand (^ t k) into (* t ... t) if  1 < k <= max_degree."""
        name = 'EXPAND_POWER'
        mut_types[name] = MutType(name, 3)
        """
        Expand select over ite expressions."""
        name = 'EXPAND_SELECT_ITE'
        mut_types[name] = MutType(name, 3)
        """
        Conservatively replace a (select (store ...) ...) term 
        by an if-then-else term."""
        name = 'EXPAND_SELECT_STORE'
        mut_types[name] = MutType(name, 3)
        """
        Reduce (store ...) = (store ...) with a common base into selects."""
        name = 'EXPAND_STORE_EQ'
        mut_types[name] = MutType(name, 3)
        """
        Replace (tan x) with (/ (sin x) (cos x))."""
        name = 'EXPAND_TAN'
        mut_types[name] = MutType(name, 3)
        """
        Use gcd rounding on integer arithmetic atoms."""
        name = 'GCD_ROUNDING'
        mut_types[name] = MutType(name, 3)
        """
        Hoist shared summands under ite expressions."""
        name = 'HOIST_ITE'
        mut_types[name] = MutType(name, 3)
        """
        Hoist multiplication over summation 
        to minimize number of multiplications."""
        name = 'HOIST_MUL'
        mut_types[name] = MutType(name, 3)
        """
        Extra ite simplifications, these additional simplifications 
        may reduce size locally but increase globally."""
        name = 'ITE_EXTRA_RULES'
        mut_types[name] = MutType(name, 3)
        """
        Perform local (i.e. cheap) context simplifications."""
        name = 'LOCAL_CTX'
        mut_types[name] = MutType(name, 3)
        """
        Replace multiplication by a power of two into a concatenation."""
        name = 'MUL2CONCAT'
        mut_types[name] = MutType(name, 3)
        """
        Collpase (* t ... t) into (^ t k), 
        it is ignored if expand_power is true."""
        name = 'MUL_TO_POWER'
        mut_types[name] = MutType(name, 3)
        """
        Pull if-then-else terms when cheap."""
        name = 'PULL_CHEAP_ITE'
        mut_types[name] = MutType(name, 3)
        """
        Push if-then-else over arithmetic terms."""
        name = 'PUSH_ITE_ARITH'
        mut_types[name] = MutType(name, 3)
        """
        Rewrite patterns."""
        name = 'REWRITE_PATTERNS'
        mut_types[name] = MutType(name, 3)
        """
        Put polynomials in sum-of-monomials form."""
        name = 'SOM'
        mut_types[name] = MutType(name, 3)
        """
        Sort nested stores when the indices are known to be different."""
        name = 'SORT_STORE'
        mut_types[name] = MutType(name, 3)
        """
        Sort the arguments of + application."""
        name = 'SORT_SUMS'
        mut_types[name] = MutType(name, 3)
        """
        Split equalities of the form (= (concat t1 t2) t3)."""
        name = 'SPLIT_CONCAT_EQ'
        mut_types[name] = MutType(name, 3)

        """
        Simplify/evaluate expressions containing 
        (algebraic) irrational numbers."""
        name = 'ALGEBRAIC_NUMBER_EVALUATOR'
        mut_types[name] = MutType(name, 3)
        """
        Eliminate ite in favor of and/or."""
        name = 'ELIM_ITE'
        mut_types[name] = MutType(name, 3)
        """
        Expand sign-ext operator using concat and extract."""
        name = 'ELIM_SIGN_EXT'
        mut_types[name] = MutType(name, 3)
        """
        Create nary applications for and, or, +, *, 
        bvadd, bvmul, bvand, bvor, bvxor."""
        name = 'FLAT'
        mut_types[name] = MutType(name, 3)
        """
        Ignores patterns on quantifiers that don't mention 
        their bound variables."""
        name = 'IGNORE_PATTERNS_ON_GROUND_QBODY'
        mut_types[name] = MutType(name, 3)
        """
        Distribute to_real over * and +."""
        name = 'PUSH_TO_REAL'
        mut_types[name] = MutType(name, 3)


type_kind_corr = {'SWAP_AND': Z3_OP_AND, 'DUP_AND': Z3_OP_AND,
                  'BREAK_AND': Z3_OP_AND, 'SWAP_OR': Z3_OP_OR,
                  'MIX_BOUND_VARS': Z3_QUANTIFIER_AST,
                  'ADD_INEQ': {Z3_OP_LE, Z3_OP_GE, Z3_OP_LT, Z3_OP_GT},
                  'ADD_LIN_RULE': Z3_OP_UNINTERPRETED,
                  'ADD_BV_RULE': Z3_OP_UNINTERPRETED,
                  'ADD_NONLIN_RULE': Z3_OP_UNINTERPRETED}

default_simplify_options = {'algebraic_number_evaluator', 'bit2bool',
                            'elim_ite', 'elim_sign_ext', 'flat', 'hi_div0',
                            'ignore_patterns_on_ground_qbody', 'push_to_real'}


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

    def __init__(self, prev_mutation=None):
        self.type = mut_types['ID']
        self.number = prev_mutation.number + 1 if prev_mutation else 0
        self.path = [None]
        self.kind = None
        self.prev_mutation = prev_mutation
        self.applied = False
        self.trans_num = None
        self.simplify_changed = True
        self.exceptions = set()

    def clear(self):
        self.type = mut_types['ID']
        self.path.clear()
        self.number = 0
        self.prev_mutation = None

    def apply(self, instance: Instance, new_instance: Instance):
        """Mutate instances."""
        timeout = False
        changed = True

        self.next_mutation(instance)
        mut_name = self.type.name

        if mut_name == 'ID':
            assert False, 'No mutation can be applied'

        assert instance.chc is not None, "Empty chc-system"

        if self.type.is_solving_param():
            new_instance.set_chc(instance.chc)
            param = mut_name.lower()
            value = not self.type.default_value
            new_instance.params += [param, value]
            return timeout, changed

        st_time = time.perf_counter()
        if mut_name == 'ADD_LIN_RULE':
            new_instance.set_chc(self.add_lin_rule(instance))

        elif mut_name == 'ADD_BV_RULE':
            new_instance.set_chc(self.add_bv_rule(instance))

        elif mut_name == 'ADD_NONLIN_RULE':
            new_instance.set_chc(self.add_nonlin_rule(instance))

        elif mut_name == 'EMPTY_SIMPLIFY':
            new_instance.set_chc(self.empty_simplify(instance.chc))

        elif mut_name in type_kind_corr:
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

    def next_mutation(self, instance: Instance):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        mult_kinds = defaultdict(list)
        types_to_choose = set()
        info = instance.info
        group = instance.get_group()
        instance.find_system_info()

        mut_name = self.type.name

        if mut_name == 'ID' or \
                (mut_name in type_kind_corr and self.kind is None):
            if mut_group_flags[1]:
                for kind in info_kinds:
                    if info.expr_num[kind] > 0:
                        if kind == type_kind_corr['SWAP_AND']:
                            types_to_choose.update({'SWAP_AND',
                                                    'DUP_AND',
                                                    'BREAK_AND'})
                        elif kind == type_kind_corr['SWAP_OR']:
                            types_to_choose.add('SWAP_OR')
                        elif kind == type_kind_corr['MIX_BOUND_VARS']:
                            types_to_choose.add('MIX_BOUND_VARS')
                        elif kind in type_kind_corr['ADD_INEQ']:
                            if not mult_kinds['ADD_INEQ']:
                                types_to_choose.add('ADD_INEQ')
                            mult_kinds['ADD_INEQ'].append(kind)
                        elif kind == type_kind_corr['ADD_LIN_RULE']:
                            types_to_choose.add('ADD_LIN_RULE')
                            types_to_choose.add('ADD_BV_RULE')
                            types_to_choose.add('ADD_NONLIN_RULE')
                        else:
                            pass

        if mut_name == 'ID':
            for mut_name in mut_types:
                group_id = mut_types[mut_name].group_id
                if not mut_group_flags[group_id]:
                    continue
                elif mut_name in {'BLAST_SELECT_STORE',
                                  'EXPAND_SELECT_STORE',
                                  'EXPAND_STORE_EQ',
                                  'SORT_STORE',
                                  'XFORM.ARRAY_BLAST',
                                  'XFORM.ARRAY_BLAST_FULL',
                                  'XFORM.INSTANTIATE_ARRAYS',
                                  'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
                                  'XFORM.QUANTIFY_ARRAYS',
                                  'XFORM.TRANSFORM_ARRAYS'} and \
                        not group.has_array:
                    continue
                elif mut_name not in type_kind_corr:
                    types_to_choose.add(mut_name)
                else:
                    pass
            types_to_choose = list(types_to_choose.difference(self.exceptions)) \
                if self.exceptions else list(types_to_choose)

            if with_weights:
                reverse_weights = random.choice([True, False]) \
                    if self.number > 0.9 * ONE_INST_MUT_LIMIT \
                    else False
                weights = []
                for name in types_to_choose:
                    weight = mut_types[name].weight
                    if reverse_weights:
                        weight = 1 - weight
                    weights.append(weight)
                try:
                    mut_name = random.choices(types_to_choose, weights)[0]

                except IndexError:
                    mut_name = 'ID'

            else:
                try:
                    mut_name = random.choice(types_to_choose)
                except IndexError:
                    mut_name = 'ID'

            self.type = mut_types[mut_name]

        if mut_name in type_kind_corr and self.kind is None:
            if mut_name == 'ADD_INEQ':
                self.kind = random.choices(mult_kinds[mut_name])[0]
            else:
                self.kind = type_kind_corr[mut_name]

    def simplify_by_one(self, chc_system: AstVector) -> AstVector:
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq."""
        mut_system = AstVector(ctx=chc_system.ctx)

        mut_name = self.type.name.lower()
        params = [mut_name, True]
        for key in default_simplify_options:
            if key != mut_name:
                params += [key, False]

        ind = range(0, len(chc_system)) if not self.path[0] else {self.path[0]}
        for i in range(len(chc_system)):
            if i in ind:
                cur_clause = AstVector(ctx=chc_system.ctx)
                cur_clause.push(chc_system[i])
                rewritten_clause = self.empty_simplify(cur_clause)[0]

                clause = simplify(rewritten_clause, *params)

                if rewritten_clause.sexpr() == clause.sexpr():
                    self.simplify_changed = False

                del cur_clause, rewritten_clause
            else:
                clause = chc_system[i]
            mut_system.push(clause)

        return mut_system

    def empty_simplify(self, chc_system: AstVector) -> AstVector:
        mut_system = AstVector(ctx=chc_system.ctx)

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
        mut_system = deepcopy(instance.chc)
        _, clause = self.get_clause_info(instance)
        head, vars = take_pred_from_clause(clause)

        body_files = os.listdir('false_formulas')
        filename = 'false_formulas/' + random.choice(body_files)
        ctx = instance.chc.ctx
        body = parse_smt2_file(filename, ctx=ctx)[0]
        implication = Implies(body, head, ctx=ctx)
        rule = ForAll(vars, implication) if vars else implication
        mut_system.push(rule)
        return mut_system

    def add_bv_rule(self, instance: Instance) -> AstVector:
        mut_system = deepcopy(instance.chc)
        _, clause = self.get_clause_info(instance)
        head, head_vars = take_pred_from_clause(clause)
        body_upred, body_vars = take_pred_from_clause(clause)
        ctx = instance.chc.ctx

        bv_size = math.floor(math.log2(len(body_vars) + 1))
        bv_size = max(bv_size, 1)
        bv = FreshConst(BitVecSort(bv_size, ctx=ctx), prefix='bv')
        body_vars.append(bv)
        body = body_upred
        for i, var in enumerate(body_vars):
            body = Not(body, ctx=ctx)
            expr = Not(bv + i >= 0, ctx=ctx)
            body = Not(Or(body, expr), ctx=ctx)
            if len(body_vars) == 1:
                expr = Not(bv + 1 >= 0, ctx=ctx)
                body = Not(Or(body, expr), ctx=ctx)
            body = Not(ForAll([var], Not(body, ctx=ctx)), ctx=ctx)

        implication = Implies(body, head, ctx=ctx)
        rule = ForAll(head_vars, implication) if head_vars else implication
        mut_system.push(rule)
        return mut_system

    def add_nonlin_rule(self, instance: Instance) -> AstVector:
        mut_system = deepcopy(instance.chc)
        _, clause = self.get_clause_info(instance)
        head_upred, head_vars, upred = take_pred_from_clause(clause, with_term=True)
        ctx = instance.chc.ctx

        body_vars = head_vars
        pred_vars_num = len(body_vars)
        num = random.randint(1, 10)
        var = Int('v' + str(0), ctx=ctx)
        body_vars.append(var)
        vars = [var]
        and_exprs = []
        for i in range(1, num + 1):
            var = FreshConst(IntSort(ctx=ctx), prefix='v')
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
        implication = Implies(body, head_upred, ctx=ctx)
        rule = ForAll(head_vars, implication) if head_vars else implication

        mut_system.push(rule)
        return mut_system

    def get_clause_info(self, instance: Instance) -> (int, AstVector):
        info = instance.info
        chc_system = instance.chc

        if self.trans_num is None and self.path[0] is None:
            ind = np.where(info.clause_expr_num[self.kind] > 0)[0]
            i = int(random.choice(ind))
            expr_num = info.clause_expr_num[self.kind][i]
            self.trans_num = random.randint(0, expr_num - 1) \
                if expr_num > 1 else 0
        else:
            i = self.path[0]

        clause = chc_system[i]
        self.path = [i]
        return i, clause

    def transform(self, instance: Instance) -> AstVector:
        """Transform an expression of the specific kind."""
        global trans_n
        chc_system = instance.chc
        mut_system = AstVector(ctx=chc_system.ctx)

        clause_ind, clause = self.get_clause_info(instance)
        trans_n = deepcopy(self.trans_num)

        mut_clause = self.transform_nth(clause, [clause_ind])
        assert self.applied, 'Mutation ' + \
                             self.type.name + \
                             ' wasn\'t applied'

        for j, clause in enumerate(chc_system):
            if j == clause_ind:
                mut_system.push(mut_clause)
            else:
                mut_system.push(chc_system[j])
        return mut_system

    def transform_nth(self, expr, path: list):
        """Transform nth expression of the specific kind in dfs-order."""
        global trans_n

        expr_kind = self.kind
        if not len(expr.children()) and self.type.name != 'REMOVE_EXPR':
            return expr

        if expr_kind is None or \
                is_app_of(expr, expr_kind) or \
                check_ast_kind(expr, expr_kind):
            if trans_n == 0:
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
                    mut_expr = update_expr(expr, children, vars)
                else:
                    pass
                self.path = path
                self.applied = True
                return mut_expr
            trans_n -= 1

        mut_children = []
        for i, child in enumerate(expr.children()):
            new_path = path + [i]
            if trans_n >= 0:
                mut_child = self.transform_nth(child, new_path)
                if mut_child is not None:
                    mut_children.append(mut_child)
            else:
                mut_children.append(child)
        if mut_children:
            return update_expr(expr, mut_children)
        else:
            return expr

    def get_chain(self, in_log_format=False):
        """Return the full mutation chain."""
        if not in_log_format:
            chain = self.get_name()
        else:
            chain = [self.get_log()]
        cur_mutation = self
        for i in range(self.number, 1, -1):
            cur_mutation = cur_mutation.prev_mutation
            if not in_log_format:
                mut_name = cur_mutation.get_name()
                chain = mut_name + '->' + chain
            else:
                cur_log = [cur_mutation.get_log()]
                chain = cur_log + chain
        return chain

    def get_name(self):
        """Get mutation name with some information about it."""
        mut_name = self.type.name

        if mut_name == 'ADD_INEQ':
            return mut_name + '(' + \
                   str(self.kind) + ', ' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'

        elif mut_name in type_kind_corr:
            return mut_name + '(' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'

        else:
            return mut_name

    def debug_print(self, chc_system: AstVector, mut_system: AstVector):
        print(chc_system[self.path[0]], '\n->\n', mut_system[self.path[0]])

    def get_log(self) -> dict:
        """Create a log entry with information about the mutation."""
        log = {'type': self.type.name,
               'path': self.path,
               'kind': self.kind,
               'trans_num': self.trans_num,
               }
        return log

    def restore(self, mut_entry):
        """Restore mutations by log or chain."""
        if type(mut_entry) == dict:
            for field in mut_entry:
                setattr(self, field, mut_entry[field])

        elif type(mut_entry) == str and mut_entry != 'nan':
            mut_info = re.findall(r"[\w]+|[0-9]+", mut_entry)
            self.type = mut_info[0]

            if self.type == 'ADD_INEQ':
                self.kind = int(mut_info[1])
                self.path = [int(mut_info[2])]
                self.trans_num = int(mut_info[3])
            elif self.type in type_kind_corr:
                self.path = [int(mut_info[1])]
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
