import math
import time
import json
import re
import traceback
from utils import *

MUT_APPLY_TIME_LIMIT = 10
SEED_SOLVE_TIME_LIMIT_MS = int(2 * 1e3)
MUT_SOLVE_TIME_LIMIT_MS = int(1e5)
INSTANCE_ID = 0

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
        self.has_array = defaultdict(bool)

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
            self.find_pred_info()
            instance.get_system_info()
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

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self[0]
        self.instances = {0: seed}
        if not seed.chc:
            seed.restore(ctx=Context(), is_seed=True)
        self.find_pred_info()
        self.analyze_vars()

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
                self.roll_back()
                return 0
        return stats_limit

    def find_pred_info(self):
        """
        Find whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        if not only_simplify and not with_difficulty_heur:
            return

        assert len(self.instances) > 0, "Instance group is empty"
        instance = self[-1]
        chc_system = instance.chc
        if chc_system is None:
            return
        all_uninter_pred = set()

        for i, clause in enumerate(chc_system):
            expr = clause
            child = clause.children()[0] if clause.children() else None
            while is_quantifier(expr) or is_quantifier(child):
                if is_quantifier(expr) and expr.is_forall():
                    expr = expr.body()
                elif is_not(expr) and child.is_exists():
                    expr = Not(child.body())
                else:
                    break
                child = expr.children()[0] if expr.children() else None

            while is_not(expr) and is_not(child):
                expr = child.children()[0]
                child = expr.children()[0] if expr.children() else None

            if is_implies(expr):
                body = expr.children()[0]
            elif is_or(expr) or (is_not(expr) and is_and(child)):
                body_expr = []
                expr = child if is_not(clause) else clause
                for subexpr in expr.children():
                    if not is_not(subexpr):
                        # it is not necessary to take the negation of
                        # and-subexpressions, since we are counting the
                        # number of predicates
                        body_expr.append(subexpr)
                body = Or(body_expr)
            elif is_not(expr) and is_or(child):
                pass
            elif (is_not(expr) and child.decl().kind() == Z3_OP_UNINTERPRETED) or \
                    expr.decl().kind() == Z3_OP_UNINTERPRETED:
                body = None
            else:
                assert False, self.filename + \
                              ' -- clause-kind: ' + \
                              str(expr)
            if body is not None:
                upred_num, uninter_pred = count_expr(body,
                                                     [Z3_OP_UNINTERPRETED],
                                                     is_unique=True)
                all_uninter_pred.update(uninter_pred[0])
                if upred_num[0] > 1:
                    self.is_linear = False
        self.upred_num = len(all_uninter_pred)

    def analyze_vars(self):
        instance = self[-1]
        for i, clause in enumerate(instance.chc):
            for var in get_bound_vars(clause):
                if is_array(var):
                    self.has_array[i] = True

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
            except AssertionError as err:
                message = traceback.format_exc()
                print(message)


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
        self.info = ClauseInfo(0)

        group = self.get_group()
        if not group.instances:
            self.mutation = Mutation()
        else:
            prev_instance = group[-1]
            self.mutation = Mutation(prev_instance.mutation)
            self.info = deepcopy(prev_instance.info)

    def set_chc(self, chc: AstVector):
        """Set the chc-system of the instance."""
        assert chc is not None, 'CHC-system wasn\'t given'

        self.chc = chc
        group = self.get_group()
        group.same_stats_limit = 5 * len(self.chc)

        if not group.instances:
            chc_len = len(self.chc)
            self.info = ClauseInfo(chc_len)

    def process_seed_info(self, info: dict):
        self.satis = CheckSatResult(info['satis'])
        _trace_states = [State.load(state_date) for state_date in info['trace_states']]
        self.trace_stats.load_states(_trace_states)
        return info['time']
            
    def reset_chc(self):
        self.chc = None
        
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
        self.satis = solver.check()

        if get_stats:
            self.trace_stats.read_from_trace(is_seed)
            self.update_traces_info()
        assert self.satis != unknown, solver.reason_unknown()

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

    def get_system_info(self):
        """
        Get information about the existence of subexpressions of kind
        from info_kinds and about their .
        """
        if self.chc is None or only_simplify:
            return

        info = self.info
        info.expr_exists = expr_exists(self.chc, info_kinds)

        shape = info.is_expr_in_clause.shape
        if shape[1] != len(self.chc):
            exp_shape = (len(info_kinds), len(self.chc))
            info.is_expr_in_clause.resize(exp_shape)

        for i, clause in enumerate(self.chc):
            is_there_expr = expr_exists(clause, info_kinds)
            for j in range(len(info_kinds)):
                info.is_expr_in_clause[j, i] = is_there_expr[j]

    def restore(self, ctx: Context, is_seed: bool = False):
        """Restore the instance from output/last_mutants/."""
        group = self.get_group()
        filename = group.filename if is_seed else \
            'output/last_mutants/' + group.filename
        self.set_chc(z3.parse_smt2_file(filename, ctx=ctx))
        assert len(self.chc) > 0, "Empty chc-system"
        self.get_system_info()

    def dump(self, dir: str, filename: str, start_ind=0,
             message: str = None, to_name=None, clear: bool = True):
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
            group = self.get_group()
            length = len(group.instances)
            for i in range(length - 1, start_ind - 1, -1):
                group[i].reset_chc()
            if self.chc:
                self.reset_chc()

    def update_mutation_stats(self, new_application: bool = False, new_trace_found: bool = False):
        global mut_stats

        mutation_type = self.mutation and self.mutation.type
        if mutation_type is None:
            return
        current_mutation_stats = \
            mut_stats.setdefault(mutation_type,
                                 {'applications': 0.0, 'new_traces': 0.0})
        current_mutation_stats['applications'] += int(new_application)
        current_mutation_stats['new_traces'] += int(new_trace_found)


mut_types = {'ID': 0.0}
mut_stats = {}
with_weights = True
only_simplify = False


def init_mut_types(options: list):
    global mut_types, with_weights, only_simplify

    if 'without_mutation_weights' in options:
        with_weights = False
    if 'only_simplify' in options:
        only_simplify = True

    if not only_simplify:
        """
        And(a, b) -> And(b, a)"""
        mut_types['SWAP_AND'] = 0.0512
        """
        And(a, b) -> And(a, b, a)"""
        mut_types['DUP_AND'] = 0.0636
        """
        And(a, b, c) -> And(a, And(b, c))
        And(a, b) -> And(a, And(a, b))"""
        mut_types['BREAK_AND'] = 0.0612

        mut_types['SWAP_OR'] = 0.0536
        mut_types['MIX_BOUND_VARS'] = 0.059
        mut_types['ADD_INEQ'] = 0.0602

        mut_types['ADD_LIN_RULE'] = 0.06
        mut_types['ADD_OR_RULE'] = 0.06
        mut_types['ADD_NONLIN_RULE'] = 0.06

    mut_types['EMPTY_SIMPLIFY'] = 0.06
    """
    Rewrite inequalities so that right-hand-side is a constant."""
    mut_types['ARITH_INEQ_LHS'] = 0.0599
    """
    All monomials are moved to the left-hand-side, 
    and the right-hand-side is just a constant."""
    mut_types['ARITH_LHS'] = 0.0537
    """
    Expand a distinct predicate into a quadratic number of disequalities."""
    mut_types['BLAST_DISTINCT'] = 0.057
    """
    Blast (some) Bit-vector equalities into bits."""
    mut_types['BLAST_EQ_VALUE'] = 0.0554
    """
    Eagerly replace all (select (store ..) ..) term 
    by an if-then-else term."""
    mut_types['BLAST_SELECT_STORE'] = 0.0556
    """
    Attempt to partially propagate extraction inwards."""
    mut_types['BV_EXTRACT_PROP'] = 0.0526
    """
    Rewrite ite that can be simplified to identity."""
    mut_types['BV_ITE2ID'] = 0.0517
    """
    Additional bu_(u/s)le simplifications."""
    mut_types['BV_LE_EXTRA'] = 0.0523
    """
    Apply simplifications for bvnot."""
    mut_types['BV_NOT_SIMPL'] = 0.0579
    """
    Sort the arguments of all AC operators."""
    mut_types['BV_SORT_AC'] = 0.0541
    """
    Conjunctions are rewritten using negation and disjunctions."""
    mut_types['ELIM_AND'] = 0.0557
    """
    Replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y)))."""
    mut_types['ELIM_REM'] = 0.0611
    """
    Eliminate to_real from arithmetic predicates 
    that contain only integers."""
    mut_types['ELIM_TO_REAL'] = 0.0542
    """
    Expand equalities into two inequalities."""
    mut_types['EQ2INEQ'] = 0.0624
    """
    Expand (^ t k) into (* t ... t) if  1 < k <= max_degree."""
    mut_types['EXPAND_POWER'] = 0.0535
    """
    Expand select over ite expressions."""
    mut_types['EXPAND_SELECT_ITE'] = 0.0535
    """
    Conservatively replace a (select (store ...) ...) term 
    by an if-then-else term."""
    mut_types['EXPAND_SELECT_STORE'] = 0.0522
    """
    Reduce (store ...) = (store ...) with a common base into selects."""
    mut_types['EXPAND_STORE_EQ'] = 0.0521
    """
    Replace (tan x) with (/ (sin x) (cos x))."""
    mut_types['EXPAND_TAN'] = 0.058
    """
    Use gcd rounding on integer arithmetic atoms."""
    mut_types['GCD_ROUNDING'] = 0.0577
    """
    Hoist shared summands under ite expressions."""
    mut_types['HOIST_ITE'] = 0.0523
    """
    Hoist multiplication over summation 
    to minimize number of multiplications."""
    mut_types['HOIST_MUL'] = 0.0573
    """
    Extra ite simplifications, these additional simplifications 
    may reduce size locally but increase globally."""
    mut_types['ITE_EXTRA_RULES'] = 0.0507
    """
    Perform local (i.e. cheap) context simplifications."""
    mut_types['LOCAL_CTX'] = 0.0539
    """
    Replace multiplication by a power of two into a concatenation."""
    mut_types['MUL2CONCAT'] = 0.0539
    """
    Collpase (* t ... t) into (^ t k), 
    it is ignored if expand_power is true."""
    mut_types['MUL_TO_POWER'] = 0.0588
    """
    Pull if-then-else terms when cheap."""
    mut_types['PULL_CHEAP_ITE'] = 0.058
    """
    Push if-then-else over arithmetic terms."""
    mut_types['PUSH_ITE_ARITH'] = 0.0609
    """
    Push if-then-else over bit-vector terms."""
    mut_types['PUSH_ITE_BV'] = 0.0582
    """
    Rewrite patterns."""
    mut_types['REWRITE_PATTERNS'] = 0.0578
    """
    Put polynomials in sum-of-monomials form."""
    mut_types['SOM'] = 0.0575
    """
    Sort nested stores when the indices are known to be different."""
    mut_types['SORT_STORE'] = 0.0549
    """
    Sort the arguments of + application."""
    mut_types['SORT_SUMS'] = 0.0604
    """
    Split equalities of the form (= (concat t1 t2) t3)."""
    mut_types['SPLIT_CONCAT_EQ'] = 0.0556

    """
    Simplify/evaluate expressions containing 
    (algebraic) irrational numbers."""
    mut_types['ALGEBRAIC_NUMBER_EVALUATOR'] = 0.0541
    """
    Try to convert bit-vector terms of size 1 
    into Boolean terms."""
    mut_types['BIT2BOOL'] = 0.0521
    """
    Eliminate ite in favor of and/or."""
    mut_types['ELIM_ITE'] = 0.0529
    """
    Expand sign-ext operator using concat and extract."""
    mut_types['ELIM_SIGN_EXT'] = 0.0565
    """
    Create nary applications for and, or, +, *, 
    bvadd, bvmul, bvand, bvor, bvxor."""
    mut_types['FLAT'] = 0.0579
    """
    Use the 'hardware interpretation' for division 
    by zero (for bit-vector terms)."""
    mut_types['HI_DIV0'] = 0.0498
    """
    Ignores patterns on quantifiers that don't mention 
    their bound variables."""
    mut_types['IGNORE_PATTERNS_ON_GROUND_QBODY'] = 0.0542
    """
    Distribute to_real over * and +."""
    mut_types['PUSH_TO_REAL'] = 0.0554


# The values are the indices of the info_kinds elements
type_kind_corr = {'SWAP_AND': 0, 'DUP_AND': 0, 'BREAK_AND': 0,
                  'SWAP_OR': 1, 'MIX_BOUND_VARS': 2,
                  'ADD_INEQ': {3, 4, 5, 6}, 'ADD_LIN_RULE': 7,
                  'ADD_OR_RULE': 7, 'ADD_NONLIN_RULE': 7}

default_simplify_options = {'algebraic_number_evaluator', 'bit2bool',
                            'elim_ite', 'elim_sign_ext', 'flat', 'hi_div0',
                            'ignore_patterns_on_ground_qbody', 'push_to_real'}


def update_mutation_weights():
    global mut_types, mut_stats
    for mut_type in mut_types:
        current_mut_stats = mut_stats.get(mut_type)
        if current_mut_stats is None or mut_type == 'ID':
            continue
        trace_discover_probability = current_mut_stats['new_traces'] / \
                                     current_mut_stats['applications']
        mut_types[mut_type] = 0.62 * mut_types[mut_type] + \
                              0.38 * trace_discover_probability


class Mutation(object):

    def __init__(self, prev_mutation=None):
        self.type = 'ID'
        self.number = prev_mutation.number + 1 if prev_mutation else 0
        self.path = [None]
        self.kind_ind = None
        self.prev_mutation = prev_mutation
        self.applied = False
        self.trans_num = None
        self.simplify_changed = True
        self.exceptions = set()

    def clear(self):
        self.type = 'ID'
        self.path.clear()
        self.number = 0
        self.prev_mutation = None

    def apply(self, instance: Instance, new_instance: Instance):
        """Mutate instances."""
        timeout = False
        is_simplify = False

        self.next_mutation(instance)

        if self.type == 'ID':
            assert False, 'No mutation can be applied'

        assert instance.chc is not None, 'Instance chc is None'

        st_time = time.perf_counter()
        if self.type == 'ADD_LIN_RULE':
            new_instance.set_chc(self.add_lin_rule(instance))

        elif self.type == 'ADD_OR_RULE':
            new_instance.set_chc(self.add_or_rule(instance))

        elif self.type == 'ADD_NONLIN_RULE':
            new_instance.set_chc(self.add_nonlin_rule(instance))

        elif self.type == 'EMPTY_SIMPLIFY':
            is_simplify = True
            new_instance.set_chc(self.empty_simplify(instance.chc))

        elif self.type in type_kind_corr:
            new_instance.set_chc(self.transform(instance))

        else:
            is_simplify = True
            new_instance.set_chc(self.simplify_by_one(instance.chc))

        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            timeout = True

        changed = True
        if not self.simplify_changed or \
                instance.chc.sexpr() == new_instance.chc.sexpr():
            self.simplify_changed = True
            changed = False
        elif is_simplify:
            new_instance.get_system_info()

        return timeout, changed

    def next_mutation(self, instance: Instance):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        mult_kinds = defaultdict(list)
        types_to_choose = set()
        info = instance.info

        if self.type == 'ID' or \
                (self.type in type_kind_corr and self.kind_ind is None):
            if not only_simplify:
                for i in range(len(info_kinds)):
                    if info.expr_exists[i]:
                        if i == type_kind_corr['SWAP_AND']:
                            types_to_choose.update({'SWAP_AND',
                                                    'DUP_AND',
                                                    'BREAK_AND'})
                        elif i == type_kind_corr['SWAP_OR']:
                            types_to_choose.add('SWAP_OR')
                        elif i == type_kind_corr['MIX_BOUND_VARS']:
                            types_to_choose.add('MIX_BOUND_VARS')
                        elif i in type_kind_corr['ADD_INEQ']:
                            if not mult_kinds['ADD_INEQ']:
                                types_to_choose.add('ADD_INEQ')
                            mult_kinds['ADD_INEQ'].append(i)
                        elif i == type_kind_corr['ADD_LIN_RULE']:
                            types_to_choose.add('ADD_LIN_RULE')
                            types_to_choose.add('ADD_OR_RULE')
                            types_to_choose.add('ADD_NONLIN_RULE')
                        else:
                            pass

        if self.type == 'ID':
            for mut in mut_types:
                if mut not in type_kind_corr:
                    types_to_choose.add(mut)
            types_to_choose = list(types_to_choose.difference(self.exceptions)) \
                if self.exceptions else list(types_to_choose)

            if with_weights:
                weights = []
                for name in types_to_choose:
                    weight = mut_types[name]
                    weights.append(weight)
                try:
                    mut_type = random.choices(types_to_choose, weights)[0]
                except IndexError:
                    mut_type = 'ID'

            else:
                try:
                    mut_type = random.choice(types_to_choose)
                except IndexError:
                    mut_type = 'ID'

            self.type = mut_type

        if self.type in type_kind_corr and self.kind_ind is None:
            if self.type == 'ADD_INEQ':
                self.kind_ind = random.choices(mult_kinds[self.type])[0]
            else:
                self.kind_ind = type_kind_corr[self.type]

    def simplify_by_one(self, chc_system: AstVector) -> AstVector:
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq."""
        mut_system = AstVector(ctx=chc_system.ctx)
        params = defaultdict(bool)
        for key in default_simplify_options:
            params[key] = False
        mut_type = self.type.lower()
        params[mut_type] = True

        ind = range(0, len(chc_system)) if not self.path[0] else {self.path[0]}
        for i in range(len(chc_system)):
            if i in ind:
                cur_clause = AstVector(ctx=chc_system.ctx)
                cur_clause.push(chc_system[i])
                rewritten_clause = self.empty_simplify(cur_clause)[0]

                clause = simplify(rewritten_clause, mut_type, params[mut_type],
                                  algebraic_number_evaluator=
                                  params['algebraic_number_evaluator'],
                                  bit2bool=params['bit2bool'],
                                  elim_ite=params['elim_ite'],
                                  elim_sign_ext=params['elim_sign_ext'],
                                  flat=params['flat'],
                                  hi_div0=params['hi_div0'],
                                  ignore_patterns_on_ground_qbody=
                                  params['ignore_patterns_on_ground_qbody'],
                                  push_to_real=params['push_to_real'])

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

    def add_or_rule(self, instance: Instance) -> AstVector:
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
        kind = info_kinds[self.kind_ind]

        if self.trans_num is None:
            ind = np.where(info.is_expr_in_clause[self.kind_ind])[0]
            i = int(random.choice(ind))
            clause = chc_system[i]
            expr_num = count_expr(clause, [kind])[0]
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

        kind = info_kinds[self.kind_ind]
        mut_clause = self.transform_nth(clause,
                                        kind,
                                        [clause_ind])
        assert self.applied, 'Mutation ' + self.type + ' wasn\'t applied'
        for j, clause in enumerate(chc_system):
            if j == clause_ind:
                mut_system.push(mut_clause)
            else:
                mut_system.push(chc_system[j])
        return mut_system

    def transform_nth(self, expr, expr_kind: int, path: list):
        """Transform nth expression of the specific kind in dfs-order."""
        global trans_n
        if not len(expr.children()):
            return expr

        if is_app_of(expr, expr_kind) or check_ast_kind(expr, expr_kind):
            if trans_n == 0:
                children = expr.children()
                if self.type in {'SWAP_AND', 'SWAP_OR'}:
                    children = children[1:] + children[:1]
                elif self.type == 'DUP_AND':
                    child = children[0]
                    children.append(child)
                elif self.type == 'BREAK_AND':
                    children = mut_break(children)
                elif self.type == 'ADD_INEQ':
                    new_ineq = create_add_ineq(children, expr_kind)
                else:
                    pass

                if expr_kind == Z3_OP_AND:
                    mut_expr = And(children)
                elif expr_kind == Z3_OP_OR:
                    mut_expr = Or(children)
                elif expr_kind == Z3_QUANTIFIER_AST:
                    vars = get_bound_vars(expr)
                    shuffle_vars(vars)
                    mut_expr = update_expr(expr, children, vars)
                else:
                    mut_expr = And([expr, new_ineq])
                self.path = path
                self.applied = True
                return mut_expr
            trans_n -= 1

        mut_children = []
        for i, child in enumerate(expr.children()):
            new_path = path + [i]
            if trans_n >= 0:
                mut_children.append(
                    self.transform_nth(child, expr_kind, new_path))
            else:
                mut_children.append(child)
        return update_expr(expr, mut_children)

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
        if self.type == 'ADD_INEQ':
            return self.type + '(' + \
                   str(self.kind_ind) + ', ' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'

        elif self.type in type_kind_corr:
            return self.type + '(' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'

        else:
            return self.type

    def debug_print(self, chc_system: AstVector, mut_system: AstVector):
        print(chc_system[self.path[0]], '\n->\n', mut_system[self.path[0]])

    def get_log(self) -> dict:
        """Create a log entry with information about the mutation."""
        log = {'type': self.type,
               'path': self.path,
               'kind_ind': self.kind_ind,
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
                self.kind_ind = int(mut_info[1])
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
