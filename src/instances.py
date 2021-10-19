import time
import json

from utils import *

MUT_APPLY_TIME_LIMIT = 10
SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
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
        self.uninter_pred = set()
        self.upred_ind = defaultdict(set)

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
            self.get_pred_info()
            instance.get_system_info()

            filename = 'output/ctx/' + self.filename
            with open(self.filename, 'r') as seed_file:
                formula = seed_file.read()
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
        self.same_stats_limit = 5 * len(seed.chc)
        self.get_pred_info()

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
        if instance.trace_stats == prev_instance.trace_stats:
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

    def get_pred_info(self):
        """
        Get whether the chc-system is linear, the number of
        uninterpreted predicates and their set.
        """
        assert len(self.instances) > 0, "Instance group is empty"
        instance = self[-1]
        chc_system = instance.chc

        for i, clause in enumerate(chc_system):
            child = clause.children()[0]
            if is_quantifier(clause):
                body = clause.body()
            elif is_not(clause) and child.is_exists():
                body = child.body()
            else:
                body = clause

            if is_implies(body):
                expr = body.children()[0]
            elif is_and(body):
                expr = body
            elif is_not(body):
                expr = body.children()[0]
            elif is_or(body):
                for child in body.children():
                    if not is_not(child):
                        expr = child
                        break
            elif body.decl().kind() == Z3_OP_UNINTERPRETED:
                expr = None
            else:
                assert False, self.filename + \
                              ' -- clause-kind: ' + \
                              str(body.decl())
            if expr is not None:
                upred_num, uninter_pred = count_expr(expr,
                                                     [Z3_OP_UNINTERPRETED],
                                                     is_unique=True)
                for pred in uninter_pred[0]:
                    self.uninter_pred.add(pred)
                    self.upred_ind[pred].add(i)

                if upred_num[0] > 1:
                    self.is_linear = False
        self.upred_num = len(self.uninter_pred)

    def restore(self, id: int, mutations):
        seed = parse_smt2_file(self.filename)
        instance = Instance(id, seed)
        self.push(instance)

        for mut in mutations:
            mut_instance = Instance(id)
            mut_instance.mutation.restore(mut)
            mut_instance.mutation.apply(instance, mut_instance)
            self.push(mut_instance)
            instance = mut_instance


class Instance(object):

    def __init__(self, group_id, chc=None):
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
        if not group.instances:
            chc_len = len(self.chc)
            self.info = ClauseInfo(chc_len)

    def check(self, solver: Solver, is_seed=False, get_stats=True):
        """Check the satisfiability of the instance."""
        solver.reset()
        if is_seed:
            solver.set('timeout', SEED_CHECK_TIME_LIMIT)
        else:
            solver.set('timeout', MUT_CHECK_TIME_LIMIT)

        solver.add(self.chc)
        self.satis = solver.check()
        assert self.satis != unknown, solver.reason_unknown()
        if get_stats:
            self.trace_stats.read_from_trace()
            unique_traces.add(self.trace_stats.hash)

    def get_group(self):
        """Return the group of the instance."""
        return instance_groups[self.group_id]

    def get_log(self, is_mutant=True) -> dict:
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
        info = self.info
        info.expr_exists = expr_exists(self.chc, info_kinds)

        shape = info.expr_num.shape
        if shape[1] != len(self.chc):
            exp_shape = (len(info_kinds), len(self.chc))
            info.expr_num.resize(exp_shape)

        for i, clause in enumerate(self.chc):
            expr_numbers = count_expr(clause, info_kinds, vars_lim=2)
            for j in range(len(info_kinds)):
                info.expr_num[j, i] = expr_numbers[j]

    def restore(self):
        """Restore the instance from output/last_mutants/."""
        group = self.get_group()
        filename = 'output/last_mutants/' + group.filename
        self.chc.ctx = Context()
        self.chc = z3.parse_smt2_file(filename, ctx=self.chc.ctx)
        assert len(self.chc) > 0, "Empty chc-system"
        self.get_system_info()

    def dump(self, dir: str, filename: str,
             start_ind=1, message=None, to_name=None):
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

        group = self.get_group()
        length = len(group.instances)
        for i in range(length - 1, start_ind - 1, -1):
            group[i].set_chc(AstVector())


class MutType(int, Enum):
    ID = 1

    """
    And(a, b) -> And(b, a)"""
    SWAP_AND = 2
    """
    And(a, b) -> And(a, b, a)"""
    DUP_AND = 3
    """
    And(a, b, c) -> And(a, And(b, c))
    And(a, b) -> And(a, And(a, b))"""
    BREAK_AND = 4
    SWAP_OR = 5

    # Cause "formula is not in Horn fragment"
    DUP_OR = 6
    BREAK_OR = 7
    # _______________________________________

    MIX_BOUND_VARS = 8
    ADD_INEQ = 9

    """
    Rewrite inequalities so that right-hand-side is a constant."""
    ARITH_INEQ_LHS = 10
    """
    All monomials are moved to the left-hand-side, 
    and the right-hand-side is just a constant."""
    ARITH_LHS = 11
    """
    Expand a distinct predicate into a quadratic number of disequalities."""
    BLAST_DISTINCT = 12
    """
    Blast (some) Bit-vector equalities into bits."""
    BLAST_EQ_VALUE = 13
    """
    Eagerly replace all (select (store ..) ..) term 
    by an if-then-else term."""
    BLAST_SELECT_STORE = 14
    """
    Attempt to partially propagate extraction inwards."""
    BV_EXTRACT_PROP = 15
    """
    Rewrite ite that can be simplified to identity."""
    BV_ITE2ID = 16
    """
    Additional bu_(u/s)le simplifications."""
    BV_LE_EXTRA = 17
    """
    Apply simplifications for bvnot."""
    BV_NOT_SIMPL = 18
    """
    Sort the arguments of all AC operators."""
    BV_SORT_AC = 19
    """
    Conjunctions are rewritten using negation and disjunctions."""
    ELIM_AND = 20
    """
    Replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y)))."""
    ELIM_REM = 21
    """
    Eliminate to_real from arithmetic predicates 
    that contain only integers."""
    ELIM_TO_REAL = 22
    """
    Expand equalities into two inequalities."""
    EQ2INEQ = 23
    """
    Replace nested stores by a lambda expression."""
    EXPAND_NESTED_STORES = 24
    """
    Expand (^ t k) into (* t ... t) if  1 < k <= max_degree."""
    EXPAND_POWER = 25
    """
    Expand select over ite expressions."""
    EXPAND_SELECT_ITE = 26
    """
    Conservatively replace a (select (store ...) ...) term 
    by an if-then-else term."""
    EXPAND_SELECT_STORE = 27
    """
    Reduce (store ...) = (store ...) with a common base into selects."""
    EXPAND_STORE_EQ = 28
    """
    Replace (tan x) with (/ (sin x) (cos x))."""
    EXPAND_TAN = 29
    """
    Use gcd rounding on integer arithmetic atoms."""
    GCD_ROUNDING = 30
    """
    Hoist shared summands under ite expressions."""
    HOIST_ITE = 31
    """
    Hoist multiplication over summation 
    to minimize number of multiplications."""
    HOIST_MUL = 32
    """
    Extra ite simplifications, these additional simplifications 
    may reduce size locally but increase globally."""
    ITE_EXTRA_RULES = 33
    """
    Perform local (i.e., cheap) context simplifications."""
    LOCAL_CTX = 34
    """
    Replace multiplication by a power of two into a concatenation."""
    MUL2CONCAT = 35
    """
    Collpase (* t ... t) into (^ t k), 
    it is ignored if expand_power is true."""
    MUL_TO_POWER = 36
    """
    Pull if-then-else terms when cheap."""
    PULL_CHEAP_ITE = 37
    """
    Push if-then-else over arithmetic terms."""
    PUSH_ITE_ARITH = 38
    """
    Push if-then-else over bit-vector terms."""
    PUSH_ITE_BV = 39
    """
    Rewrite patterns."""
    REWRITE_PATTERNS = 40
    """
    Put polynomials in sum-of-monomials form."""
    SOM = 41
    """
    Sort nested stores when the indices are known to be different."""
    SORT_STORE = 42
    """
    Sort the arguments of + application."""
    SORT_SUMS = 43
    """
    Split equalities of the form (= (concat t1 t2) t3)."""
    SPLIT_CONCAT_EQ = 44

    """
    Simplify/evaluate expressions containing 
    (algebraic) irrational numbers."""
    ALGEBRAIC_NUMBER_EVALUATOR = 45
    """
    Try to convert bit-vector terms of size 1 
    into Boolean terms."""
    BIT2BOOL = 46
    """
    Eliminate ite in favor of and/or."""
    ELIM_ITE = 47
    """
    Expand sign-ext operator using concat and extract."""
    ELIM_SIGN_EXT = 48
    """
    Create nary applications for and, or, +, *, 
    bvadd, bvmul, bvand, bvor, bvxor."""
    FLAT = 49
    """
    Use the 'hardware interpretation' for division 
    by zero (for bit-vector terms)."""
    HI_DIV0 = 50
    """
    Ignores patterns on quantifiers that don't mention 
    their bound variables."""
    IGNORE_PATTERNS_ON_GROUND_QBODY = 51
    """
    Distribute to_real over * and +."""
    PUSH_TO_REAL = 52


class Mutation(object):

    def __init__(self, prev_mutation=None):
        self.type = MutType.ID
        self.number = prev_mutation.number + 1 if prev_mutation else 0
        self.path = [None]
        self.kind_ind = 0
        self.prev_mutation = prev_mutation
        self.applied = False

        self.trans_num = None
        self.simp_flags = {0: True, 1: True, 2: True}

    def clear(self):
        self.type = MutType.ID
        self.path.clear()
        self.number = 0
        self.prev_mutation = None

    def apply(self, instance: Instance, new_instance: Instance,
              exceptions=None):
        """Mutate instances."""
        if self.type == MutType.ID:
            self.next_mutation(instance, exceptions)

        if self.type == MutType.ID:
            assert False, 'No mutation can be applied'

        if self.type.value in range(2, 10):
            new_instance.set_chc(self.transform(instance))

        elif self.type.value > 9:
            new_instance.set_chc(self.simplify_by_one(instance.chc))
            new_instance.get_system_info()

        else:
            assert False

        if bool(instance.chc == new_instance.chc):
            exc_type = self.type.value
            if not exceptions:
                exceptions = {exc_type}
            else:
                exceptions.add(exc_type)
            self.type = MutType.ID
            self.apply(instance, new_instance, exceptions)

    def next_mutation(self, instance: Instance, exceptions: set):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        # mut_weights = {2: 0.3256, 3: 0.4086, 4: 0.3443, 5: 0.501,
        #                8: 0.5061, 9: 0.5847}
        type_kind_corr = {2: 0, 3: 0, 4: 0, 5: 1, 8: 2, 9: []}

        mut_types = set(range(11, len(MutType) + 1))
        info = instance.info

        for i in range(len(info_kinds)):
            if info.expr_exists[i]:
                if i == 0:
                    mut_types.update({2, 3, 4})
                elif i == 1:
                    mut_types.add(5)
                elif i == 2:
                    mut_types.add(8)
                else:
                    if not type_kind_corr[9]:
                        mut_types.update({9, 10})
                    type_kind_corr[9].append(i)
        # weights = []
        # for i in mut_types:
        #     weights.append(mut_weights[i])
        #
        # mut_id = random.choices(mut_types, weights)[0]
        mut_types = list(mut_types.difference(exceptions)) if exceptions \
            else list(mut_types)
        try:
            mut_id = random.choice(mut_types)
        except IndexError:
            mut_id = 1
        self.type = MutType(mut_id)
        if mut_id == 9:
            self.kind_ind = random.choices(type_kind_corr[mut_id])[0]
        elif 1 < mut_id < 9:
            self.kind_ind = type_kind_corr[mut_id]

    def simplify_by_one(self, chc_system: AstVector) -> AstVector:
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq."""
        mut_system = AstVector(ctx=chc_system.ctx)
        params = defaultdict(bool)
        for key in {'algebraic_number_evaluator', 'bit2bool',
                    'elim_ite', 'elim_sign_ext', 'flat', 'hi_div0',
                    'ignore_patterns_on_ground_qbody', 'push_to_real'}:
            params[key] = False
        mut_type = self.type.name.lower()
        params[mut_type] = True

        ind = range(0, len(chc_system)) if not self.path[0] else {self.path[0]}
        for i in range(len(chc_system)):
            if i in ind:
                clause = simplify(chc_system[i], mut_type, params[mut_type],
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
            else:
                clause = chc_system[i]
            mut_system.push(clause)
        return mut_system

    def transform(self, instance: Instance) -> AstVector:
        """Transform an expression of the specific kind."""
        global trans_n
        info = instance.info
        chc_system = instance.chc
        mut_system = AstVector(ctx=chc_system.ctx)
        kind = info_kinds[self.kind_ind]

        if not self.trans_num:
            ind = np.where(info.expr_num[self.kind_ind] != 0)[0]
            i = int(random.choice(ind))
            clause = chc_system[i]
            info.expr_num[self.kind_ind][i] = \
                count_expr(clause, [kind], vars_lim=2)[0]
            num = info.expr_num[self.kind_ind][i]
            self.trans_num = random.randint(0, num - 1)
        else:
            i = self.path[0]
            clause = chc_system[i]
        trans_n = deepcopy(self.trans_num)
        self.path = [i]

        mut_clause = self.transform_nth(clause, kind,
                                        [i], time.perf_counter())
        assert self.applied, 'Mutation ' + self.type.name + ' wasn\'t applied'
        for j, clause in enumerate(chc_system):
            if j == i:
                mut_system.push(mut_clause)
            else:
                mut_system.push(chc_system[j])
        return mut_system

    def transform_nth(self, expr, expr_kind: int,
                      path: list, st_time: float):
        """Transform nth expression of the specific kind in dfs-order."""
        global trans_n
        if time.perf_counter() - st_time >= MUT_APPLY_TIME_LIMIT:
            raise TimeoutError('Timeout of applying mutation')
        if not len(expr.children()):
            return expr

        if is_app_of(expr, expr_kind) or check_ast_kind(expr, expr_kind):
            if trans_n == 0:
                children = expr.children()
                if self.type in {MutType.SWAP_AND, MutType.SWAP_OR}:
                    children = children[1:] + children[:1]
                elif self.type in {MutType.DUP_AND, MutType.DUP_OR}:
                    child = children[0]
                    children.append(child)
                elif self.type in {MutType.BREAK_AND, MutType.BREAK_OR}:
                    children = mut_break(children, expr_kind)
                elif self.type == MutType.ADD_INEQ:
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
                    self.transform_nth(child, expr_kind, new_path, st_time))
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
        if self.type.value < 10:
            return self.type.name + '(' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'
        else:
            return self.type.name

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
        if type(mut_entry) == list:
            for field in mut_entry:
                setattr(self, field, mut_entry[field])

        elif type(mut_entry) == str:
            mut_info = mut_entry[:-1].split('(')
            mut_info[1] = mut_info[1].split(', ')
            self.type = MutType[mut_info[0]]

            if self.type.value < 10:
                self.path = [int(mut_info[1][0])]
                self.trans_num = int(mut_info[1][1])
        else:
            assert False, 'Incorrect mutation entry'


def mut_break(children, expr_kind: int):
    """
    Return the children of the expression
    after applying the mutation BREAK_AND/BREAK_OR
    """

    children_part = children[-2:]
    if len(children) == 2:
        mut_children = children[:-1]
    else:
        mut_children = children[:-2]
    if expr_kind == Z3_OP_AND:
        mut_children.append(And(children_part))
    else:
        mut_children.append(Or(children_part))
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
