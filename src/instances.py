import time

from utils import *

MUT_APPLY_TIME_LIMIT = 10
SEED_CHECK_TIME_LIMIT = int(2 * 1e3)
MUT_CHECK_TIME_LIMIT = int(1e5)
INSTANCE_ID = 0

trans_n = 0
unique_traces = set()


class InstanceGroup(object):

    def __init__(self, filename):
        self.filename = filename
        self.instances = defaultdict(Instance)
        self.same_stats = 0
        self.same_stats_limit = 0
        self.is_linear = True
        self.upred_num = 0
        self.uninter_pred = set()
        self.upred_ind = defaultdict(set)
        self.is_simplified = False

    def __getitem__(self, index):
        if index < 0:
            index = len(self.instances) + index
        return self.instances[index]

    def __setitem__(self, index, instance):
        if index < 0:
            index = len(self.instances) + index
        self.instances[index] = instance

    def push(self, instance):
        """Add an instance to the group."""
        length = len(self.instances)
        self.instances[length] = instance
        if length == 0:
            self.get_pred_info()
            instance.get_system_info()

    def pop(self):
        length = len(self.instances)
        self.instances.pop(length - 1)

    def roll_back(self):
        """Roll back the group to the seed."""
        seed = self[0]
        self.instances = {0: seed}
        self.is_simplified = False
        self.same_stats_limit = 5 * len(seed.chc)
        self.get_pred_info()

    def check_stats(self, stats_limit):
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

            child = body.children()[0]
            if is_implies(body):
                expr = body.children()[0]
            elif is_and(body):
                expr = body
            elif is_not(body) and is_or(child):
                expr = child
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


instance_group = defaultdict(InstanceGroup)


class Instance(object):

    def __init__(self, group_id, chc=None):
        global INSTANCE_ID
        self.id = INSTANCE_ID
        INSTANCE_ID += 1
        self.group_id = group_id
        self.chc = chc
        self.satis = unknown
        self.trace_stats = TraceStats()
        self.sort_key = 0
        group = self.get_group()

        if not group.instances:
            chc_len = len(self.chc)
            self.mutation = Mutation()
            self.info = ClauseInfo(chc_len)
        else:
            prev_instance = group[-1]
            self.mutation = Mutation(prev_instance.mutation)
            self.info = deepcopy(prev_instance.info)

    def check(self, solver, is_seed=False, get_stats=True):
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
        return instance_group[self.group_id]

    def get_log(self, is_seed=False):
        """Create a log entry with information about the instance."""
        group = self.get_group()
        log = {'filename': group.filename, 'id': self.id}
        if not is_seed:
            log['prev_inst_id'] = group[-1].id
            log['mut_type'] = self.mutation.get_name()
        return log

    def get_system_info(self):
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


class MutType(Enum):
    ID = 1

    """And(a, b) -> And(b, a)"""
    SWAP_AND = 2
    """And(a, b) -> And(a, b, a)"""
    DUP_AND = 3
    """
    And(a, b, c) -> And(a, And(b, c))
    And(a, b) -> And(a, And(a, b))
    """
    BREAK_AND = 4
    SWAP_OR = 5

    # Cause "formula is not in Horn fragment"
    DUP_OR = 6
    BREAK_OR = 7
    # _______________________________________

    MIX_BOUND_VARS = 8
    SIMPLIFY = 9
    ADD_INEQ = 10


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

    def apply(self, instance, new_instance):
        """Mutate instances."""
        if self.type == MutType.ID:
            self.next_mutation(instance)

        if self.type == MutType.ID:
            assert False, 'No mutation can be applied'

        elif self.type in {MutType.SWAP_AND, MutType.SWAP_OR,
                           MutType.DUP_AND, MutType.DUP_OR,
                           MutType.BREAK_AND, MutType.BREAK_OR,
                           MutType.MIX_BOUND_VARS, MutType.ADD_INEQ}:
            new_instance.chc = self.transform(instance)

        elif self.type == MutType.SIMPLIFY:
            new_instance.chc = self.simplify_ineq(instance.chc)
            new_instance.get_system_info()

        else:
            assert False

    def next_mutation(self, instance):
        """
        Return the next mutation based on the instance,
        type of the previous mutation etc.
        """
        ind = ineq_ind = []
        info = instance.info
        for i in range(len(info_kinds)):
            if info.expr_exists[i]:
                if 2 < i < 8:
                    ineq_ind.append(i)
                else:
                    ind.append(i)
        ind.append(random.choice(ineq_ind))

        if not ind:
            self.type = MutType.ID
        else:
            group = instance.get_group()
            self.kind_ind = random.choice(ind)
            if self.kind_ind == 0:
                value = random.randrange(2, 5)
                self.type = MutType(value)
            elif self.kind_ind == 1:
                value = 5  # random.randrange(5, 8)
                self.type = MutType(value)
            elif self.kind_ind == 2:
                self.type = MutType.MIX_BOUND_VARS
            elif self.kind_ind == 7:
                self.type = MutType.SIMPLIFY
                group.is_simplified = True
            else:
                if not group.is_simplified:
                    self.type = MutType.SIMPLIFY
                    group.is_simplified = True
                else:
                    self.type = MutType.ADD_INEQ

    def simplify_ineq(self, chc_system):
        """Simplify instance with arith_ineq_lhs, arith_lhs and eq2ineq"""
        mut_system = AstVector()
        ind = range(0, len(chc_system)) if not self.path[0] else self.path[0]
        for i in ind:
            mut_clause = simplify(chc_system[i],
                                  arith_ineq_lhs=self.simp_flags[0],
                                  arith_lhs=self.simp_flags[1],
                                  eq2ineq=self.simp_flags[2])
            mut_system.push(mut_clause)
        return mut_system

    def transform(self, instance):
        """Transform an expression of the specific kind."""
        global trans_n
        info = instance.info
        chc_system = instance.chc
        mut_system = AstVector()
        kind = info_kinds[self.kind_ind]

        if not self.trans_num:
            ind = np.where(info.expr_num[self.kind_ind] != 0)[0]
            i = int(random.choice(ind))
            num = info.expr_num[self.kind_ind][i]
            self.trans_num = random.randint(0, num - 1)
        else:
            i = self.path[0]
        clause = chc_system[i]
        trans_n = deepcopy(self.trans_num)
        self.path = [i]

        expr_num = info.expr_num[:, i]
        mut_clause = self.transform_nth(clause, kind, expr_num,
                                        [i], time.perf_counter())
        assert self.applied, 'Mutation ' + self.type.name + ' wasn\'t applied'
        for j, clause in enumerate(chc_system):
            if j == i:
                mut_system.push(mut_clause)
            else:
                mut_system.push(chc_system[j])

        assert bool(chc_system != mut_system), \
            'Mutation ' + self.type.name + ' didn\'t change the CHC'
        return mut_system

    def transform_nth(self, expr, expr_kind, expr_num, path, st_time):
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
                    for i, kind in enumerate(info_kinds):
                        if is_app_of(child, kind) or check_ast_kind(child, kind):
                            expr_num[i] += 1
                elif self.type in {MutType.BREAK_AND, MutType.BREAK_OR}:
                    children = mut_break(children, expr_kind)
                    expr_num[self.kind_ind] += 1
                elif self.type == MutType.ADD_INEQ:
                    new_ineq = create_add_ineq(children, expr_kind)
                    if expr_kind in {Z3_OP_LE, Z3_OP_LT}:
                        expr_num[6] += 1
                    else:
                        expr_num[7] += 1
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
                    expr_num[0] += 1
                self.path = path
                self.applied = True
                return mut_expr
            trans_n -= 1

        mut_children = []
        for i, child in enumerate(expr.children()):
            new_path = path + [i]
            if trans_n >= 0:
                mut_children.append(self.transform_nth(child, expr_kind, expr_num,
                                                       new_path, st_time))
            else:
                mut_children.append(child)
        return update_expr(expr, mut_children)

    def get_chain(self):
        """Return the full mutation chain."""
        chain = self.get_name()
        cur_mutation = self
        for i in range(self.number, 1, -1):
            cur_mutation = cur_mutation.prev_mutation
            mut_name = cur_mutation.get_name()
            chain = mut_name + '->' + chain
        return chain

    def get_name(self):
        if self.type in {MutType.SWAP_AND, MutType.SWAP_OR,
                         MutType.DUP_AND, MutType.DUP_OR,
                         MutType.BREAK_AND, MutType.BREAK_OR,
                         MutType.MIX_BOUND_VARS, MutType.ADD_INEQ}:
            return self.type.name + '(' + \
                   str(self.path[0]) + ', ' + \
                   str(self.trans_num) + ')'
        elif self.type == MutType.SIMPLIFY:
            flags = list(map(int, self.simp_flags.values()))
            info = str(flags)
            if self.path[0]:
                info = str(info) + ', ' + str(self.path[0])
            return self.type.name + '(' + info + ')'
        else:
            return self.type.name

    def debug_print(self, chc_system: AstVector, mut_system: AstVector):
        print(chc_system[self.path[0]], '\n->\n', mut_system[self.path[0]])


def mut_break(children, expr_kind):
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


def create_add_ineq(children, expr_kind):
    if expr_kind in {Z3_OP_LE, Z3_OP_LT}:
        new_child = children[1] + 1
        new_ineq = children[0] < new_child
    else:
        new_child = children[1] - 1
        new_ineq = children[0] > new_child
    return new_ineq
