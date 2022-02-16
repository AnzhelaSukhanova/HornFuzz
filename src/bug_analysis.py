import argparse
import instances

from main import check_satis
from instances import *
from seeds import get_filenames

sys.setrecursionlimit(1000)


def is_same_res(instance: Instance, result: bool = False, message: str = None) -> bool:
    """
    Return True if solving an instance returns
    the expected result and False otherwise.
    """

    try:
        same_res = result == check_satis(instance, get_stats=False)[0]
        if message:
            same_res = False
    except AssertionError as err:
        same_res = repr(err) == message
    return same_res


def reduce_instance(seed: Instance, bug_instance: Instance,
                    message: str = None) -> tuple[Instance, bool]:
    """Reduce the chc-system causing the problem."""

    print('Instance reducing')
    instance = deepcopy(bug_instance)
    is_reduced = False

    for i, clause in enumerate(instance.chc):
        print('Clause:', i)
        expr_queue = [clause]
        trans_number = -1
        expr_number = -1

        while len(expr_queue):
            cur_expr = expr_queue.pop()

            trans_number += 1
            expr_number += 1
            mutation = Mutation()
            mutation.type = mut_types['REMOVE_EXPR']
            mutation.trans_num = trans_number
            mutation.path = [i]
            mutation.kind_ind = -1

            try:
                reduced_chc = mutation.transform(instance)
                instance.set_chc(reduced_chc)
            except Exception as err:
                print(repr(err))
                # print(traceback.format_exc())
                instance.set_chc(bug_instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)
                continue

            is_eq = equivalence_check(seed.chc,
                                      instance.chc)
            if is_same_res(instance, message=message) and is_eq:
                bug_instance.set_chc(instance.chc)
                print('Reduced:', expr_number)
                trans_number -= 1
                is_reduced = True
            else:
                instance.set_chc(bug_instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)
                # print('Cannot be reduced:', trans_number)
    return bug_instance, is_reduced


def reduce_mut_chain(instance: Instance, message: str = None) -> Instance:
    """
    Search for a reduced version of mutation chain that is
    the minimal set of bug-triggering transformations.
    """
    group = instance.get_group()
    group.push(instance)
    initial_size = len(group.instances)
    chunk_size = initial_size // 2

    while chunk_size:
        print('Chunk size:', chunk_size)
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            new_group = undo_mutations(instance, ind_chunk)
            new_instance = new_group[-1]
            if group != new_group and \
                    is_same_res(new_instance, message=message):
                group = new_group

            if chunk_size == 1:
                mut_type = group[ind_chunk[0]].mutation.type
                if mut_type not in type_kind_corr and mut_type != 'ID':
                    group[ind_chunk[0]] = reduce_simplify(group[ind_chunk[0] - 1], mut_type, message)
        chunk_size //= 2

    instance = group.pop()
    print(instance.mutation.get_chain())
    return instance


def undo_mutations(instance: Instance, ind: range) -> InstanceGroup:
    """Undo the mutations from a given interval."""

    group = instance.get_group()
    new_group = deepcopy(group)
    new_group.instances.clear()
    for i in range(ind[0]):
        new_group.push(group[i])

    last_instance = new_group[ind[0] - 1]
    for i in range(ind[-1] + 1, len(group.instances)):
        mut_instance = Instance(last_instance.group_id)
        mut_instance.mutation = group[i].mutation
        mut = mut_instance.mutation
        try:
            mut.apply(last_instance, mut_instance)
        except AssertionError:
            return group
        new_group.push(mut_instance)
        last_instance = mut_instance

    return new_group


def reduce_simplify(instance: Instance, mut_type: str, message: str = None) -> Instance:
    """Reduce the applying of SIMPLIFY"""

    mut_instance = Instance(instance.group_id)
    mut = mut_instance.mutation
    mut.type = mut_type

    mut.path[0] = [i for i in range(len(instance.chc))]
    for i in range(len(instance.chc)):
        mut.path[0].remove(i)
        mut.apply(instance, mut_instance)
        if not is_same_res(mut_instance, message=message):
            mut.path[0].append(i)
        mut_instance.set_chc(instance.chc)
    if mut.path[0] == range(len(instance.chc)):
        mut.path[0] = None

    mut.apply(instance, mut_instance)
    return mut_instance


def reduce(reduce_chain: bool = False):
    filenames = get_filenames('output/bugs')
    for i, filename in enumerate(filenames):
        print(filename)
        mutations, message, seed_name = get_bug_info(filename)
        group = InstanceGroup(i, seed_name)

        if reduce_chain:
            group.restore(i, mutations)
            mut_instance = group[-1]
            assert is_same_res(mut_instance, message=message), \
                'Incorrect mutant-restoration'
            mut_instance = reduce_mut_chain(mut_instance, message)
        else:
            group.restore(i, {})
            mut_system = parse_smt2_file(filename, ctx=current_ctx)
            mut_instance = Instance(i, mut_system)
            for entry in mutations:
                type_name = entry["type"]
                type = mut_types[type_name]
                if type.is_solving_param():
                    mut_instance.add_param(type)

            assert is_same_res(mut_instance, message=message), \
                'Incorrect mutant-restoration'

        reduce_dir = 'output/reduced/'
        if not os.path.exists(reduce_dir):
            os.mkdir(reduce_dir)
        for dir in {'spacer-benchmarks/', 'chc-comp21-benchmarks/',
                    'sv-benchmarks-clauses/'}:
            for subdir in os.walk(dir):
                dir_path = reduce_dir + subdir[0]
                if not os.path.exists(dir_path):
                    os.mkdir(dir_path)
        try:
            is_reduced = True
            while is_reduced:
                mut_instance, is_reduced = \
                    reduce_instance(group[0], mut_instance, message)
                mut_instance.dump('output/reduced', seed_name, clear=False)

        except Exception:
            print(traceback.format_exc())


def get_bug_info(filename: str):
    with open(filename) as file:
        mut_line = file.readline()[2:]
        message = file.readline()
        message = message[2:] if message[0] == ';' else None

    mutations = json.loads(mut_line) \
        if mut_line[2] == '[' \
        else mut_line.split('->')
    seed_chunks = filename.split('_')
    if len(seed_chunks) > 1:
        filename = '/'.join(filename.split('/')[2:])
        seed_name = '_'.join(filename.split('_')[:-1]) + '.smt2'
    else:
        seed_name = filename

    return mutations, message, seed_name


def redo_mutations(filename: str):
    """Reproduce the bug."""
    mutations, message, seed_name = get_bug_info(filename)
    id = 0
    group = InstanceGroup(id, seed_name)
    group.restore(id, mutations)
    instance = group.pop()
    if is_same_res(instance, message=message):
        instance.dump('output/bugs',
                      group.filename,
                      0,
                      to_name=instance.id)
    else:
        assert False, 'Bug not found'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('bug_file',
                        nargs='?',
                        default=None)
    parser.add_argument('seed_file',
                        nargs='?',
                        default=None)
    parser.add_argument('-reduce_chain', action='store_true')
    parser.add_argument('-reproduce', action='store_true')
    argv = parser.parse_args()
    instances.set_ctx(Context())

    init_mut_types([])
    if not argv.seed_file:
        if not argv.reproduce:
            reduce(argv.reduce_chain)
        else:
            redo_mutations(argv.bug_file)
    else:
        seed = parse_smt2_file(argv.seed_file, ctx=current_ctx)
        mutant = parse_smt2_file(argv.bug_file, ctx=current_ctx)
        if equivalence_check(seed, mutant):
            print('Equivalent')
        else:
            assert False, 'The mutant is not equivalent to its seed'


if __name__ == '__main__':
    main()
