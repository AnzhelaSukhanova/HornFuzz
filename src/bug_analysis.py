import traceback
import argparse

from main import check_satis
from instances import *
from seeds import get_filenames


def is_same_res(instance: Instance, result=False, message=None) -> bool:
    """
    Return True if solving an instance returns
    the expected result and False otherwise.
    """

    try:
        same_res = result == check_satis(instance, get_stats=False)
        if message:
            same_res = False
    except AssertionError as err:
        same_res = repr(err) == message
    return same_res


def reduce_instance(instance: Instance, mutation: Mutation,
                    message=None) -> Instance:
    """Reduce the chc-system causing the problem."""

    group = instance.get_group()
    new_instance = deepcopy(instance)
    new_instance.mutation = mutation
    last_chc = instance.chc
    reduced_ind = set()
    upred_ind = group.upred_ind

    for pred in upred_ind:
        ind = group.upred_ind[pred].intersection(reduced_ind)
        new_instance.set_chc(remove_clauses(new_instance.chc, ind))

        mut_instance = deepcopy(new_instance)
        mut = new_instance.mutation
        if mut.path[0]:
            for i in ind:
                if mut.path[0] == i:
                    continue
                elif mut.path[0] > i:
                    mut.path[0] -= 1
        new_instance.get_system_info()

        mut.apply(new_instance, mut_instance)

        if not is_same_res(mut_instance):
            new_instance.set_chc(last_chc)
        else:
            last_chc = new_instance.chc
            reduced_ind = reduced_ind.union(group.upred_ind[pred])
    old_len = len(instance.chc)
    new_len = len(new_instance.chc)
    if old_len != new_len:
        print('Reduced:',
              old_len, '->', new_len,
              '(number of clauses)')
        reduced_instance = reduce_instance(new_instance, mutation, message)
        new_instance.set_chc(reduced_instance.chc)
    return new_instance


def reduce_mut_chain(instance: Instance, message=None) -> Instance:
    """
    Search for a reduced version of mutation chain that is
    the minimal set of bug-triggering transformations.
    """
    group = instance.get_group()
    group.push(instance)
    initial_size = len(group.instances)
    chunk_size = initial_size // 2

    while chunk_size:
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            new_group = undo_mutations(instance, ind_chunk)
            new_instance = new_group[-1]
            if group != new_group and \
                    is_same_res(new_instance, message=message):
                group = new_group

            if chunk_size == 1:
                if group[ind_chunk[0]].mutation.type == MutType.SIMPLIFY:
                    group[ind_chunk[0]] = reduce_simplify(group[ind_chunk[0] - 1], message)
        chunk_size //= 2

    instance = group[-1]
    group.pop()
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
        info = last_instance.info
        if mut.trans_num is not None:
            clause_ind = mut.path[0]
            expr_num = info.expr_num[mut.kind_ind][clause_ind]
            if mut.trans_num >= expr_num:
                return group
        mut.apply(last_instance, mut_instance)
        new_group.push(mut_instance)
        last_instance = mut_instance

    return new_group


def reduce_simplify(instance: Instance, message=None) -> Instance:
    """Reduce the applying of SIMPLIFY"""

    mut_instance = Instance(instance.group_id)
    mut = mut_instance.mutation
    mut.type = MutType.SIMPLIFY
    flags_num = len(mut.simp_flags)

    for i in range(flags_num):
        mut.simp_flags[i] = False
        mut.apply(instance, mut_instance)
        if not is_same_res(mut_instance, message=message):
            mut.simp_flags[i] = True
        mut_instance.set_chc(instance.chc)

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


def reduce():
    filenames = get_filenames('output/bugs')
    for i, filename in enumerate(filenames):
        with open(filename) as file:
            mut_line = file.readline()[2:]
            message = file.readline()
            message = message[2:] if message[0] == ';' else None

        mutations = json.loads(mut_line)
        filename = '/'.join(filename.split('/')[2:])
        seed_name = '_'.join(filename.split('_')[:-1]) + '.smt2'
        group = InstanceGroup(i, seed_name)
        group.restore(i, mutations)
        instance = group[-2]
        mut_instance = group[-1]
        assert is_same_res(mut_instance, message=message), \
            'Incorrect mutant-restoration'

        mut_instance = reduce_mut_chain(mut_instance, message)
        try:
            reduced_chc = reduce_instance(instance,
                                          mut_instance.mutation,
                                          message)
            reduced_chc.dump('output/reduced', seed_name, 0)
        except Exception:
            print(traceback.format_exc())

        instance.ctx = Context()


def redo_mutations(filename: str, mutations):
    """Reproduce the bug."""

    id = 0
    group = InstanceGroup(id, filename)
    group.restore(id, mutations)
    instance = group[-1]
    res = check_satis(instance)
    if not res:
        instance.dump('output/bugs',
                      group.filename,
                      0,
                      to_name=instance.id)
    else:
        assert False, 'Bug not found'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('file',
                        nargs='?',
                        default=None,
                        help='file to reproduce the bug')
    parser.add_argument('-mut_chain',
                        nargs='?',
                        default='',
                        help='chain of mutations to be applied '
                             'to the instance from the file')
    argv = parser.parse_args()
    if not argv.file:
        reduce()
    else:
        if not argv.mut_chain:
            assert False, 'The chain of mutations not given'
        mutations = argv.mut_chain.split('->')
        redo_mutations(argv.file, mutations)


if __name__ == '__main__':
    main()
