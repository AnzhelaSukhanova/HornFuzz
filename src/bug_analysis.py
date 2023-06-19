import argparse

from typing import Tuple

import log_analysis
import file_handler

from main import check_satis
import instances
from instances import *

sys.setrecursionlimit(1000)
mutations = {}
message = ''


def is_same_res(instance: Instance, result: bool = False, wrong_model: bool = False) -> bool:
    """
    Return True if solving an instance returns
    the expected result and False otherwise.
    """

    try:
        same_res = result == check_satis(instance, instance.get_group())
        instance.check_model()
        if instance.model_info[0] == unsat:
            same_res = True
        elif wrong_model:
            same_res = False
        instance.model_info = (sat, 0)
    except AssertionError as err:
        same_res = repr(err) == message
    return same_res


def reduce_instance(is_seed: bool, seed: Instance, instance: Instance = None,
                    wrong_model: bool = False) -> bool:
    print('Instance reducing')
    start_instance = deepcopy(instance)
    cur_instance = deepcopy(instance)
    remove_clause_num = 0

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
            mutation.set_remove_mutation(trans_number, i - remove_clause_num)

            try:
                reduced_chc = mutation.transform(cur_instance)
                cur_instance.set_chc(reduced_chc)
            except Exception:
                print(traceback.format_exc())
                cur_instance.set_chc(instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)
                continue

            if is_seed:
                entry = {'id': 0,
                         'filename': seed.get_group().filename,
                         'seed': cur_instance,
                         'mut_chain': mutations,
                         'message': ''}
                bug_is_reproducible = reproducible(entry)
            else:
                is_eq = equivalence_check(seed.chc, cur_instance.chc) \
                    if not wrong_model \
                    else True
                bug_is_reproducible = is_same_res(cur_instance, wrong_model=wrong_model) and is_eq

            if bug_is_reproducible:
                instance.set_chc(cur_instance.chc)
                print('Reduced:', expr_number)
                if expr_number == 0:
                    remove_clause_num += 1
            else:
                cur_instance.set_chc(instance.chc)
                for child in cur_expr.children():
                    expr_queue.append(child)

    is_reduced = True if start_instance.chc.sexpr() != instance.chc.sexpr() else False
    return is_reduced


def reduce_mut_chain(group: InstanceGroup) -> Instance:
    global mutations
    initial_size = len(group.instances)
    chunk_size = initial_size // 2

    while chunk_size:
        print(f'\nChunk size: {chunk_size}.')
        for i in range(initial_size - 1, 0, -chunk_size):
            from_ind = max(i - chunk_size + 1, 1)
            ind_chunk = range(from_ind, i + 1)
            try:
                new_group = undo_mutations(group, ind_chunk)
            except Z3Exception:
                continue
            new_instance = new_group[-1]
            if len(group.instances) != len(new_group.instances) and \
                    is_same_res(new_instance):
                group = new_group
                initial_size -= chunk_size
                print(f'{chunk_size} mutation can be removed.')
                print(group[-1].mutation.get_chain())
        chunk_size //= 2

    instance = group.pop()
    print(instance.mutation.get_chain())
    mutations = instance.mutation.get_chain(format='log')
    return instance


def undo_mutations(group: InstanceGroup, ind: range) -> InstanceGroup:
    """Undo the mutations from a given interval."""
    group_len = len(group.instances)
    new_group = InstanceGroup(len(instance_groups), group.filename)
    new_group.copy_info(group)
    for i in range(ind[0]):
        new_group.push(group[i])

    for i in range(ind[-1] + 1, group_len):
        last_instance = new_group[-1]
        mut_instance = Instance()
        mut_instance.mutation = deepcopy(group[i].mutation)
        mut = mut_instance.mutation
        try:
            mut.apply(last_instance, mut_instance)
        except AssertionError:
            return group
        new_group.push(mut_instance)

    return new_group


def reduce_declarations(instance: Instance):
    def get_pred_name(decl: str):
        name = decl.split(' ', 1)[0].rstrip()
        return name[1:-1] if name[0] == '|' else name

    group = instance.get_group()
    filename = group.filename
    decl_path = instances.output_dir + 'decl/' + filename
    with open(decl_path, 'r') as decl_file:
        declarations = decl_file.read()
    predicates = get_predicates(instance.chc)
    decl_chunks = declarations.split('(declare-fun ')
    i = 0
    for chunk in decl_chunks[1:]:
        i += 1
        pred_decl = get_pred_name(chunk)
        str_predicates = {str(item) for item in predicates}
        if pred_decl not in str_predicates:
            decl_chunks.pop(i)
            i -= 1
    new_declarations = '(declare-fun '.join(decl_chunks)
    return new_declarations


def reduce(filename: str = None, group: InstanceGroup = None,
           reduce_chain: bool = False, reduce_seed: bool = False,
           reduce_mutant: bool = False):

    reduce_dir = instances.output_dir + 'reduced/'
    if not os.path.exists(reduce_dir):
        os.mkdir(reduce_dir)
    for dir in map((lambda x: x + '/'), SEED_DIRS):
        for subdir in os.walk(dir):
            dir_path = reduce_dir + subdir[0]
            if not os.path.exists(dir_path):
                os.mkdir(dir_path)

    mut_instance = group[-1]
    seed = group[0]
    wrong_model = False if mut_instance.satis != seed.satis else True

    if reduce_chain:
        try:
            assert is_same_res(mut_instance)
        except AssertionError:
            print('Bug isn\'t reproduced:', filename)
            print(mutations)
            return None
        mut_instance = reduce_mut_chain(group)

    if reduce_seed or reduce_mutant:
        try:
            cur_instance = seed if reduce_seed else mut_instance
            is_seed = reduce_seed is True
            is_reduced = True
            while is_reduced:
                is_reduced = reduce_instance(is_seed=is_seed,
                                             seed=seed,
                                             instance=cur_instance,
                                             wrong_model=wrong_model)
                declarations = reduce_declarations(cur_instance) \
                    if not is_reduced else None
                cur_instance.dump(reduce_dir,
                                  group.filename,
                                  declarations=declarations,
                                  clear=False)
                print(len(cur_instance.chc))

        except Exception:
            print(traceback.format_exc())


def reproducible(file_info) -> bool:
    global mutations, message

    group, mutations, message = file_handler.restore_group(file_info)
    instance = group[-1]
    if is_same_res(instance):
        instance.dump(instances.output_dir + 'bugs/',
                      group.filename,
                      to_name=instance.id)
        return True
    else:
        print('Bug not found')
        return False


def deduplicate(bug_files=None, logfile: str = 'logfile') -> defaultdict:
    def with_transformations(params: dict, transformation_group: set) -> bool:
        for param in params:
            if param in transformation_group:
                return True
        return False

    if bug_files is None:
        bug_files = []
    bug_groups = defaultdict(set)
    if not bug_files:
        stats = log_analysis.prepare_data(logfile)
        ind = stats.df['status'].isin(['bug', 'wrong_model'])
        for i, entry in stats.df.loc[ind].iterrows():
            if entry['model_state'] != 0:
                bug_files.append(entry)

    for file in bug_files:
        group, mutations, message = file_handler.restore_group(file)
        instance = group[-1]
        if instance is None:
            continue

        params = instance.params
        reproduce = True
        if instance.mutation.number == 1:
            reduce(file, group, reduce_chain=True)
            new_instance = group[-1]
            if new_instance is not None:
                instance = new_instance
            else:
                reproduce = False
        last_mutation = instance.mutation
        if reproduce:
            if 'xform.inline_linear' in params:
                bug_groups['inline_linear'].add(instance)
            elif 'xform.inline_eager' in params:
                bug_groups['inline_eager'].add(instance)
            elif last_mutation.number <= 1 and reproduce:
                bug_groups[last_mutation.type.name.lower()].add(instance)
            elif with_transformations(params, DISABLED_SPACER_CORE_PARAMETERS):
                bug_groups['disable_space_core_transformations'].add(instance)
            elif with_transformations(params, ENABLED_SPACER_CORE_PARAMETERS):
                bug_groups['enable_space_core_transformations'].add(instance)
            elif with_transformations(params, DISABLED_PARAMETERS):
                bug_groups['disable_other_transformations'].add(instance)
            elif with_transformations(params, ENABLED_PARAMETERS):
                bug_groups['enable_other_transformations'].add(instance)
            else:
                bug_groups['other'].add(instance)
                print(mutations)

    return bug_groups


def main():
    global mutations, message

    parser = argparse.ArgumentParser()
    parser.add_argument('bug_file',
                        nargs='?',
                        default=None)
    parser.add_argument('seed_file',
                        nargs='?',
                        default=None)
    parser.add_argument('-logfiles',
                        nargs='*',
                        default=None)
    parser.add_argument('-mut_chain',
                        nargs='?',
                        default=None)
    parser.add_argument('-reduce_chain', action='store_true')
    parser.add_argument('-reduce_seed', action='store_true')
    parser.add_argument('-reduce_mutant', action='store_true')
    parser.add_argument('-reproduce', action='store_true')
    argv = parser.parse_args()
    ctx.set_ctx(Context())
    set_solver('spacer')

    init_mut_types([], ['own', 'simplifications', 'spacer_parameters', 'eldarica_parameters'])
    if not argv.seed_file:
        filenames = file_handler.get_filenames([argv.bug_file]) if argv.bug_file else None
        if argv.reduce_chain or argv.reduce_seed or argv.reduce_mutant:
            for filename in filenames:
                group, mutations, message = file_handler.restore_group(filename)
                reduce(filename, group, argv.reduce_chain, argv.reduce_seed, argv.reduce_mutant)

        elif argv.reproduce:
            if argv.mut_chain:
                entry = {'id': 0,
                         'filename': argv.bug_file,
                         'mut_chain': argv.mut_chain,
                         'message': ''}
                reproducible(entry)
            elif filenames:
                for filename in filenames:
                    reproducible(filename)

        elif argv.logfiles:
            bug_groups = defaultdict()
            for log in argv.logfiles:
                bug_groups[log] = deduplicate(filenames, log)
            for log in bug_groups:
                print(log, len(bug_groups[log]))
                for key in bug_groups[log]:
                    print(key, len(bug_groups[log][key]))
                print()

        else:
            deduplicate(filenames)

    else:
        print(argv.seed_file)
        seed = parse_smt2_file(argv.seed_file,
                               ctx=ctx.current_ctx)
        mutant = parse_smt2_file(argv.bug_file,
                                 ctx=ctx.current_ctx)
        if equivalence_check(seed, mutant):
            print('Equivalent')
        else:
            assert False, 'The mutant is not equivalent to its seed'


if __name__ == '__main__':
    main()
