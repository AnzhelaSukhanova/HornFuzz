import json
import os
import instances
from constants import SEED_DIRS


def get_relational(directory: str) -> set:
    """
    Return tests from the /spacer-benchmarks/relational
    that don't return 'unknown' and don't work long.
    """

    files = {
        'point-location-nr.52.smt2',
        'point-location-nr.53.smt2',
        'point-location-nr.50.smt2',
        'inc-loop-1.smt2',
        'point-location-nr.54.smt2',
        'mccarthy-monotone.smt2',
        'mccarthy-equivalent.smt2',
        'point-location-nr.51.smt2',
        'point-location-nr.49.smt2',
        'inc-loop-2.smt2',
        'inc-loop-5.smt2'
    }
    seeds = {directory +
             'spacer-benchmarks/relational/' +
             file for file in files}
    return seeds


def get_filenames(files: list) -> list:
    filenames = []
    for item in files:
        if os.path.isdir(item):
            for root, subdirs, files in os.walk(item):
                for file in files:
                    path = os.path.join(root, file)
                    filenames.append(path)
        else:
            filenames.append(item)
    return filenames


def get_instance_names(dir_path: str) -> set:
    """Return all seed-names from the directory with its subdirectories."""

    seeds = set()
    for root, subdirs, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = os.path.join(root, file)
                seeds.add(path)
    return seeds


def exclude_unknown_seed(seeds: set) -> set:
    file = open('exclude_seed.json', 'r')
    blacklist = json.load(file)
    return seeds.difference(blacklist)


def restore_group(entry, with_mutations: bool = True):
    seed = None
    if isinstance(entry, str):
        mutations, message, seed_name, out_dir = get_mutant_info(entry)
        instances.set_output_dir(out_dir)
    else:
        mutations = entry['mut_chain']
        if isinstance(mutations, str):
            mutations = eval(mutations)
        message = entry['message']
        seed_name = entry['filename']
        seed = entry['seed']
        print(seed_name[:-5] + '_' + str(int(entry['id'])) + '.smt2')
    group_id = len(instances.instance_groups)
    group = instances.InstanceGroup(group_id, seed_name)
    if with_mutations:
        if seed:
            group.push(seed)
        group.restore(mutations)
    return group, mutations, message


def get_mutant_info(filename: str):
    with open(filename) as file:
        mut_line = file.readline()
        mut_line = mut_line[2:] if mut_line[0] == ';' else None
        message = file.readline()
        message = message[2:] if message[0] == ';' else None

    mutations = []
    is_bug = False
    if mut_line:
        mutations = json.loads(mut_line)
    out_dir = ''
    if not filename.startswith(tuple(SEED_DIRS)):
        chunks = filename.split('/')
        counter = 1
        for i, chunk in enumerate(chunks):
            if chunk == 'bugs':
                is_bug = True
            if chunks[i + 1] not in SEED_DIRS:
                counter += 1
                out_dir += chunk + '/'
            else:
                break
        filename = '/'.join(chunks[counter:])
        seed_name = '_'.join(filename.split('_')[:-1]) + '.smt2'\
            if is_bug else filename
    else:
        seed_name = filename

    return mutations, message, seed_name, out_dir


def get_last_file(path):
    files = os.listdir(path)
    paths = [os.path.join(path, basename) for basename in files]
    return max(paths, key=os.path.getctime)


def get_seeds(argv, directory: str, restore: bool) -> set:
    mutant_path = instances.output_dir + '/last_mutants'
    mutant_num = 0
    if restore:
        for root, dirs, files in os.walk(mutant_path):
            mutant_num += len(files)

    if mutant_num:
        seeds = get_filenames([mutant_path])
    elif len(argv) == 0:
        seeds = get_relational(directory)
    elif argv[0] == 'all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_instance_names(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds.update(get_instance_names(dir_path))
        dir_path = directory + 'sv-benchmarks-clauses/'
        seeds.update(get_instance_names(dir_path))
        seeds = exclude_unknown_seed(seeds)
    else:
        if argv[0].endswith('.smt2'):
            seeds = set(argv)
        else:
            dir_path = directory + argv[0] + '/'
            seeds = get_instance_names(dir_path)
            seeds = exclude_unknown_seed(seeds)
    return seeds


def create_output_dirs():
    """Create directories for storing instances"""

    if not os.path.exists('output'):
        os.mkdir('output')
    for dir in {'output/last_mutants', 'output/decl',
                'output/bugs', 'output/unknown', 'output/mutants'}:
        if not os.path.exists(dir):
            os.mkdir(dir)
        if dir != 'output':
            for benchmark_dir in {'spacer-benchmarks/',
                                  'chc-comp21-benchmarks/',
                                  'sv-benchmarks-clauses/'}:
                for subdir in os.walk(benchmark_dir):
                    dir_path = dir + '/' + subdir[0]
                    if not os.path.exists(dir_path):
                        os.mkdir(dir_path)

