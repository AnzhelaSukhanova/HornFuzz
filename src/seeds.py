import json
import itertools
from os import walk
from os.path import join
from typing import Optional

import src.main
from src.main import *

current_ctx = None


def mk_seed_instance(counter: dict, idx: int, seed_file_name: str, parse: bool = False) -> \
        Optional[Instance]:
    group = InstanceGroup(idx, seed_file_name)
    instance = Instance(idx)
    try:
        if parse:
            parse_ctx = Context()
            seed = parse_smt2_file(seed_file_name, ctx=parse_ctx)
            seed = seed.translate(current_ctx)
            if not seed:
                return None
            instance.set_chc(seed)
        else:
            instance.reset_chc()

        group.push(instance)
        return instance
    except Exception as err:
        message = traceback.format_exc()
        analyze_check_exception(counter,
                                instance,
                                err,
                                message=message,
                                is_seed=True)
        print(message)
        print_general_info(counter)
        return None


def known_seeds_processor(counter: dict, general_stats: TraceStats,
                          files: set, base_idx: int, seed_info_index):
    def process_seed(i, seed, seed_info, general_stats):
        if 'error' in seed_info:
            return None
        instance = mk_seed_instance(counter, i, seed)
        if instance is None:
            return None
        counter['runs'] += 1
        solve_time = instance.process_seed_info(seed_info)
        instance.update_traces_info()
        general_stats += instance.trace_stats
        return instance, solve_time

    apply_data = {
        seed: {
            'i': i,
            'seed': seed
        }
        for i, seed in enumerate(files, start=base_idx)
    }
    processed_seeds = map_seeds_ordered(apply_data, seed_info_index, general_stats, process_seed)
    return (it for it in processed_seeds if it is not None)


def new_seeds_processor(counter: dict, files: set, base_idx: int, seed_info_index):
    seed_info = {}
    for i, seed in enumerate(files, start=base_idx):
        instance = mk_seed_instance(i, seed, parse=True)
        if instance is None:
            seed_info[seed] = {'error': 'error at instance creation'}
            continue
        counter['runs'] += 1
        try:
            st_time = time.perf_counter()
            check_satis(instance, is_seed=True)
            message = instance.check_model()
            if instance.model_info[0] != sat:
                handle_bug(counter,
                           instance,
                           message=message)
            solve_time = time.perf_counter() - st_time
            seed_info[seed] = {
                'satis': instance.satis.r,
                'time': solve_time,
                'trace_states': [state.save() for state in getattr(instance.trace_stats, 'states', [])]
            }
            yield instance, solve_time
        except Exception as err:
            analyze_check_exception(counter,
                                    instance,
                                    err,
                                    is_seed=True)
            print_general_info(counter)
            seed_info[seed] = {'error': 'error at seed check'}
        finally:
            if len(seed_info) > 300:
                store_seed_info(seed_info, seed_info_index)
                seed_info = {}
    if seed_info:
        store_seed_info(seed_info, seed_info_index)


def run_seeds(files: set, queue: list, seed_number: int,
              counter: dict, general_stats: TraceStats) -> Context:
    """Read and solve the seeds."""
    global current_ctx

    current_ctx = Context()
    src.main.set_ctx(current_ctx)
    seed_info_index = build_seed_info_index()
    known_seed_files = files & set(seed_info_index.keys())
    other_seed_files = files - known_seed_files
    known_seeds = known_seeds_processor(counter, general_stats, known_seed_files, 0, seed_info_index)
    other_seeds = new_seeds_processor(counter, other_seed_files, len(known_seed_files), seed_info_index)

    for i, (instance, solve_time) in enumerate(itertools.chain(known_seeds, other_seeds)):
        queue.append(instance)
        log_run_info('seed', instance=instance)
        print_general_info(counter, solve_time=solve_time)
    seed_number = len(queue)

    assert seed_number > 0, 'All seeds are unknown or ' \
                            'in the incorrect format'

    return current_ctx


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


def get_problem(directory: str) -> set:
    files = {
        'LIA-Lin/chc-LIA-Lin_214.smt2',
        'LIA-Lin/chc-LIA-Lin_239.smt2',
        'LIA-Lin/chc-LIA-Lin_244.smt2',
        'LIA-Lin/chc-LIA-Lin_258.smt2',
        'LIA-Lin/chc-LIA-Lin_450.smt2',
        'LIA-Lin-Arrays/chc-LIA-Lin-Arrays_117.smt2',
        'LIA-Lin-Arrays/chc-LIA-Lin-Arrays_182.smt2',
        'LIA-NonLin/chc-LIA-NonLin_033.smt2',
        'LIA-NonLin/chc-LIA-NonLin_417.smt2',
        'LIA-NonLin/chc-LIA-NonLin_518.smt2',
        'LIA-NonLin/chc-LIA-NonLin_575.smt2'
    }
    seeds = {directory +
             'chc-comp21-benchmarks/' +
             file for file in files}
    return seeds


def get_filenames(dir_path: str) -> set:
    """Return all seed-names from the directory with its subdirectories."""

    seeds = set()
    for root, subdirs, files in walk(dir_path):
        for file in files:
            if file.endswith('.smt2'):
                path = join(root, file)
                seeds.add(path)
    return seeds


def exclude_unknown_seed(seeds: set) -> set:
    file = open('exclude_seed.json', 'r')
    blacklist = json.load(file)
    return seeds.difference(blacklist)


def get_seeds(argv, directory: str) -> set:
    if len(argv) == 0:
        seeds = get_relational(directory)
    elif argv[0] == 'debug':
        seeds = get_problem(directory)
    elif argv[0] == 'all':
        dir_path = directory + 'spacer-benchmarks/'
        seeds = get_filenames(dir_path)
        dir_path = directory + 'chc-comp21-benchmarks/'
        seeds.update(get_filenames(dir_path))
        dir_path = directory + 'sv-benchmarks-clauses/'
        seeds.update(get_filenames(dir_path))
        seeds = exclude_unknown_seed(seeds)
    else:
        if argv[0].endswith('.smt2'):
            seeds = set(argv)
        else:
            dir_path = directory + argv[0] + '/'
            seeds = get_filenames(dir_path)
            seeds = exclude_unknown_seed(seeds)
    return seeds
