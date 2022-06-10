import multiprocessing
import faulthandler
import argparse
import os.path

from src.seeds import *

faulthandler.enable()
enable_trace('spacer')
enable_trace('dl_rule_transf')

heuristics = []
heuristic_flags = defaultdict(bool)
mutations = []
options = []

seed_number = 0
queue = []
current_ctx = None
counter = defaultdict(int)
general_stats = TraceStats()

PROBLEMS_LIMIT = 10
MUT_WEIGHT_UPDATE_RUNS = 10000
PROCESS_NUMBER = 4

with_oracles = False


def ensure_current_context_is_deletable():
    global current_ctx

    refs = gc.get_referrers(current_ctx)
    if len(refs) > 1:
        # dot_file = io.StringIO()
        # objgraph.show_backrefs([current_ctx],
        #                        max_depth=7,
        #                        output=dot_file)
        # dot_file.seek(0)
        logging.error(json.dumps({'context_deletion_error': {
            # 'refs': str(refs),
            # 'grapf': dot_file.read()
        }}))
        current_ctx.__del__()


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


def main(files: set):
    global queue, current_ctx

    set_global_vars(with_oracles, seed_number)
    current_ctx = run_seeds(files, queue, seed_number, counter, general_stats)
    src.main.set_ctx(current_ctx)

    logging.info(json.dumps({'seed_number': seed_number,
                             'heuristics': heuristics,
                             'mutations': mutations,
                             'options': options}))

    while queue:
        sort_queue(queue, general_stats, heuristics)
        instance = queue.pop(0)
        proc = multiprocessing.Process(target=fuzz, args=(instance,))
        try:
            print(proc)
            proc.start()
            proc.join()
        except Exception:
            proc.terminate()
            continue


def fuzz(instance: Instance):
    global current_ctx, counter

    runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

    group = instance.get_group()
    try:
        src.instances.set_ctx(None)
        ensure_current_context_is_deletable()
        current_ctx = Context()
        src.instances.set_ctx(current_ctx)

        is_seed = len(group.instances) == 1
        instance.restore(is_seed=is_seed)

        if with_weights:
            if runs_before_weight_update <= 0:
                update_mutation_weights()
                runs_before_weight_update = MUT_WEIGHT_UPDATE_RUNS

        i = 0
        problems_num = 0
        mut_types_exc = set()

        while i < ONE_INST_MUT_LIMIT:
            counter['runs'] += 1
            i += 1
            if with_weights:
                runs_before_weight_update -= 1

            mut_instance = Instance(instance.group_id)
            mut = mut_instance.mutation
            if mut_types_exc:
                mut.exceptions = mut_types_exc
            mut_time = time.perf_counter()
            timeout, changed = mut.apply(instance, mut_instance)
            mut_time = time.perf_counter() - mut_time
            mut_instance.update_mutation_stats(new_application=True)
            mut_instance.dump('output/mutants',
                              group.filename,
                              to_name=mut_instance.id,
                              clear=False)

            if changed:
                mut_types_exc = set()
                try:
                    st_time = time.perf_counter()
                    res = check_satis(general_stats, mut_instance)
                    solve_time = time.perf_counter() - st_time
                except AssertionError as err:
                    analyze_check_exception(counter,
                                            instance,
                                            err,
                                            mut_instance=mut_instance)

                    problems_num += 1
                    if problems_num == PROBLEMS_LIMIT:
                        i = ONE_INST_MUT_LIMIT
                    print_general_info(counter, mut_time)
                    instance = group[0]
                    mut_instance.reset_chc()
                    continue

                trace_changed = (instance.trace_stats.hash !=
                                 mut_instance.trace_stats.hash)
                mut_instance.update_mutation_stats(new_trace_found=trace_changed)

                if not res:
                    handle_bug(counter, instance, mut_instance)
                    problems_num += 1

                elif timeout:
                    counter['timeout'] += 1
                    log_run_info('mutant_timeout',
                                 instance=instance,
                                 mut_instance=mut_instance)
                    problems_num += 1
                    group.roll_back()
                    instance = group[0]

                    mut_instance.reset_chc()

                else:
                    message = mut_instance.check_model()
                    if mut_instance.model_info[0] != sat and message != 'timeout':
                        handle_bug(counter, instance, mut_instance, message)
                        problems_num += 1
                    else:
                        status = 'model_timeout' if message == 'timeout' else 'pass'

                        if with_oracles:
                            found_problem, states = compare_satis(mut_instance)
                        else:
                            found_problem = False
                        group.push(mut_instance)
                        group.check_stats()

                        if found_problem:
                            log_run_info('oracle_bug',
                                         message=str(states),
                                         instance=instance,
                                         mut_instance=mut_instance)
                            counter['conflict'] += 1
                        else:
                            log_run_info(status,
                                         instance=instance,
                                         mut_instance=mut_instance)
                        instance = mut_instance

                print_general_info(counter,
                                   solve_time,
                                   mut_time,
                                   trace_changed)

            else:
                exc_type = instance.mutation.type
                mut_types_exc.add(exc_type)
                log_run_info('without_change',
                             instance=instance,
                             mut_instance=mut_instance)
                print_general_info(counter)

                mut_instance.reset_chc()

            if problems_num == PROBLEMS_LIMIT:
                i = ONE_INST_MUT_LIMIT

        instance.dump('output/last_mutants',
                      group.filename)
        group.reset()
        queue.append(instance)

    except Exception as err:
        message = traceback.format_exc()
        analyze_check_exception(counter,
                                instance,
                                err,
                                message=message)
        print(group.filename)
        print(message)
        print_general_info(counter)


def preprocess() -> set:
    global heuristics, heuristic_flags, mutations, \
        options, seed_number, with_oracles

    parser = argparse.ArgumentParser()
    parser.add_argument('seeds',
                        nargs='*',
                        default='',
                        help='directory with seeds or keyword \'all\'')
    parser.add_argument('-heuristics', '-heur',
                        nargs='*',
                        choices=['transitions', 'states',
                                 'difficulty', 'simplicity'],
                        default=[],
                        help='trace data which will be used to '
                             'select an instance for mutation')
    parser.add_argument('-mutations', '-mut',
                        nargs='*',
                        choices=['simplifications', 'solving_parameters',
                                 'own'],
                        default=[])
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['without_mutation_weights', 'with_oracles'],
                        default=[])
    argv = parser.parse_args()

    logging.basicConfig(format='%(message)s',
                        filename='logfile',
                        filemode='w',
                        level=logging.INFO)

    np.set_printoptions(suppress=True)
    set_option(max_args=int(1e6), max_lines=int(1e6),
               max_depth=int(1e6), max_visited=int(1e6))

    heuristics = argv.heuristics
    for heur in heuristics:
        heuristic_flags[heur] = True
    set_stats_type(heuristic_flags)

    options = argv.options
    with_oracles = 'with_oracles' in options
    mutations = argv.mutations

    directory = os.path.dirname(os.path.dirname(parser.prog))
    if directory:
        directory += '/'
    files = get_seeds(argv.seeds, directory)
    create_output_dirs()
    init_mut_types(options, mutations)

    seed_number = len(files)
    assert seed_number > 0, 'Seeds not found'
    return files


if __name__ == '__main__':
    files = preprocess()
    main(files)
