import logging
import objgraph
import gc

import src.instances
import src.oracles
import src.utils
from src.instances import *
from src.seed_info_utils import *

# noinspection PyUnresolvedReferences
import src.z3_api_mods

oracles_names = {'Eldarica'}
seed_number = 0
with_oracles = False


def set_global_vars(oracle_flag: bool, seed_num: int):
    global with_oracles, seed_number

    with_oracles = oracle_flag
    seed_number = seed_num


def calc_sort_key(heuristic: str, stats, weights=None) -> int:
    """Calculate the priority of an instance in the sorted queue."""

    if heuristic == 'transitions':
        prob_matrix = stats.get_probability(StatsType.TRANSITIONS)
        size = stats.matrix.shape[0]
        weight_matrix_part = weights[:size, :size]
        trans_matrix = stats.matrix
        sort_key = np.sum(prob_matrix * trans_matrix * weight_matrix_part)
    elif heuristic == 'states':
        states_prob = stats.get_probability(StatsType.STATES)
        sort_key = sum(states_prob[state] * weights[state]
                       for state in stats.states_num)
    elif heuristic in {'difficulty', 'simplicity'}:
        is_nonlinear = not stats[0]
        upred_num = stats[1]
        sort_key = (is_nonlinear, upred_num)
    else:
        assert False, "Incorrect heuristic"
    return sort_key


def check_satis(general_stats: TraceStats, instance: Instance,
                is_seed: bool = False, get_stats: bool = True):
    solver = SolverFor('HORN',
                       ctx=src.instances.current_ctx)
    solver.set('engine', 'spacer')

    if not is_seed:
        seed = instance.get_group()[0]
        if seed.satis == unknown:
            seed.check(solver, is_seed=True, get_stats=get_stats)
        satis = seed.satis

    for param in instance.params:
        value = instance.params[param]
        solver.set(param, value)

    instance.check(solver, is_seed, get_stats)
    if is_seed:
        satis = instance.satis

    if get_stats:
        general_stats += instance.trace_stats
    return instance.satis == satis


def sort_queue(queue: list, general_stats: TraceStats, heuristics: list):
    """Sort the queue by statistics."""
    length = len(heuristics)
    for i in range(length):
        heur = heuristics[i]
        if heur in {'transitions', 'states'}:
            type = StatsType.TRANSITIONS if heur == 'transitions' \
                else StatsType.STATES
            weights = general_stats.get_weights(type)
        chunk_size = len(queue) // (i + 1)
        queue_chunks = [queue[j:j + chunk_size]
                        for j in range(0, len(queue), chunk_size)]
        queue = []
        for chunk in queue_chunks:
            for instance in chunk:
                if heur == 'transitions' or heur == 'states':
                    ins_stats = instance.trace_stats
                    instance.sort_key = calc_sort_key(heur,
                                                      ins_stats,
                                                      weights)
                else:
                    group = instance.get_group()
                    instance.sort_key = calc_sort_key(heur,
                                                      (group.is_linear,
                                                       group.upred_num))
            to_reverse = False if heur == 'simplicity' else True
            chunk.sort(key=lambda item: item.sort_key, reverse=to_reverse)
            queue += chunk


def update_mutation_weights():
    src.instances.update_mutation_weights()
    logging.info(json.dumps({'update_mutation_weights': src.instances.get_mut_weights_dict()},
                            cls=MutTypeEncoder))


def print_general_info(counter: dict, solve_time: time = None,
                       mut_time: time = None, trace_changed: bool = None):
    """Print and log information about runs."""
    traces_num = len(unique_traces)
    log = {'current_time': time.perf_counter(),
           'runs': counter['runs']}
    if solve_time:
        log['solve_time'] = solve_time
    if mut_time:
        log['mut_time'] = mut_time
    if trace_changed is not None:
        log['trace_changed'] = trace_changed
    if counter['runs']:
        print('Total:', counter['runs'],
              'Bugs:', counter['bug'],
              'Timeout:', counter['timeout'],
              'Unknown:', counter['unknown'],
              'Errors:', counter['error'])
        if with_oracles and counter['runs'] > seed_number:
            print('Solver conflicts:', counter['conflict'])
    log['unique_traces'] = traces_num
    if traces_num:
        print('Unique traces:', traces_num, '\n')
    else:
        print()
    logging.info(json.dumps({'general_info': log}))


def log_run_info(status: str, message: str = None,
                 instance: Instance = None, mut_instance: Instance = None):
    """Create a log entry with information about the run."""

    log = {'current_time': time.perf_counter(),
           'status': status}
    if message:
        log['message'] = message
    if instance:
        if not mut_instance:
            instance_info = instance.get_log(is_mutant=False)
            log.update(instance_info)
            if status == 'error':
                if instance.chc:
                    log['chc'] = instance.chc.sexpr()
                chain = instance.mutation.get_chain()
                log['mut_chain'] = chain
            else:
                log['satis'] = instance.satis.r

        else:
            mutant_info = mut_instance.get_log()
            log.update(mutant_info)
            if status not in {'pass', 'without_change'}:
                chain = mut_instance.mutation.get_chain()
                log['mut_chain'] = chain
                if status in {'bug', 'wrong_model',
                              'mutant_unknown', 'error'}:
                    log['satis'] = mut_instance.satis.r
                    if status == 'wrong_model':
                        log['model_state'] = mut_instance.model_info[0].r
                        log['bug_clause'] = str(mut_instance.model_info[1])

    logging.info(json.dumps({'run_info': log}))


def analyze_check_exception(counter: dict, instance: Instance, err: Exception,
                            message: str = None, mut_instance: Instance = None,
                            is_seed: bool = False):
    """Log information about exceptions that occur during the check."""
    group = instance.get_group()

    if is_seed:
        if str(err) == 'timeout':
            counter['timeout'] += 1
            status = 'seed_timeout'
        elif message:
            counter['error'] += 1
            status = 'error'
        else:
            counter['unknown'] += 1
            status = 'seed_unknown'
            message = repr(err)
        log_run_info(status,
                     message,
                     instance)
    else:
        if not message:
            message = repr(err)
        if str(err) == 'timeout' or isinstance(err, TimeoutError):
            counter['timeout'] += 1
            status = 'mutant_timeout' if mut_instance \
                else 'timeout_before_check'
            log_run_info(status,
                         message,
                         instance,
                         mut_instance)
        else:
            if mut_instance:
                counter['unknown'] += 1
                status = 'mutant_unknown'
            else:
                counter['error'] += 1
                status = 'error'
            log_run_info(status,
                         message,
                         instance,
                         mut_instance)
        if status == 'unknown':
            mut_instance.dump('output/unknown',
                              group.filename,
                              message=message,
                              to_name=mut_instance.id)
        elif status == 'timeout_before_check':
            group[0].dump('output/last_mutants',
                          group.filename)

        if status != 'error':
            group.roll_back()


def handle_bug(counter: dict, instance: Instance,
               mut_instance: Instance = None, message: str = None):
    counter['bug'] += 1
    model_state = mut_instance.model_info[0] \
        if mut_instance \
        else instance.model_info[0]
    status = 'bug' if model_state == sat else 'wrong_model'
    log_run_info(status,
                 message=message,
                 instance=instance,
                 mut_instance=mut_instance)

    group = instance.get_group()
    if mut_instance:
        mut_instance.dump('output/bugs',
                          group.filename,
                          to_name=mut_instance.id)
    else:
        instance.dump('output/bugs',
                      group.filename,
                      to_name=0)
        group.reset()


def compare_satis(instance: Instance, is_seed: bool = False):
    group = instance.get_group()
    states = defaultdict()
    found_problem = False

    if not is_seed:
        instance.dump('output/last_mutants/',
                      group.filename,
                      clear=False)
        filename = 'output/last_mutants/' + group.filename
    else:
        filename = group.filename
    for name in oracles_names:
        state = src.oracles.solve(name, filename)
        states[name] = state
        if state != instance.satis.r and state in {'sat', 'unsat'}:
            found_problem = True
    return found_problem, states
