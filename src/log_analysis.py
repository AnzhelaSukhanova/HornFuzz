import argparse
import json
import math
import os
from constants import *
from files import get_filenames
from collections import defaultdict
from statistics import mean

import matplotlib.pyplot as plt
import pandas as pd

unique_traces = 0
num_dict = defaultdict(list)
count_dict = defaultdict(list)
colors = ['crimson', 'teal', 'darkorange', 'darkblue']
markers = ['d', 's', '^', 'o', '+', '*', '1', 'x', 'h', '.', '2', '3', '4', 'D', 'H', 'X']
graph_i = 0
chain_lengths = []


class Stats:

    def __init__(self, filename):
        self.logfile = filename
        file = open(filename, 'r')
        self.lines = file.readlines()
        file.close()
        self.df = None
        self.seed_num = 0

    def create_time_graph(self, fig1: plt.Figure, fig2: plt.Figure, y: str = 'runs',
                          with_mut_type_times: bool = False, number: int = 0):
        def get_time(entry, times: list, key: str = 'solve_time'):
            if not math.isnan(entry[key]):
                time = entry[key] / SEC_IN_HOUR
                times.append(time)
                # print(entry['filename'], time * SEC_IN_HOUR)
                return time
            else:
                return 0
        num_axis = []
        time_axis = []
        ratio_axis = []
        total_solve_time = 0
        total_mut_time = 0
        total_trace_time = 0
        total_model_time = 0
        total_select_time = 0
        ax1 = fig1.gca()
        ax2 = fig2.gca()
        num = 0
        time_ind = self.df['current_time'].notnull()
        status_ind = self.df['status'].notnull()
        status_rows = self.df[status_ind]

        solve_times = []
        mut_times = []
        trace_times = []
        model_times = []
        select_times = []

        if with_mut_type_times:
            mut_type_times = defaultdict(float)
            mut_type_ind = self.df['mut_type'].notnull()

            for j, entry in self.df[mut_type_ind].iterrows():
                mut_type = entry['mut_type']
                mut_type = mut_type.split('(')[0]
                mut_type_times[mut_type] += entry['mut_time'] / SEC_IN_HOUR

        k = -self.seed_num
        entry = self.df[time_ind].iloc[0]
        fst_time = entry['current_time']
        last_time = fst_time

        for i, entry in self.df[time_ind].iterrows():
            if entry['status'] == 'seed':
                continue
            total_solve_time += get_time(entry, solve_times, 'solve_time')
            total_mut_time += get_time(entry, mut_times, 'mut_time')
            if 'trace_time' in entry:
                total_trace_time += get_time(entry, trace_times, 'trace_time')
                total_model_time += get_time(entry, model_times, 'model_time')
                total_select_time += get_time(entry, select_times, 'select_time')

            time = (entry['current_time'] - fst_time) / SEC_IN_HOUR
            if time > DAY:
                break
            time_axis.append(time)

            if not math.isnan(entry['solve_time']):
                time = (entry['current_time'] - last_time)/entry['solve_time']
            else:
                time = 0
            ratio_axis.append(time)

            if y == 'bugs':
                k += 1
                if 0 < k and status_rows.iloc[k]['status'] in {'bug', 'wrong_model'}:
                    num += 1
            else:
                num = entry[y]
            num_axis.append(num)
            last_time = entry['current_time']
        total_time = (last_time - fst_time) / SEC_IN_HOUR

        ax1.set_xlabel('Time, h')
        if y == 'bugs':
            ax1.set_ylabel('Bugs')
        else:
            ax1.set_ylabel('Inputs solved')
            # ax2.set_xlabel('Inputs')
            # ax2.set_ylabel('Solving time to total time')
            # ax2.plot(num_axis, ratio_axis)

        ax1.plot(time_axis, num_axis)
        ax1.grid()

        print("Total time:", round(total_time, ROUND_NUM))
        print("Mean solving time:", round(mean(solve_times), ROUND_NUM))
        print()
        print("Solving:", round(total_solve_time, ROUND_NUM), round(total_solve_time / total_time, ROUND_NUM))
        print("Mutation:", round(total_mut_time, ROUND_NUM), round(total_mut_time / total_time, ROUND_NUM))
        if 'trace_time' in entry:
            print("Trace processing:", round(total_trace_time, ROUND_NUM), round(total_trace_time / total_time, ROUND_NUM))
            print("Model check:", round(total_model_time, ROUND_NUM), round(total_model_time / total_time, ROUND_NUM))
            print("Instance selection:", round(total_select_time, ROUND_NUM), round(total_select_time / total_time, ROUND_NUM))

        print(round((total_solve_time + total_mut_time + total_trace_time +
                    total_model_time + total_select_time)/ total_time, ROUND_NUM))
        print()

        if with_mut_type_times:
            sorted_mut_type_times = dict(sorted(mut_type_times.items(),
                                                key=lambda item: item[1],
                                                reverse=True))
            for mut in sorted_mut_type_times:
                print(mut, sorted_mut_type_times[mut] / total_mut_time)

    def create_traces_time_graph(self, fig: plt.Figure):
        global graph_i

        time_axis = []
        unique_traces_axis = []
        # coef = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()

        fst_entry = self.df[ind].iloc[0]
        fst_time = fst_entry['current_time']
        last_entry = self.df[ind].iloc[-1]
        last_time = last_entry['current_time']
        total_time = (last_time - fst_time) / SEC_IN_HOUR
        print("Total time:", round(total_time, ROUND_NUM))

        cur_trace = 0
        cur_run = 0
        j = 0
        last_time = None
        for i, entry in self.df[ind].iterrows():
            cur_time = entry['current_time']
            cur_trace = entry['unique_traces']
            cur_run = entry['runs']
            if i >= self.seed_num and \
                    (not last_time or
                     cur_time - last_time >= SEC_IN_HOUR):
                time = (cur_time - fst_time) / SEC_IN_HOUR
                if time > DAY:
                    break
                time_axis.append(time)
                unique_traces_axis.append(cur_trace)
                last_time = cur_time
            j += 1

        print("Run number:", cur_run)
        print("Trace number:", cur_trace)

        ax.set_ylabel('Unique traces')
        ax.set_xlabel('Time, h')

        # lin_coef = mean(coef)
        # ax.plot(time_axis, [item * lin_coef for item in time_axis], c='black', linestyle='--')
        ax.plot(time_axis, unique_traces_axis, marker=markers[graph_i], fillstyle='none')
        ax.grid()
        graph_i += 1

    def get_mutation_weights(self):
        entries_ind = self.df[self.df['SWAP_AND'].notnull()].index.tolist()
        last_ind = entries_ind[-1]
        last_entry = self.df.iloc[last_ind]
        mut_weights_ind = last_entry.notnull()
        mut_weights = last_entry[mut_weights_ind][2:]
        with open('stats/mut-weights.txt', 'w+') as file:
            sorted_weights = dict()
            mut_names = mut_weights.index.values
            for i, entry in enumerate(mut_weights):
                sorted_weights[mut_names[i]] = round(entry, 5)
            sorted_weights = dict(sorted(sorted_weights.items(),
                                         key=lambda item: item[1],
                                         reverse=True))
            for mut_name in sorted_weights:
                file.writelines([mut_name,
                                 ' ',
                                 str(sorted_weights[mut_name]),
                                 '\n'])

    def analyze_entries(self, status: str, log_i: int):
        def add_to_count_dict(cur_dict: defaultdict, filename: str):
            if len(cur_dict[filename]) > log_i:
                cur_dict[filename][log_i] += 1
            else:
                while len(cur_dict[filename]) < log_i:
                    cur_dict[filename].append(0)
                cur_dict[filename].append(1)

        global num_dict, count_dict, chain_lengths

        ind = self.df['filename'].notnull()
        num = 0
        status_num = 0
        for i, entry in self.df.loc[ind].iterrows():
            filename = entry['filename']
            num += 1
            # mutation = entry['mut_type'].split('(')[0]
            add_to_count_dict(num_dict, entry['status'])
            if entry['status'] == status:
                if status != 'wrong_model' or entry['model_state'] != -1:
                    continue
                status_num += 1
                add_to_count_dict(count_dict, entry['mut_type'])
        num_dict[''].append(num)
        count_dict[''].append(status_num)


def prepare_data(name: str):
    stats = Stats(name)

    entries = []
    for line in stats.lines:
        try:
            entry = json.loads(line)
            if not stats.seed_num and 'seed_number' in entry:
                info = entry
                stats.seed_num = info['seed_number']
            elif 'general_info' in entry or 'run_info' in entry \
                    or 'update_mutation_weights' in entry:
                entries.append(list(entry.values())[0])
            elif 'context_deletion_error' not in entry:
                entries.append(entry)

        except Exception:
            pass
            # print('Can\'t read the line:', line)
    stats.df = pd.DataFrame(entries)
    return stats


def analyze(log_names: list, stats: list, select: list, options: list):
    global num_dict

    if not os.path.exists('stats'):
        os.makedirs('stats')

    traces = plt.figure()
    times = plt.figure()
    time_ratio = plt.figure()
    legend = []

    for i, name in enumerate(log_names):
        cur_stats = prepare_data(name)
        if not stats:
            for status in select:
                cur_stats.analyze_entries(status, i)

        if 'traces' in stats:
            cur_stats.create_traces_time_graph(traces)
        with_mut_type_times = True if 'with_mut_type_times' in options else False
        if 'runs' in stats:
            cur_stats.create_time_graph(times, time_ratio, 'runs', with_mut_type_times, i)
        if 'bugs' in stats:
            cur_stats.create_time_graph(times, time_ratio, 'bugs', with_mut_type_times, i)
        if 'mutations' in stats:
            cur_stats.get_mutation_weights()

        legend.append(name.split('/')[-1])

    if 'traces' in stats:
        traces.legend(legend, loc='upper left')
        traces.savefig('stats/traces.png', bbox_inches='tight')

    if 'runs' in stats:
        times.legend(legend, loc='upper left')
        times.savefig('stats/runs.png', bbox_inches='tight')
        # time_ratio.legend(legend)
        # time_ratio.savefig('stats/ratio.png', bbox_inches='tight')

    if 'bugs' in stats:
        times.legend(legend, loc='upper left')
        times.savefig('stats/bugs.png', bbox_inches='tight')

    num_dict = dict(sorted(num_dict.items(),
                           key=lambda item: item[1][0],
                           reverse=True))
    for key in num_dict:
        if num_dict[key][0] > 1:
            print(key, num_dict[key][0])
        # if count_dict[key]:
        #     print(key, count_dict[key])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('logfile',
                        nargs='*',
                        default=['logfile'])
    parser.add_argument('-stats',
                        nargs='*',
                        choices=['runs', 'traces', 'mutations', 'bugs', 'cov'],
                        default=[],
                        help='what statistics do you want to see')
    parser.add_argument('-select',
                        nargs='*',
                        choices=['seed_unknown', 'seed_timeout',
                                 'solver_conflict', 'mutant_timeout',
                                 'mutant_unknown', 'error', 'bug',
                                 'wrong_model', 'model_timeout', 'pass',
                                 'timeout_before_check', 'without_change'],
                        default=[''],
                        help='what kind of log entries do you want to see')
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['with_mut_type_times'],
                        default=[])
    argv = parser.parse_args()

    plt.rc('font', size=11)
    log_names = get_filenames(argv.logfile)
    analyze(log_names, argv.stats, argv.select, argv.options)


if __name__ == '__main__':
    main()
