import argparse
import json
import math
import os
from collections import defaultdict

import matplotlib.pyplot as plt
import pandas as pd
from prettytable import PrettyTable

INPUTS_GROUP_NUM = 1
SEC_IN_HOUR = 3600
DAY = 24
ROUND_NUM = 5

unique_traces = 0
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

    def create_time_graph(self, fig: plt.Figure, y: str, with_mut_type_times: bool, graph_i: int):
        num_axis = []
        time_axis = []
        total_mut_time = 0
        total_solve_time = 0
        ax = fig.gca()
        num = 0
        time_ind = self.df['current_time'].notnull()
        status_ind = self.df['status'].notnull()
        status_rows = self.df[status_ind]

        solve_times = []
        mut_times = []

        if with_mut_type_times:
            mut_type_times = defaultdict(float)
            mut_type_ind = self.df['mut_type'].notnull()
            mut_type_rows = self.df[mut_type_ind]
            j = -1

        k = -self.seed_num
        entry = self.df[time_ind].iloc[0]
        fst_time = entry['current_time']
        last_entry = self.df[time_ind].iloc[-1]
        if last_entry['current_time'] - fst_time < DAY * SEC_IN_HOUR:
            return

        for i, entry in self.df[time_ind].iterrows():
            if not math.isnan(entry['solve_time']):

                if with_mut_type_times and not math.isnan(entry['mut_type']):
                    j += 1
                    mut_type = mut_type_rows.iloc[j]['mut_type']
                    mut_type = mut_type.split('(')[0]
                    mut_type_times[mut_type] += entry['mut_time'] / SEC_IN_HOUR

                if not math.isnan(entry['mut_time']):
                    mut_times.append(entry['mut_time'] / SEC_IN_HOUR)
                    total_mut_time += entry['mut_time'] / SEC_IN_HOUR
                solve_times.append(entry['solve_time'] / SEC_IN_HOUR)
                total_solve_time += entry['solve_time'] / SEC_IN_HOUR
            time = (entry['current_time'] - fst_time) / SEC_IN_HOUR
            if time > DAY:
                break

            time_axis.append(time)
            if y == 'bugs':
                k += 1
                if 0 < k and status_rows.iloc[k]['status'] in {'bug', 'wrong_model'}:
                    num += 1
            else:
                num = entry[y]
            num_axis.append(num)

        entry = self.df[time_ind].iloc[-1]
        last_time = entry['current_time']
        total_time = (last_time - fst_time) / SEC_IN_HOUR

        ax.set_xlabel('Time, h')
        if y == 'bugs':
            ax.set_ylabel('Bugs')
        else:
            ax.set_ylabel('Inputs solved')

        ax.plot(time_axis, num_axis)

        # print('Mutation time to total time:',
        #       round(total_mut_time / total_time, ROUND_NUM))
        # print("Mutation time:", round(total_mut_time, ROUND_NUM))
        # print('Solving time to total time:',
        #       round(total_solve_time / total_time, ROUND_NUM))
        # print("Solving time:", round(total_solve_time, ROUND_NUM))
        # print("Mean solving time:", round(mean(solve_times), ROUND_NUM))
        # print("Total time:", round(total_time, ROUND_NUM))


        if with_mut_type_times:
            sorted_mut_type_times = dict(sorted(mut_type_times.items(),
                                           key=lambda item: item[1],
                                           reverse=True))
            for mut in sorted_mut_type_times:
                print(mut, sorted_mut_type_times[mut] / total_time)

    def create_traces_time_graph(self, fig: plt.Figure):
        global graph_i

        time_axis = []
        unique_traces_axis = []
        coef = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()

        fst_entry = self.df[ind].iloc[0]
        fst_time = fst_entry['current_time']
        last_entry = self.df[ind].iloc[-1]
        last_time = last_entry['current_time']
        total_time = (last_time - fst_time) / SEC_IN_HOUR
        if total_time < DAY:
            return
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
        graph_i += 1

    def create_traces_runs_graph(self, fig: plt.Figure):
        global graph_i

        time_axis = []
        unique_traces_axis = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()
        last_trace = 0
        j = 0
        for i, entry in self.df[ind].iterrows():
            if i >= self.seed_num and \
                    (entry['unique_traces'] - last_trace > 2000):
                last_trace = entry['unique_traces']
                unique_traces_axis.append(last_trace)
                time_axis.append(entry['runs'])
            j += 1
        ax.set_ylabel('Количество уникальных трасс')
        ax.set_xlabel('Количество прогонов')
        ax.plot(time_axis, unique_traces_axis, marker=markers[graph_i], fillstyle='none')
        # c=colors[graph_i],  fillstyle='none')
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
                sorted_weights[mut_names[i]] = entry
            sorted_weights = dict(sorted(sorted_weights.items(),
                                         key=lambda item: item[1],
                                         reverse=True))
            for mut_name in sorted_weights:
                file.writelines([mut_name,
                                 ' ',
                                 str(sorted_weights[mut_name]),
                                 '\n'])

    def analyze_entries(self, status: str, log_i: int):
        global count_dict, chain_lengths

        # print('_______________' + status +
        #       '_______________', end='\n')
        ind = self.df['status'] == status
        # ind = self.df['filename'].notnull()
        num = 0
        for i, entry in self.df.loc[ind].iterrows():
            if status == 'wrong_model' and entry['model_state'] != -1:
                continue
            filename = entry['filename']
            num += 1
            mutation = entry['mut_type'].split('(')[0]
            chain_len = len(entry['mut_chain'].split('->'))
            chain_lengths.append(chain_len)
            # if len(count_dict[mutation]) > log_i:
            #     count_dict[mutation][log_i] += 1
            # else:
            #     while len(count_dict[mutation]) < log_i:
            #         count_dict[mutation].append(0)
            #     count_dict[mutation].append(1)
        # count_dict[''].append(num)


def prepare_data(name: str):
    stats = Stats(name)

    entries = []
    for line in stats.lines:
        try:
            entry = json.loads(line)
            if not stats.seed_num and 'seed_number' in entry:
                info = entry
                stats.seed_num = info['seed_number']
            elif 'context_deletion_error' not in entry:
                entries.append(list(entry.values())[0])

        except Exception:
            print('Can\'t read the line:', line)
    stats.df = pd.DataFrame(entries)
    return stats


def analyze(log_names: list, stats: list, select: list, options: list):
    global count_dict

    if not os.path.exists('stats'):
        os.makedirs('stats')

    traces = plt.figure()
    times = plt.figure()
    legend = []

    for i, name in enumerate(log_names):
        cur_stats = prepare_data(name)
        if select:
            for status in select:
                cur_stats.analyze_entries(status, i)

        if 'traces' in stats:
            cur_stats.create_traces_time_graph(traces)
            # cur_stats.create_traces_runs_graph(traces)
        with_mut_type_times = True if 'with_mut_type_times' in options else False
        if 'runs' in stats:
            cur_stats.create_time_graph(times, 'runs', with_mut_type_times, i)
        if 'bugs' in stats:
            cur_stats.create_time_graph(times, 'bugs', with_mut_type_times, i)
        if 'mutations' in stats:
            cur_stats.get_mutation_weights()

        legend.append(name.split('/')[-1])
    # legend.append('Random order')
    # legend.append('Simple instance heuristic')
    # legend.append('Complex instance heuristic')
    # legend.append('Rare transition heuristic')
    # legend.append('Linear approximation')

    print(sorted(chain_lengths))
    if 'traces' in stats:
        traces.legend(legend)  # (0.49, 0.88)
        traces.savefig('stats/traces.png', bbox_inches='tight')

    if 'runs' in stats or 'bugs' in stats:
        times.legend(legend) # (0.9, 0.28))
        times.savefig('stats/times.png', bbox_inches='tight')

    if select:
        table = PrettyTable()
        #table.field_names = ['seed'] + log_names
        table.field_names = ['mutation', 'transitions + parameters',
                             'transitions', 'default + parameters', 'default']
        count_dict = dict(sorted(count_dict.items(),
                                 key=lambda item: item[1][0],
                                 reverse=True))
        for key in count_dict:
            row = [key[:55]] + count_dict[key]
            while len(row) < 5:
                row += [0]
            try:
                table.add_row(row)
            except Exception:
                print(row)
                break
        print(table)


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
                        default=[],
                        help='what kind of log entries do you want to see')
    parser.add_argument('-options', '-opt',
                        nargs='*',
                        choices=['with_mut_type_times'],
                        default=[])
    argv = parser.parse_args()

    plt.rc('font', size=11)
    log = argv.logfile
    if os.path.isdir(log[0]):
        log = []
        for root, subdirs, files in os.walk(argv.logfile[0]):
            for file in files:
                path = os.path.join(root, file)
                log.append(path)
    analyze(log, argv.stats, argv.select, argv.options)


if __name__ == '__main__':
    main()
