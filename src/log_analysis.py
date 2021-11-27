import json
import argparse
import math
import os
from collections import defaultdict
from prettytable import PrettyTable
from statistics import mean

import pandas as pd
import matplotlib.pyplot as plt

INPUTS_GROUP_NUM = 500
MUT_TABLE_COLUMN_NUMBER = 8

unique_traces = 0
mutations = set()
mut_traces_axis = defaultdict(list)
mut_num_axis = defaultdict(list)
mut_traces = defaultdict(int)
mut_num = defaultdict(int)


class Stats:

    def __init__(self, filename):
        self.logfile = filename
        file = open(filename, 'r')
        self.lines = file.readlines()
        file.close()
        self.df = None
        self.seed_num = 0

    def create_time_graph(self, fig: plt.Figure):
        num_axis = []
        time_axis = []
        total_mut_time = time = 0
        ax = fig.gca()
        solve_time_ind = self.df['solve_time'].notnull()
        for i, entry in self.df[solve_time_ind].iterrows():
            if not math.isnan(entry['mut_time']):
                total_mut_time += entry['mut_time'] / 3600
            time += entry['solve_time'] / 3600
            time_axis.append(time)
            num = entry['runs']
            num_axis.append(num)

        total_time_ind = self.df['current_time'].notnull()
        entry = self.df[total_time_ind].iloc[0]
        fst_time = entry['current_time']
        entry = self.df[total_time_ind].iloc[-1]
        last_time = entry['current_time']
        total_time = (last_time - fst_time) / 3600

        ax.set_xlabel('Time, h')
        ax.set_ylabel('Inputs solved')
        ax.plot(time_axis, num_axis)
        print('The ratio of mutation time to total time:',
              total_mut_time/total_time)

    def create_traces_graph(self, fig: plt.Figure):
        num_axis = []
        unique_traces_axis = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()
        for i, entry in self.df[ind].iterrows():
            unique_traces_axis.append(entry['unique_traces'])
            num_axis.append(entry['runs'])
        ax.set_ylabel('Unique traces')
        ax.set_xlabel('Inputs solved')
        ax.plot(num_axis, unique_traces_axis)

    def get_mutation_stats(self):
        global unique_traces
        ind = self.df['mut_type'].notnull()

        for i, entry in self.df[ind].iterrows():
            if not unique_traces:
                unique_traces = self.df.loc[i - 1]['unique_traces']
            mut = entry['mut_type'].split('(')[0]
            mutations.add(mut)
            new_unique_traces = self.df.loc[i + 1]['unique_traces']
            mut_traces[mut] += new_unique_traces - unique_traces
            mut_traces_axis[mut].append(mut_traces[mut])
            mut_num[mut] += 1
            mut_num_axis[mut].append(mut_num[mut])
            unique_traces = new_unique_traces

        self.create_mutation_table()

    def create_mutation_table(self):
        groups_num = []
        for mut in mutations:
            groups_num.append(mut_num[mut] // INPUTS_GROUP_NUM)
        groups_lim = round(mean(groups_num))
        rows = [INPUTS_GROUP_NUM * i for i in range(1, groups_lim + 1)] + \
               ['——', 'Average']
        columns = defaultdict(list)

        for mut in mutations:
            mut_num_axis[mut].insert(0, 0)
            mut_traces_axis[mut].insert(0, 0)

            avg = 0
            for i in range(len(rows[:-2])):
                num = rows[i]
                if mut_num_axis[mut][-1] >= num:
                    columns[mut].append(
                        round(mut_traces_axis[mut][num] / num, 4))
                else:
                    if not avg:
                        avg = mean(columns[mut])
                    columns[mut].append('')
            if not avg:
                avg = mean(columns[mut])
            columns[mut] += ['——', (round(avg, 4))]
            print('mut_types[\'' + str(mut) + '\'] =', round(avg, 4))

        columns = {mut: col for mut, col in
                   sorted(columns.items(), key=lambda item: item[1][-1])}

        with open('stats/mut_table.' + self.logfile + '.txt', 'a') as file:
            file.truncate(0)
            for i, mut in enumerate(columns):
                if i % MUT_TABLE_COLUMN_NUMBER == 0:
                    if i > 0:
                        file.write(table.get_string() + '\n')
                    table = PrettyTable()
                    table.add_column('Mutated inputs', rows)
                table.add_column(mut, columns[mut])
            if len(columns) < MUT_TABLE_COLUMN_NUMBER:
                file.write(table.get_string() + '\n')

    def analyze_entries(self, status: str):
        print('_______________' + status +
              '_______________', end='\n')
        ind = self.df['status'] == status
        for i, entry in self.df.loc[ind].iterrows():
            print(entry['filename'], end='\n')


def analyze(log_names: list, options: list, select: list):
    if not os.path.exists('stats'):
        os.makedirs('stats')

    traces = plt.figure()
    times = plt.figure()
    stats = []
    min_len = -1
    legend = []
    for i, name in enumerate(log_names):
        stats.append(Stats(name))
        min_len = len(stats[i].lines) if min_len == -1 \
            else min(len(stats[i].lines), min_len)

    for cur_stats in stats:
        entries = []
        info = {'heuristics': []}
        for line in cur_stats.lines:  # or stats[i].lines[:min_len]:
            try:
                entry = json.loads(line)
                if not cur_stats.seed_num and 'seed_number' in entry:
                    info = entry
                    cur_stats.seed_num = info['seed_number']
                else:
                    entries.append(list(entry.values())[0])
            except Exception:
                print('Can\'t read the line:', line)
        cur_stats.df = pd.DataFrame(entries)

        for heur in info['heuristics']:
            if heur == 'transitions':
                legend.append('Trace transition heuristic')
            elif heur == 'states':
                legend.append('Trace state heuristic')
            elif heur == 'difficulty':
                legend.append('Complexity heuristic')
            else:
                legend.append('Default')

        if select:
            for status in select:
                cur_stats.analyze_entries(status)

        if 'traces' in options:
            cur_stats.create_traces_graph(traces)
        if 'time' in options:
            cur_stats.create_time_graph(times)
        if 'mutations' in options:
            cur_stats.get_mutation_stats()

    for cur_stats in stats:
        if 'traces' in options:
            traces.gca().axvline(x=cur_stats.seed_num,
                                 linestyle='--',
                                 color='k')
            traces.legend(legend, bbox_to_anchor=(0.9, 0.28))
            traces.savefig('stats/traces.png', bbox_inches='tight')

        if 'time' in options:
            times.gca().axhline(y=cur_stats.seed_num,
                                linestyle='--',
                                color='k')
            times.legend(legend, bbox_to_anchor=(0.9, 0.28))  # (0.49, 0.88)
            times.savefig('stats/times.png', bbox_inches='tight')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('logfile',
                        nargs='*',
                        default='logfile')
    parser.add_argument('-stats',
                        nargs='*',
                        choices=['time', 'traces', 'mutations'],
                        default={},
                        help='what statistics do you want to see')
    parser.add_argument('-select',
                        nargs='*',
                        choices=['seed_unknown', 'seed_timeout',
                                 'solver_conflict', 'mutant_timeout',
                                 'mutant_unknown', 'error', 'bug'],
                        default={},
                        help='what kind of log entries do you want to see')
    argv = parser.parse_args()

    analyze([argv.logfile], argv.stats, argv.select)


if __name__ == '__main__':
    main()
