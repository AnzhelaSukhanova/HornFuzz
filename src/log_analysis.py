import json
import sys
from collections import defaultdict
from prettytable import PrettyTable
from statistics import mean

import pandas as pd
import matplotlib.pyplot as plt

colors = ['red', 'gold', 'aqua', '#3dea62', '#6b57ff',
          'deeppink', 'indigo', 'coral']
unique_traces = 0
mutations = ['SWAP_AND', 'DUP_AND', 'BREAK_AND',
             'SWAP_OR', 'MIX_BOUND_VARS', 'UNION',
             'SIMPLIFY', 'ADD_INEQ']
mut_traces_axis = defaultdict(list)
mut_num_axis = defaultdict(list)
mut_traces = defaultdict(int)
mut_num = defaultdict(int)


class Stats:

    def __init__(self, log_name):
        file = open(log_name, 'r')
        self.lines = file.readlines()
        file.close()
        self.df = None
        self.seed_num = 0

    def create_time_graph(self, fig, color_i):
        num_axis = []
        time_axis = []
        total_time = 0
        last_time = 0
        ax = fig.gca()
        ind = self.df['time'].notnull()
        for i, entry in self.df[ind].iterrows():
            time = entry['time']
            num = entry['runs']
            if last_time:
                total_time += (time - last_time) / 3600
                time_axis.append(total_time)
                num_axis.append(num)
            last_time = time
        ax.set_xlabel('Time, h')
        ax.set_ylabel('Inputs solved')
        ax.plot(time_axis, num_axis, colors[color_i])

    def create_traces_graph(self, fig, color_i):
        num_axis = []
        unique_traces_axis = []
        ax = fig.gca()
        ind = self.df['unique_traces'].notnull()
        for i, entry in self.df[ind].iterrows():
            unique_traces_axis.append(entry['unique_traces'])
            num_axis.append(entry['runs'])
        ax.set_ylabel('Unique traces')
        ax.set_xlabel('Inputs solved')
        ax.plot(num_axis,
                unique_traces_axis,
                colors[color_i])

    def get_mutation_stats(self, fig, is_end=False):
        global unique_traces
        ind = self.df['mut_type'].notnull()
        ind += self.df['mut_chain'].notnull()
        ax = fig.gca()
        legend = []

        for i, entry in self.df[ind].iterrows():
            if not unique_traces:
                unique_traces = self.df.loc[i - 1]['unique_traces']
            if pd.notna(entry['mut_type']):
                mut = entry['mut_type'].split('(')[0]
            else:
                mut = entry['mut_chain'].split('->')[-1]
            new_unique_traces = self.df.loc[i + 1]['unique_traces']
            mut_traces[mut] += new_unique_traces - unique_traces
            mut_traces_axis[mut].append(mut_traces[mut])
            mut_num[mut] += 1
            mut_num_axis[mut].append(mut_num[mut])
            unique_traces = new_unique_traces

        if is_end:
            ax.set_ylabel('Unique traces')
            ax.set_xlabel('Inputs solved')

            for i, mut in enumerate(mutations):
                legend.append(mut)
                mut_num_axis[mut].insert(0, 0)
                mut_traces_axis[mut].insert(0, 0)
                ax.plot(mut_num_axis[mut],
                        mut_traces_axis[mut],
                        colors[i])
            with open('mut_table.txt', 'w+') as file:
                file.write(self.get_mutation_table().get_string())
            fig.legend(legend, bbox_to_anchor=(0.9, 0.5))

    def get_mutation_table(self):
        table = PrettyTable()
        rows = [1000 * i for i in range(1, 19)] + ['——', 'Average']
        columns = defaultdict(list)
        table.add_column('Mutated inputs', rows)

        for mut in mutations:
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

        columns = {mut: col for mut, col in
                   sorted(columns.items(), key=lambda item: item[-1])}
        for mut in columns:
            table.add_column(mut, columns[mut])
        return table

    def analyze_entries(self, status):
        print('____________' + status + '____________', end='\n')
        ind = self.df['status'] == status
        for i, entry in self.df.loc[ind].iterrows():
            print(entry['filename'], entry['message'], end='\n')


def main(log_names):
    traces = plt.figure()
    times = plt.figure()
    mut = plt.figure()
    stats = []
    min_len = -1
    legend = []
    for i, name in enumerate(log_names):
        stats.append(Stats(name))
        min_len = len(stats[i].lines) if min_len == -1 \
            else min(len(stats[i].lines), min_len)

    for i, cur_stats in enumerate(stats):
        entries = []
        info = json.loads(cur_stats.lines[0])
        cur_stats.seed_num = info['seed_number']
        for line in cur_stats.lines[1:]:  # or stats[i].lines[1:min_len]:
            entry = json.loads(line)
            entries.append(list(entry.values())[0])
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
        # cur_stats.analyze_entries('mutant_unknown')
        # cur_stats.analyze_entries('mutant_timeout')
        # cur_stats.analyze_entries('error')
        # cur_stats.analyze_entries('bug')
        cur_stats.create_traces_graph(traces, i)
        cur_stats.create_time_graph(times, i)
        cur_stats.get_mutation_stats(mut, i == len(stats) - 1)

    for cur_stats in stats:
        traces.gca().axvline(x=cur_stats.seed_num, linestyle='--', color='k')
        times.gca().axhline(y=cur_stats.seed_num, linestyle='--', color='k')

    traces.legend(legend, bbox_to_anchor=(0.9, 0.28))
    traces.savefig('traces.png', bbox_inches='tight')
    times.legend(legend, bbox_to_anchor=(0.9, 0.28))  # (0.49, 0.88)
    times.savefig('times.png', bbox_inches='tight')
    mut.savefig('mut.png', bbox_inches='tight')


if __name__ == '__main__':
    if len(sys.argv) < 2:
        log_names = ['logfile']
    else:
        log_names = sys.argv[1:]
    main(log_names)
