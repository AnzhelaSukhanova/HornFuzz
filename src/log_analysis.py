import json
import argparse
import math
import os
from collections import defaultdict

import pandas as pd
import matplotlib.pyplot as plt

INPUTS_GROUP_NUM = 1
MUT_TABLE_COLUMN_NUMBER = 8

unique_traces = 0


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

    def get_mutation_weights(self):
        entries_ind = self.df[self.df['SWAP_AND'].notnull()].index.tolist()
        last_ind = entries_ind[-1]
        last_entry = self.df.iloc[last_ind]
        mut_weights_ind = last_entry.notnull()
        mut_weights = last_entry[mut_weights_ind]
        with open('stats/mut_weights.txt', 'w+') as file:
            file.write(mut_weights.to_string())

    def analyze_entries(self, status: str):
        print('_______________' + status +
              '_______________', end='\n')
        ind = self.df['status'] == status
        for i, entry in self.df.loc[ind].iterrows():
            print(entry['filename'], entry['message'],
                  end='\n')


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
                elif 'context_deletion_error' not in entry:
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
            cur_stats.get_mutation_weights()

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
                        default=['logfile'])
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

    analyze(argv.logfile, argv.stats, argv.select)


if __name__ == '__main__':
    main()
