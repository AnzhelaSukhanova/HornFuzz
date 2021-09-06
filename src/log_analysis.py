import json
import sys

import pandas as pd
import matplotlib.pyplot as plt

colors = ['firebrick', '#3dea62', '#6b57ff', '#434343']


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

    # def analyze_errors(self):
    #     ind = self.df['status'] == 'error'
    #     for i, entry in self.df.loc[ind].iterrows():
    #         print(entry['mut_chain'], entry['message'], end='\n')
    #
    # def analyze_unknown(self):
    #     ind = self.df['status'] == 'mutant_unknown'
    #     for i, entry in self.df.loc[ind].iterrows():
    #         print(entry['message'], entry['mut_chain'], end='\n')
    #
    # def analyze_bugs(self):
    #     ind = self.df['status'] == 'bug'
    #     for i, entry in self.df.loc[ind].iterrows():
    #         print(entry['mut_chain'], end='\n')


def main(log_names):
    traces = plt.figure()
    times = plt.figure()
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
        cur_stats.create_traces_graph(traces, i)
        cur_stats.create_time_graph(times, i)

    for cur_stats in stats:
        traces.gca().axvline(x=cur_stats.seed_num, linestyle='--', color='k')
        times.gca().axhline(y=cur_stats.seed_num, linestyle='--', color='k')

    traces.legend(legend, bbox_to_anchor=(0.9, 0.28))
    traces.savefig('traces.png', bbox_inches='tight')
    times.legend(legend, bbox_to_anchor=(0.9, 0.28))  # (0.49, 0.88)
    times.savefig('times.png', bbox_inches='tight')


if __name__ == '__main__':
    if len(sys.argv) < 2:
        log_names = ['logfile']
    else:
        log_names = sys.argv[1:]
    main(log_names)
