import json
from typing import Optional

import pandas as pd
from dataclasses import dataclass

COVERAGE = {
    'seed': 'coverage-datailed.json',
    'best': 'coverage-datailed.json',
    'worst': 'coverage-datailed.json',
}


class Analysis:
    pass


@dataclass
class Minus(Analysis):
    left: object
    right: object

    def __str__(self):
        left = str(self.left) if not isinstance(self.left, Analysis) else f'({str(self.left)})'
        right = str(self.right) if not isinstance(self.right, Analysis) else f'({str(self.right)})'
        return f'{left} - {right}'


@dataclass
class Pick(Analysis):
    name: str

    def __str__(self):
        return self.name


ANALYZE = [
    Pick('seed'),
    Pick('best'),
    Pick('worst'),
    Minus('best', 'seed'),
    Minus('worst', 'seed'),
    Minus(Minus('best', 'seed'), 'worst'),
    Minus(Minus('worst', 'seed'), 'best')
]


@dataclass
class Coverage:
    all: set
    code: set
    covered: set


def line_info(lines):
    all_line_numbers = set()
    code_line_numbers = set()
    covered_line_numbers = set()

    for line in lines:
        line_number = line['line_number']
        all_line_numbers.add(line_number)
        if line['gcovr/noncode']:
            continue
        code_line_numbers.add(line_number)
        if line['count'] > 0:
            covered_line_numbers.add(line_number)
    if len(all_line_numbers) != len(lines):
        raise Exception('Non unique line numbers')
    return Coverage(all_line_numbers, code_line_numbers, covered_line_numbers)


def parse_coverage_data(data):
    files = {it['file']: it['lines'] for it in data['files']}
    if len(files) != len(data['files']):
        raise Exception('non unique files')
    return {
        file: line_info(lines)
        for file, lines in files.items()
    }


def get_coverage(source, coverage_data, file) -> Coverage:
    if isinstance(source, Analysis):
        return analyze_file_coverage(source, coverage_data, file)
    else:
        return coverage_data[source].get(file)


def analyze_file_coverage(analysis, coverage_data, file) -> Optional[Coverage]:
    if isinstance(analysis, Minus):
        left = get_coverage(analysis.left, coverage_data, file)
        right = get_coverage(analysis.right, coverage_data, file)
        if left is None or right is None:
            return None
        if left.all != right.all:
            raise Exception('all lines mismatch')
        if left.code != right.code:
            raise Exception('code lines mismatch')
        return Coverage(left.all, left.code, left.covered - right.covered)
    if isinstance(analysis, Pick):
        return get_coverage(analysis.name, coverage_data, file)


def analyze(coverage_data):
    parsed_coverage_data = {
        name: parse_coverage_data(data)
        for name, data in coverage_data.items()
    }

    all_coverage_files = set()
    for data in parsed_coverage_data.values():
        all_coverage_files |= data.keys()

    df_columns = ['file', 'all_lines', 'code_lines'] + [str(it) for it in ANALYZE]
    data = pd.DataFrame(columns=df_columns)

    for file in sorted(all_coverage_files):
        all_lines = None
        code_lines = None
        res = {'file': file}
        for analysis in ANALYZE:
            coverage = analyze_file_coverage(analysis, parsed_coverage_data, file)
            all_lines = all_lines or coverage and coverage.all
            code_lines = code_lines or coverage and coverage.code
            res[str(analysis)] = coverage and len(coverage.covered)
        res['all_lines'] = all_lines and len(all_lines)
        res['code_lines'] = code_lines and len(code_lines)
        data = data.append(res, ignore_index=True)
    return data


def main():
    coverage_data = {}
    for name, file in COVERAGE.items():
        with open(file) as f:
            coverage_data[name] = json.load(f)
    result = analyze(coverage_data)
    a = 3


if __name__ == '__main__':
    main()
