import json

LEFT_FILE = 'coverage-datailed.json'
RIGHT_FILE = 'coverage-datailed.json'


def line_info(lines):
    if lines is None:
        return None

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
    return {
        'all': all_line_numbers,
        'code': code_line_numbers,
        'covered': covered_line_numbers
    }


def line_coverage_summary(info):
    return info and {
        'all_lines': len(info['all']),
        'code_lines': len(info['code']),
        'covered_lines': len(info['covered']),
    }


def compare_line_coverage(left, right):
    if left and right and left['all'] != right['all']:
        raise Exception('All lines mismatch')
    if left and right and left['code'] != right['code']:
        raise Exception('Code lines mismatch')
    if left is None and right is None:
        return None
    all_info_source = left or right
    result = {
        'all': len(all_info_source['all']),
        'all_lines': all_info_source['all'],
        'code': len(all_info_source['code']),
        'code_lines': all_info_source['code'],
    }

    only_left_lines = left and left['covered']
    only_right_lines = right and right['covered']
    both_lines = None
    if only_left_lines is not None and only_right_lines is not None:
        both_lines = only_left_lines & only_right_lines
        only_left_lines = only_left_lines - both_lines
        only_right_lines = only_right_lines - both_lines

    result['both'] = both_lines and len(both_lines)
    result['both_lines'] = both_lines
    result['left'] = only_left_lines and len(only_left_lines)
    result['left_lines'] = only_left_lines
    result['right'] = only_right_lines and len(only_right_lines)
    result['right_lines'] = only_right_lines
    return result


def compare_coverage_files(left, right):
    files = left.keys() | right.keys()

    result = {}
    for file in sorted(files):
        left_info = line_info(left.get(file))
        right_info = line_info(right.get(file))
        result[file] = {
            'left_summary': line_coverage_summary(left_info),
            'right_summary': line_coverage_summary(right_info),
            'coverage': compare_line_coverage(left_info, right_info)
        }

    return result


def compare_coverage_reports(left, right):
    if left['gcovr/format_version'] != right['gcovr/format_version']:
        raise Exception('different report formats')
    left_files = {it['file']: it['lines'] for it in left['files']}
    right_files = {it['file']: it['lines'] for it in right['files']}
    if len(left_files) != len(left['files']):
        raise Exception('left: non unique files')
    if len(right_files) != len(right['files']):
        raise Exception('left: non unique files')

    return compare_coverage_files(left_files, right_files)


def main():
    with open(LEFT_FILE) as f:
        left_data = json.load(f)
    with open(RIGHT_FILE) as f:
        right_data = json.load(f)
    result = compare_coverage_reports(left_data, right_data)
    result_report = {
        'left': LEFT_FILE,
        'right': RIGHT_FILE,
        'coverage_diff': result
    }
    result_file_name = f'{LEFT_FILE}-{RIGHT_FILE}.diff.json'
    with open(result_file_name, 'w') as f:
        json.dump(result_report, f, default=list)


if __name__ == '__main__':
    main()
