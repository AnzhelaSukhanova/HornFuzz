import os


def solve(name, filename):
    if name == 'eldarica':
        os.system('./eldarica/eld -horn -t:10 ' + filename + ' > oracle_result')
        with open('oracle_result', 'r') as file:
            status = file.readline().rstrip()
            if not status:
                status = 'unknown'
            return status
    else:
        assert False, 'Wrong solver name'
