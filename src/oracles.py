import subprocess

SOLVE_TIME_LIMIT = 50


def solve(name, filename):
    file = open('oracle_output', 'w')
    if name == 'Eldarica':
        p = subprocess.Popen(['./eldarica/eld', '-horn', '-t:' +
                              str(SOLVE_TIME_LIMIT), filename],
                             stdout=file, stderr=file)
    else:
        assert False, 'Wrong solver name'
    try:
        p.wait(SOLVE_TIME_LIMIT)
        file.close()
        with open('oracle_output', 'r') as file:
            state = file.readlines()[-1].rstrip()
    except subprocess.TimeoutExpired:
        p.kill()
        print(name + ': timeout')
        state = 'unknown'
    return state
