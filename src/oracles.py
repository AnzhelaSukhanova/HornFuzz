import subprocess

TIMEOUT = 50


def solve(name, filename):
    if name == 'Eldarica':
        file = open('oracle_output', 'w')
        p = subprocess.Popen(['./eldarica/eld', '-horn', '-t:' + str(TIMEOUT),
                              filename], stdout=file, stderr=file)
        try:
            p.wait(TIMEOUT)
            file.close()
            with open('oracle_output', 'r') as file:
                state = file.readlines()[-1].rstrip()
                if not state:
                    state = 'unknown'
        except subprocess.TimeoutExpired:
            p.kill()
            print('Eldarica: timeout')
            state = 'unknown'
        return state
    else:
        assert False, 'Wrong solver name'
