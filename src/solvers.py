import subprocess


def eldarica_check(filename, timeout) -> [str]:
    file = open('eldarica_output', 'w')
    p = subprocess.Popen(['./eldarica/eld', '-horn', '-t:' + str(timeout), filename],
                         stdout=file, stderr=file)
    try:
        p.wait(timeout)
        file.close()
        with open('eldarica_output', 'r') as file:
            state = file.readlines()[-1].rstrip()
    except subprocess.TimeoutExpired:
        p.kill()
        raise TimeoutError('Eldarica timeout')
    reason_unknown = '' if state == 'unknown' else ''
    return state, reason_unknown
