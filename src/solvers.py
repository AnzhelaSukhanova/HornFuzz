import subprocess


def eldarica_check(filename, timeout) -> [str]:
    model = None
    file = open('eldarica_output', 'w')
    p = subprocess.Popen(['./eldarica/eld', '-horn', '-ssol', '-t:' + str(timeout), filename],
                         stdout=file, stderr=file)
    output = ''
    i = 0
    try:
        p.wait(timeout)
        file.close()
        with open('eldarica_output', 'r') as file:
            output = file.readlines()
            out_len = len(output)
            state = ''
            while state not in {'sat', 'unsat', 'unknown'} and i < out_len:
                state = output[i].rstrip()
                i += 1
    except subprocess.TimeoutExpired:
        p.kill()
        raise TimeoutError('Eldarica timeout')
    if state == 'sat' and i < out_len:
        model = output[i:]
        model = " ".join(model) if len(model) > 1 else model[0]
    reason_unknown = '' if state == 'unknown' else ''
    return state, model, reason_unknown
