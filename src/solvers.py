import subprocess


def eldarica_check(filename, timeout, parameters: dict = None):
    model = None
    file = open('eldarica_output', 'w')
    cmd_list = ['./eldarica/eld', '-horn', '-ssol', '-t:' + str(timeout)]
    if parameters:
        for mut_name in parameters:
            cmd_list.append(parameters[mut_name])
    cmd_list.append(filename)
    p = subprocess.Popen(cmd_list, stdout=file, stderr=file)
    i = 0
    try:
        p.wait(timeout)
        file.close()
    except subprocess.TimeoutExpired:
        p.kill()
        raise TimeoutError('Eldarica timeout')
    with open('eldarica_output', 'r') as file:
        output = file.readlines()
    out_len = len(output)
    state = ''
    while state not in {'sat', 'unsat', 'unknown'} and i < out_len:
        state = output[i].rstrip()
        i += 1
    if state not in {'sat', 'unsat', 'unknown'}:
        state = 'unknown'
    elif state == 'sat' and i < out_len:
        model = output[i:]
        model = " ".join(model) if len(model) > 1 else model[0]
    reason_unknown = "\n".join(output) if state == 'unknown' else ''
    return state, model, reason_unknown
