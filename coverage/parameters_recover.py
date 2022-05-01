BASE_DIR = '.'

import os
import json
from tqdm import tqdm

all_smt2_queries = [
    os.path.join(dp, f)
    for dp, dn, filenames in os.walk(BASE_DIR)
    for f in filenames
    if os.path.splitext(f)[1] == '.smt2'
]

DEFAULT_FALSE_PARAMS = {
    'SPACER.P3.SHARE_INVARIANTS',
    'SPACER.P3.SHARE_LEMMAS',
    # 'SPACER.PUSH_POB', -- takes a long time
    'SPACER.USE_LIM_NUM_GEN',
    'SPACER.RESET_POB_QUEUE',
    'SPACER.SIMPLIFY_LEMMAS_POST',
    'SPACER.SIMPLIFY_LEMMAS_PRE',
    'SPACER.SIMPLIFY_POB',
    'SPACER.USE_BG_INVS',
    'SPACER.USE_EUF_GEN',
    'SPACER.USE_LEMMA_AS_CTI',
    'XFORM.ARRAY_BLAST_FULL',
    'XFORM.COALESCE_RULES',
    'XFORM.ELIM_TERM_ITE',
    # 'XFORM.FIX_UNBOUND_VARS', -- often causes unknown
    'XFORM.INLINE_LINEAR_BRANCH',
    'XFORM.INSTANTIATE_ARRAYS',
    'XFORM.INSTANTIATE_ARRAYS.ENFORCE',
    'XFORM.INSTANTIATE_QUANTIFIERS',
    # 'XFORM.MAGIC', -- often causes unknown
    # 'XFORM.SCALE', -- often causes unknown
    'XFORM.QUANTIFY_ARRAYS',
    'XFORM.TRANSFORM_ARRAYS'
}

DEFAULT_TRUE_PARAMS = {
    'SPACER.CTP',
    'SPACER.ELIM_AUX',
    'SPACER.EQ_PROP',
    'SPACER.GROUND_POBS',
    'SPACER.KEEP_PROXY',
    'SPACER.MBQI',
    'SPACER.PROPAGATE',
    'SPACER.REACH_DNF',
    'SPACER.USE_ARRAY_EQ_GENERALIZER',
    'SPACER.USE_DERIVATIONS',
    'SPACER.USE_INC_CLAUSE',
    'SPACER.USE_INDUCTIVE_GENERALIZER',
    'XFORM.COI',
    'XFORM.COMPRESS_UNBOUND',
    'XFORM.INLINE_EAGER',
    'XFORM.INLINE_LINEAR',
    'XFORM.SLICE',
    'XFORM.TAIL_SIMPLIFIER_PVE'
}

INT_PARAMS = {
    'SPACER.ORDER_CHILDREN': 0,
    'SPACER.RANDOM_SEED': 0
}

ALL_PARAMS = DEFAULT_FALSE_PARAMS | DEFAULT_TRUE_PARAMS | INT_PARAMS.keys()


def print_param(param_name, param_value):
    return f'(set-option :fp.{param_name} {param_value})'.lower()


def restore_param_values(mutations):
    result = {}
    params = [m['type'] for m in mutations if m['type'] in ALL_PARAMS]
    for param in params:
        if param in INT_PARAMS:  # no way to restore value
            continue
        default_value = None
        if param in DEFAULT_TRUE_PARAMS:
            default_value = True
        if param in DEFAULT_FALSE_PARAMS:
            default_value = False
        current_value = result.get(param, default_value)
        if current_value is None:  # something went wrong
            continue
        result[param] = not current_value
    return result


def recover_query_parameters(query):
    mutations_line = None
    for line in query.split('\n'):
        if line.startswith('; ['):
            mutations_line = line
            break
    if mutations_line is None:
        return query
    mutations_line = mutations_line.lstrip(';')
    mutations = json.loads(mutations_line)
    params = restore_param_values(mutations)
    params_str = '\n'.join(print_param(p, v) for p, v in params.items())
    return params_str + '\n' + query


for file_name in tqdm(all_smt2_queries):
    with open(file_name, 'r') as query_file:
        original_query = query_file.read()
    recovered = recover_query_parameters(original_query)
    with open(file_name, 'w') as query_file:
        query_file.write(recovered)
