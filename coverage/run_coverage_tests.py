BASE_DIR = '/tests'
Z3_BINARY = '/z3/build/z3'
QUERY_DIR = '/queries'

import os
from tqdm import tqdm

all_smt2_queries = [
    os.path.join(dp, f)
    for dp, dn, filenames in os.walk(BASE_DIR)
    for f in filenames
    if os.path.splitext(f)[1] == '.smt2'
]

for i, query_file in enumerate(tqdm(all_smt2_queries)):
    with open(query_file) as f:
        query = f.read()
    if '(set-logic HORN)' not in query:
        query = '(set-logic HORN)\n{}'.format(query)
    if '(check-sat)' not in query:
        query = '{}\n(check-sat)'.format(query)
    if '(get-model)' not in query:
        query = '{}\n(get-model)'.format(query)

    actual_query = os.path.join(QUERY_DIR, query_file)
    with open(actual_query, 'w') as f:
        f.write(query)
    os.system('{} {} > /dev/null 2>&1'.format(Z3_BINARY, actual_query))
