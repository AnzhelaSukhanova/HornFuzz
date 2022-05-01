SOURCE = ''
TARGET = 'tests/'
EXCLUDE_FILE = '../exclude_seed.json'

import os
import json

exclude = set(json.load(open(EXCLUDE_FILE)))
files = [
    os.path.join(dp, f)
    for dp, dn, filenames in os.walk(SOURCE)
    for f in filenames
    if os.path.splitext(f)[1] == '.smt2'
]

filtered_files = [f for f in files if f not in exclude]

for file in filtered_files:
    os.system('cp {} {}'.format(file, TARGET))
