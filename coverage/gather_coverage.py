import os

print('Gather coverage')
os.system('cd z3 && gcovr --json-summary /coverage/coverage.json --html /coverage/coverage.html --gcov-executable "llvm-cov gcov" .')
print('Gather detailed coverage')
os.system('mkdir /coverage/cov-details')
os.system('cd z3 && gcovr --json /coverage/coverage-datailed.json --html-details /coverage/cov-details/coverage.html --gcov-executable "llvm-cov gcov" -r /z3/src --object-directory /z3/build')
