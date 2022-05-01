import os

os.system('gcovr --html /coverage/coverage.html --gcov-executable "llvm-cov gcov" /z3/')
os.system('gcovr --html-details /coverage/cov-details/coverage.html --gcov-executable "llvm-cov gcov" -r /z3/src --object-directory /z3/build')
