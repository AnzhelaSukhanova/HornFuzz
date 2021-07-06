# Fuzzing of Spacer
JetBrains Research intership project.

## Install
Install Z3 with Python API according to the instructions given here: https://github.com/Z3Prover/z3.  

## Use
* `python src/main.py <seed-file1> [<seed-file2> ...]`  
* `python src/tests.py` — to check benchmarks from _/spacer-benchmarks/relational_ that don't run for long and don't return "unknown".  
* `python src/tests.py -conn` — to check the mutation connecting seeds.
* `python src/tests.py -all` — to check all benchmarks from _/spacer-benchmarks_.  

## Seeds
Download benchmarks from https://github.com/dvvrd/spacer-benchmarks and place them in the root directory of this repository.  

