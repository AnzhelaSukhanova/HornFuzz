# Fuzzing of Spacer
JetBrains Research intership project.

## Install
Install Z3 with Python API according to the instructions given here: https://github.com/Z3Prover/z3.  
Or you can use the Dockerfile (`docker build -t spacer/fuzz .`).

## Use
* `python src/main.py <seed-file1> [<seed-file2> ...]`  
* `python src/tests.py` — to check benchmarks from _/spacer-benchmarks/relational_ that don't run for long and don't return "unknown".  
* `python src/tests.py -conn` — to check the mutation connecting seeds.  
* `python src/tests.py spacer-benchmarks[/<subdir>]` — to check all benchmarks from _/spacer-benchmarks_ or _/spacer-benchmarks/\<subdirectory\>_.  
* `python src/tests.py chc-comp<year>-benchmarks[/<subdir>]` — to check all benchmarks from _/chc-comp\<year\>-benchmarks_ or _/chc-comp\<year\>-benchmarks/\<subdirectory\>_.  

`docker run spacer/fuzz python ...` if you are using docker.

## Seeds
Download benchmarks from
* https://github.com/dvvrd/spacer-benchmarks  
* https://github.com/chc-comp/chc-comp21-benchmarks (or for another year)  

and place them in the root directory of this repository.  

