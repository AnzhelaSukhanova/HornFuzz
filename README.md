# Fuzzing of Spacer
JetBrains Research intership project.

## Install
Install Z3 with Python API according to the instructions given here: https://github.com/Z3Prover/z3.  
Or you can use the Dockerfile (`docker build -t spacer/fuzz .`).

## Use
* `python src/main.py <seed-file1> [<seed-file2> ...]`  
* `python src/main.py` — to check benchmarks from _/spacer-benchmarks/relational_ that don't run for long and don't return "unknown".  
* `python src/main.py spacer-benchmarks[/<subdir>]` — to check all benchmarks from _/spacer-benchmarks_ or _/spacer-benchmarks/\<subdirectory\>_.  
* `python src/main.py chc-comp<year>-benchmarks[/<subdir>]` — to check all benchmarks from _/chc-comp\<year\>-benchmarks_ or _/chc-comp\<year\>-benchmarks/\<subdirectory\>_.  
* `python src/main.py all` — to check all benchmarks.  

`docker run spacer/fuzz` if you are using docker.  

Add `-heuristic <priority1> <priority2> ...` (or `-heur`) to change the instance selection by the probability of transition to the selection based on:  
* the probability of states (`states`);  
* chc-difficulty (`difficulty`);  
* the number of expressions that can be mutated (`many-targets` or `few-targets`).  

## Seeds
Download benchmarks from
* https://github.com/dvvrd/spacer-benchmarks  
* https://github.com/chc-comp/chc-comp21-benchmarks (or for another year)  

and place them in the root directory of this repository.  

