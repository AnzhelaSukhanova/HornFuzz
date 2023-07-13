# HornFuzz
Fuzzer of the CHC solvers.

## Paper
HornFuzz: Fuzzing CHC solvers https://dl.acm.org/doi/10.1145/3593434.3593455.

## Install
Install Z3 with Python API according to the instructions given in the branch https://github.com/AnzhelaSukhanova/z3.  
You can also use the Dockerfile.

Install Eldarica: https://github.com/uuverifiers/eldarica.git.

## Seeds
Download benchmarks from
* https://github.com/dvvrd/spacer-benchmarks  
* https://github.com/chc-comp/chc-comp21-benchmarks  
* https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/main/clauses  

and place them in the root directory of this repository.  

## Use

`python src/main.py all`

By default HornFuzz tests the Spacer solver but it can also fuzz the Eldarica: use `-solver Eldarica`.  

### Seeds
* `python src/main.py <seed-file1> [<seed-file2> ...]` — you can provide both single seeds and a directory with seeds.
* `python src/main.py all` — to check all seeds from <em>spacer-benchmarks</em>, <em>chc-comp21-benchmarks</em> and <em>sv-benchmarks</em>.

### Heuristics
Add `-heuristic <heuristic>` (or `-heur`) to change default instance selection to the selection based on:  
* the probability of transitions (`transitions`);  
* the probability of states (`states`);  
* chc-difficulty (`difficulty`).  

### Other options
You can add `-options <option1> <option2>` (or `-opt`) to run fuzzer with some options.  
* `without_mutation_weights` option to allows choose mutations equiprobably.
* With `restore` option HornFuzz restores the last run and continues running.

To choose mutation groups add `-mutations <group1> <group2> ...` (or `-mut`). Available mutation groups:  
* `own`;  
* `simplifications`;  
* `<solver>_parameters`.  

