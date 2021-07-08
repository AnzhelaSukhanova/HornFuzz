FROM ubuntu

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

RUN apt-get update \

# preinstall
 && apt-get install -y g++ \
                       make \
                       git \
                       python \
                       python3 \
                       pip \
                       
# download, compile and install Z3
 && git clone https://github.com/Z3Prover/z3.git \
 && cd z3 && python scripts/mk_make.py --python \
 && cd build && make && make install && cd ../../ \
 && pip install z3-solver \
 
# download this project
 && git clone https://github.com/AnzhelaSukhanova/fuzzing_of_spacer.git \
 
# download benchmarks
 && git clone https://github.com/dvvrd/spacer-benchmarks.git \
 && git clone https://github.com/chc-comp/chc-comp21-benchmarks.git
 
