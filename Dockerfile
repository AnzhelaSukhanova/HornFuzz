FROM archlinux

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

ENV Z3_VERSION "4.8.11"

# preinstall
RUN pacman -Syy \
 && yes | pacman -S wget \
                    git \
                    python \
                    python-pip
                       
# download and install Z3
RUN wget -qO- https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-solver-${Z3_VERSION}.0.tar.gz | tar -xz \
 && pip install z3-solver
 
# download benchmarks
RUN git clone https://github.com/dvvrd/spacer-benchmarks.git \
 && git clone https://github.com/chc-comp/chc-comp21-benchmarks.git
  
# add project-files
COPY . .

