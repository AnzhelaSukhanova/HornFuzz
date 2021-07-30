FROM archlinux

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

ENV Z3_VERSION "4.8.11"

# preinstall
RUN pacman -Syy \
 && yes | pacman -S wget \
                    git \
                    python \
                    python-pip \
                    make \
                    gcc
                       
# download and edit Z3-sourses
RUN git clone https://github.com/Z3Prover/z3.git \
 && cd z3 && python scripts/mk_make.py --debug \
 && sed -i -e 's, -*\\n"; CODE tout << "-*\\n,\\n,g' src/util/trace.h \
 && sed -i -e 's,<< "-* \[" << TAG << "\] ",,g' src/util/trace.h
 
# install Z3 in debug mode
RUN cd z3/build && make && make install && cd ../../

# download benchmarks
RUN git clone https://github.com/dvvrd/spacer-benchmarks.git \
 && git clone https://github.com/chc-comp/chc-comp21-benchmarks.git

# copy and install requirements
COPY requirements.txt .
RUN pip install -r requirements.txt

# add project-files
COPY . .

# run fuzzing
CMD ["python", "src/main.py", "-all"]
