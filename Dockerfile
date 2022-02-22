FROM archlinux

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

# preinstall
RUN pacman -Syy \
 && pacman --noconfirm -Suy \
 && pacman --noconfirm -S wget \
                    git \
                    python \
                    python-pip \
                    make \
                    gcc \
                    libffi \
                    scala \
 && 1 | pacman --noconfirm -S sbt

# install Eldarica
RUN git clone https://github.com/uuverifiers/eldarica.git --depth 1 && cd eldarica && sbt assembly

# download seeds
RUN git clone https://github.com/dvvrd/spacer-benchmarks.git --depth 1 \
 && git clone https://github.com/chc-comp/chc-comp21-benchmarks.git --depth 1 \
 && git clone https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks.git --depth 1
 
# prepare seeds
RUN mv sv-benchmarks/clauses sv-benchmarks-clauses \
 && rm -rf sv-benchmarks sv-benchmarks-clauses/QALIA sv-benchmarks-clauses/BOOL\
 && rm -rf chc-comp21-benchmarks/LRA-TS chc-comp21-benchmarks/ADT-Nonlin \
 && gzip -d -r chc-comp21-benchmarks

# copy and install requirements
COPY requirements.txt .
RUN pip install -r requirements.txt
                       
# download and edit Z3-sourses
RUN git clone https://github.com/AnzhelaSukhanova/z3.git \
 && cd z3 \
 && git checkout 21bdebe \
 && python scripts/mk_make.py --python \
 && sed -i -e 's, -D_MP_INTERNAL, -D_TRACE -D_MP_INTERNAL,g' build/config.mk
 
# install Z3
RUN cd z3/build && make -j$(nproc) && make install

# add project-files
ADD src src
ADD seed_info seed_info
ADD false_formulas false_formulas
ADD exclude_seed.json .

# run fuzzing
CMD ["python", "src/main.py", "all", "-heuristics", "transitions"]
