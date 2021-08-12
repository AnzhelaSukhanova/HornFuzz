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
 && cd z3 && python scripts/mk_make.py \
 && sed -i -e 's, -D_MP_INTERNAL, -D_TRACE -D_MP_INTERNAL,g' build/config.mk \ 
 && sed -i -e 's, -*\\n"; CODE tout << "-*\\n,\\n,g' src/util/trace.h \
 && sed -i -e 's,<< "-* \[" << TAG << "\] ",,g' src/util/trace.h \
 && sed -i -e ':a;N;$!ba;s,#ifdef _*EMSCRIPTEN_*\n#define NO\_Z3\_DEBUGGER\n#endif,#define NO\_Z3\_DEBUGGER,g' src/util/debug.h
 
# install Z3 in debug mode
RUN cd z3/build && make && make install && cd ../../

# download benchmarks
RUN git clone https://github.com/dvvrd/spacer-benchmarks.git \
 && git clone https://github.com/chc-comp/chc-comp21-benchmarks.git \
 && rm -rf chc-comp21-benchmarks/LRA-TS && rm -rf chc-comp21-benchmarks/ADT-Nonlin \
 && gzip -d -r chc-comp21-benchmarks

# copy and install requirements
COPY requirements.txt .
RUN pip install -r requirements.txt \
 && ln -s /usr/lib/libz3.so libz3.so

# add project-files
ADD src src
ADD exclude_seed.json .

# run fuzzing
CMD ["python", "src/main.py", "all"]
