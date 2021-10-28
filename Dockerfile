FROM archlinux

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

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
 && cd z3 && python scripts/mk_make.py --python \
 && sed -i -e 's, -D_MP_INTERNAL, -D_TRACE -D_MP_INTERNAL,g' build/config.mk \ 
 && sed -i -e 's,<< "-* \[" << TAG << "\] ",,g' src/util/trace.h \
 && sed -i -e 's, -*\\n,\\n,g' src/util/trace.h \
 && sed -i -e 's,--*\\n,,g' src/util/trace.h \
 && sed -i -e ':a;N;$!ba;s,#ifdef _*EMSCRIPTEN_*\n#define NO\_Z3\_DEBUGGER\n#endif,#define NO\_Z3\_DEBUGGER,g' src/util/debug.h \
 && sed -i -e 's, exit(ERR_UNREACHABLE);,,g' src/util/debug.h
 
# install Z3
RUN cd z3/build && make && make install

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
RUN sed -i -e 's|to_symbol(logic|to_symbol(logic, ctx=ctx|g' usr/lib/python3.9/site-packages/z3/z3.py
CMD ["python", "src/main.py", "all"]
