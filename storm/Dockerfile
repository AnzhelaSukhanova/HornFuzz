FROM archlinux:base-devel

MAINTAINER Anzhela Sukhanova <bidelya@gmail.com>

# preinstall
RUN pacman -Syu --noconfirm \
 && pacman --noconfirm -S git \
						  python \
						  python-pip \
                    	  make \
                    	  gcc \
                    	  libffi 

RUN mkdir benchmarks && mkdir LIA && mkdir ALIA && mkdir NIA

# download and prepare chc-comp21-benchmarks
RUN git clone https://github.com/chc-comp/chc-comp21-benchmarks.git --depth 1 \
 && rm -rf chc-comp21-benchmarks/LRA-TS chc-comp21-benchmarks/ADT-Nonlin \
 && gzip -d -r chc-comp21-benchmarks \
 && mv -t LIA chc-comp21-benchmarks/LIA-Lin chc-comp21-benchmarks/LIA-NonLin \
 && mv -t ALIA chc-comp21-benchmarks/LIA-Lin-Arrays chc-comp21-benchmarks/LIA-NonLin-Arrays \
 && rm -rf chc-comp21-benchmarks
 
# download and prepare spacer-benchmarks
RUN git clone https://github.com/dvvrd/spacer-benchmarks.git --depth 1 \
 && mv -t LIA spacer-benchmarks/relational && mv -t NIA spacer-benchmarks/hoice \
 && rm -rf spacer-benchmarks

RUN mv -t benchmarks LIA NIA ALIA
 
# download and edit Z3-sourses
RUN git clone https://github.com/AnzhelaSukhanova/z3.git \
 && cd z3 \
 && git checkout 99e4985 \
 && python scripts/mk_make.py --python \
 && sed -i -e 's, -D_MP_INTERNAL, -D_TRACE -D_MP_INTERNAL,g' build/config.mk
 
# install Z3
RUN cd z3/build && make -j$(nproc) && make install

# download storm-sourses
RUN git clone https://github.com/AnzhelaSukhanova/storm.git \
 && cd storm && git checkout 57cec57

# install storm
RUN cd storm && python setup.py install

# run fuzzing
CMD ["storm", "--benchmark=benchmarks", "--solverbin=", "--solver=z3"]
