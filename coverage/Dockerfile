FROM ubuntu:latest

ENV CC=clang
ENV CXX: clang++
ENV BUILD_TYPE=Debug
ENV CMAKE_GENERATOR=Ninja
ENV COV_DETAILS_PATH=/cov-details

ENV TZ=Europe/Moscow
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt-get update -y \
  && apt-get install -y git gcovr ninja-build llvm clang cmake

RUN git clone https://github.com/AnzhelaSukhanova/z3.git \
 && cd z3 \
 && git checkout ddd611d

# fiz z3 repo
RUN rm /z3/src/util/z3_version.h

# Configure CMake Z3
RUN cd z3 && CFLAGS=="--coverage" CXXFLAGS="--coverage" LDFLAGS="-lgcov" cmake -B /z3/build -DCMAKE_BUILD_TYPE=$BUILD_TYPE -DCMAKE_INSTALL_PREFIX=./install

# Build Z3
RUN cmake --build /z3/build --target install --config $BUILD_TYPE

RUN pip install tqdm
RUN mkdir /queries
RUN mkdir /coverage/cov-details

ADD run_coverage_tests.py .
ADD gather_coverage.py .

CMD python run_coverage_tests.py; python gather_coverage.py
