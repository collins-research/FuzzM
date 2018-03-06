FROM ubuntu:18.04

ARG proxy

ENV http_proxy=$proxy
ENV https_proxy=$proxy
ENV LD_LIBRARY_PATH=/usr/local/lib

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update && \
    apt-get install -y \
    git \
    gdb \
    autoconf \
    automake \
    libtool \
    make \
    vim \
    wget \ 
    binutils-dev \
    clang \
    pkg-config \
    libunwind8-dev \
    valgrind \
    afl \
    afl-clang \
    afl-cov

WORKDIR /tmp

RUN git clone --depth=1 https://github.com/google/honggfuzz.git && \
    cd honggfuzz && \
    make -j && \
    cp honggfuzz -v /bin && \
    cp -v libhfuzz/*.a /usr/local/lib && \
    cp -v libhfcommon/*.a /usr/local/lib && \
    cp -v hfuzz_cc/* /bin

ADD . /root/fuzz-off

WORKDIR /root/fuzz-off

RUN make fuzz
