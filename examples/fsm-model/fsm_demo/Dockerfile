FROM debian:jessie

ARG proxy

ENV http_proxy=${proxy}
ENV https_proxy=${proxy}

RUN apt-get update && \
    apt-get install -y \
    make \
    g++

ADD . /root/fsm

WORKDIR  /root/fsm

RUN make

ENTRYPOINT [ "/root/fsm/fsm" ]
