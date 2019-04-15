FROM debian:latest

ARG proxy

ENV http_proxy=$proxy
ENV https_proxy=$proxy

RUN apt-get update && \
    apt-get install -y \
    make \
    g++ \
    python3 \
    python3-pip

RUN pip3 install psutil

ADD . /root/fsm

WORKDIR  /root/fsm

RUN make

ENTRYPOINT [ "python3", "/root/fsm/monitor.py" ]
