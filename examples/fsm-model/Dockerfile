FROM python:3.4.3

ARG proxy

ENV http_proxy=$proxy
ENV https_proxy=$proxy

RUN \
   pip3 install --proxy ${proxy} pika pyqtgraph scapy-python3

RUN \
   apt-get update && \
   apt-get install -y tcpdump && \
   mv /usr/sbin/tcpdump /usr/bin/

ADD . /root/fsm

WORKDIR /root/fsm

ADD scripts/wait-for-it.sh /usr/local/bin/

RUN chmod +x /usr/local/bin/wait-for-it.sh

ENTRYPOINT [ "python3", "relay.py" ]
