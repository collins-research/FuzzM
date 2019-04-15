FROM python

ARG proxy

ENV http_proxy=$proxy
ENV https_proxy=$proxy

RUN \
   pip3 install --upgrade pip && \
   pip3 install --proxy ${proxy} \
   pika \
   pyqtgraph

ADD . /root/relay-base

WORKDIR /root/relay-base

ADD scripts/wait-for-it.sh /usr/local/bin/

RUN chmod +x /usr/local/bin/wait-for-it.sh

ENTRYPOINT [ "python3", "print_relay.py" ]
