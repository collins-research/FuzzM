FROM maven:3.5.2-jdk-8

ARG proxy_host
ARG proxy_port

ENV proxy_host ${proxy_host}
ENV proxy_port ${proxy_port}

ADD fuzzm /root/fuzzm

WORKDIR /root/fuzzm

RUN \
      umask 000 && \
      mvn \
      -Dhttp.proxyHost=${proxy_host} -Dhttp.proxyPort=${proxy_port} \
      -Dhttps.proxyHost=${proxy_host} -Dhttps.proxyPort=${proxy_port} \
      clean compile assembly:single && \
      cp /root/fuzzm/target/fuzzm-0.0.1-SNAPSHOT-jar-with-dependencies.jar /root/fuzzm/target/fuzzm.jar && \
      cp /root/fuzzm/target/fuzzm.jar  /usr/local/bin/fuzzm.jar && \
      cp /root/fuzzm/mvn-repo/jkind/jkind/uf/jkind-uf.jar /usr/local/bin/jkind.jar

ADD scripts/wait-for-it.sh /usr/local/bin/

RUN chmod +x /usr/local/bin/wait-for-it.sh

RUN echo "java -jar /usr/local/bin/jkind.jar -jkind \"\$@\"" > /usr/local/bin/jkind && \
    chmod +x /usr/local/bin/jkind*

RUN echo "java -jar /usr/local/bin/fuzzm.jar -fuzzm \"\$@\"" > /usr/local/bin/fuzzm && \
    chmod +x /usr/local/bin/fuzzm*

CMD [ "--help" ]

ENTRYPOINT [ "fuzzm" ]
