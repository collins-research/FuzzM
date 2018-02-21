FROM ubuntu:16.04

USER root

# <RC Interal Hosting>

ARG proxy=http://secproxy.rockwellcollins.com:9090

ENV http_proxy=$proxy
ENV https_proxy=$proxy

RUN \
   echo "Acquire::http::proxy \"${proxy}\";" >> /etc/apt/apt.conf && \
   echo "Acquire::https::proxy \"${proxy}\";" >> /etc/apt/apt.conf

RUN \
   apt-get update && \
   apt-get -y upgrade && \
   apt-get install -y \
   openssh-client \
   build-essential \
   git \
   unzip \
   wget \
   curl \
   vim

RUN mkdir /root/.ssh

ADD id_rsa /root/.ssh/id_rsa

RUN chmod 600 /root/.ssh/id_rsa && chmod 700 /root/.ssh && \
    touch /root/.ssh/known_hosts && ssh-keyscan eisgit.rockwellcollins.com > /root/.ssh/known_hosts

# CCANET certs

WORKDIR /root/ccanet-certs

RUN git clone git@eisgit.rockwellcollins.com:info/certs.git . && \
    cp RockwellCollinsRootCAG2.crt RockwellCollinsIssuingCA2G2.crt /usr/local/share/ca-certificates/ && \
    update-ca-certificates

# Git LFS

RUN curl -s https://packagecloud.io/install/repositories/github/git-lfs/script.deb.sh | bash && \
    apt-get install -y git-lfs

WORKDIR /root/binaries

RUN git clone git@eisgit.rockwellcollins.com:cyber/mbf/ts/binaries.git . && \
    git checkout master && git status

RUN mkdir /root/jkind && cp /root/binaries/jkind.jar /root/jkind/ && \
    mkdir /root/jfuzz && cp /root/binaries/jfuzz.jar /root/jfuzz/

# </RC Interal Hosting>

# JKind

WORKDIR /root/jkind

RUN \
   apt-get install -y \
   openjdk-8-jdk 

# GitHub
# RUN wget https://github.com/agacek/jkind/releases/download/v3.0/jkind-v3.0.zip && unzip jkind-v3.0.zip

ENV PATH=${PATH}:/root/jkind

# JFuzz

WORKDIR /root/jfuzz

RUN \
   apt-get install -y \
   python

ENV PATH=${PATH}:/root/jfuzz

# <RC Interal Hosting>

# eisgit
# RUN wget <somewhere>

# </RC Interal Hosting>

ADD wait-for-it.sh .

RUN chmod +x wait-for-it.sh

ADD gradient.lus .

CMD [ "gradient.lus" ]

ENTRYPOINT [ "java", "-jar", "jfuzz.jar", "-jfuzz" ]
