#!/bin/sh

# Follow symbolic links to find actual JKind directory
# By David Greve
# Adapted from http://stackoverflow.com/a/7400673/984145
rawpath() { [ ! -h "$1" ] && echo "$1" || (local link="$(expr "$(command ls -ld -- "$1")" : '.*-> \(.*\)$')"; cd $(dirname $1); rawpath "$link" | sed "s|^\([^/].*\)\$|$(dirname $1)/\1|"); }

linkdir() { cd $(dirname $(rawpath $1)); pwd -P; }

SCRIPT_DIR=$(linkdir $0)

cd ${SCRIPT_DIR}/../

docker build --build-arg proxy_host=${PROXY_HOST} --build-arg proxy_port=${PROXY_PORT} -t fuzzmbuild:latest -f Dockerfile.Build .

docker create --name fuzzmmachine fuzzmbuild:latest
mkdir -p ./fuzzm/bin/
docker cp fuzzmmachine:/root/fuzzm/target/fuzzm.jar ./fuzzm/bin/fuzzm.jar
docker rm -f fuzzmmachine
