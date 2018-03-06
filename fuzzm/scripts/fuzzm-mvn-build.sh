#!/bin/sh

# Follow symbolic links to find actual JKind directory
# By David Greve
# Adapted from http://stackoverflow.com/a/7400673/984145
rawpath() { [ ! -h "$1" ] && echo "$1" || (local link="$(expr "$(command ls -ld -- "$1")" : '.*-> \(.*\)$')"; cd $(dirname $1); rawpath "$link" | sed "s|^\([^/].*\)\$|$(dirname $1)/\1|"); }

linkdir() { cd $(dirname $(rawpath $1)); pwd -P; }

SCRIPT_DIR=$(linkdir $0)

pomdir() { cd ${SCRIPT_DIR}/../fuzzm/; pwd -P; }

cd $(pomdir)

mvn \
-Dhttp.proxyHost=${PROXY_HOST} \
-Dhttp.proxyPort=${PROXY_PORT} \
-Dhttps.proxyHost=${PROXY_HOST} \
-Dhttps.proxyPort=${PROXY_PORT} \
clean compile assembly:single

mkdir -p ./bin

mv ./target/fuzzm*MAVEN*.jar ./bin/fuzzm.jar
