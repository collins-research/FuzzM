#!/bin/sh

mvn deploy:deploy-file -DgroupId=jkind -DartifactId=jkind -Dversion=uf -Dpackaging=jar -Dfile=$1 -Durl=file:../fuzzm/mvn-repo
