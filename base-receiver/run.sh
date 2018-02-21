#!/bin/bash
if [ "$#" -ne 1 ]; then
    echo "Provide name of Lustre file"
    exit 1
fi

FILE=$1

cp $FILE input.lus

function cleanup 
{
    docker-compose -p $USER down
    rm -f input.lus
}

trap cleanup EXIT

docker-compose -p $USER up --abort-on-container-exit 
