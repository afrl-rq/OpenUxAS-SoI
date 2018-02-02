#!/bin/bash -e


if [ ! "$(docker ps -q -f name=uxas_run)" ]; then
    if [ "$(docker ps -aq -f status=exited -f name=uxas_run)" ]; then
        docker rm uxas_run
    fi
else
    docker stop uxas_run
    docker rm uxas_run
fi
docker run \
  -it \
  --name uxas_run -w="/working" \
  --mount type=bind,source="${PWD}",target="/working"  uxas_run \
  -cfgPath ${1-./cfg_TestUxAS.xml}
