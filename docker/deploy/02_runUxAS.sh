#!/bin/bash -e


if [ ! "$(docker ps -q -f name=uxas_deploy)" ]; then
    if [ "$(docker ps -aq -f status=exited -f name=uxas_deploy)" ]; then
        docker rm uxas_deploy
    fi
else
    docker stop uxas_deploy
    docker rm uxas_deploy
fi
docker run \
  -it \
  --name uxas_deploy -w="/working" \
  --mount type=bind,source="${PWD}",target="/working"  uxas_deploy \
  -cfgPath ${1-./cfg_TestUxAS.xml}
