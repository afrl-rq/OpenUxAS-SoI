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
  --name uxas_run \
  --mount type=bind,source="${PWD}",target="/datawork"  uxas/run \
  -cfgPath datawork/cfg_TestUxAS.xml

#docker exec -it uxas_run bash /OpenUxAS/docker/develop/buildUxAS.sh

