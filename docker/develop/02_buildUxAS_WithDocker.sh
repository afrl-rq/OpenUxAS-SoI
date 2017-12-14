#!/bin/bash -e


if [ ! "$(docker ps -q -f name=uxas_build)" ]; then
    if [ "$(docker ps -aq -f status=exited -f name=uxas_build)" ]; then
        docker rm uxas_build
    fi
    # run your container
	docker run \
	  -it \
	  -d \
	  --name uxas_build \
	  --mount type=bind,source="${PWD}/../../../OpenUxAS",target="/OpenUxAS"  uxas/build 
fi

docker exec -it uxas_build bash /OpenUxAS/docker/develop/buildUxAS.sh

