#!/bin/bash


#!/bin/bash -e

# if [ ! "$(docker ps -q -f name=uxas_develop)" ]; then
#     if [ "$(docker ps -aq -f status=exited -f name=uxas_develop)" ]; then
#         docker rm uxas_develop
#     fi
#     # run your container
# 	docker run \
# 	  -it \
# 	  -d \
# 	  --name uxas_develop  -w="/UxASDev/OpenUxAS"\
# 	  --mount type=bind,source="${PWD}/../../..",target="/UxASDev"  steveras/uxas-build:x86_64 
# fi

docker run -it -d \
  --name uxas_develop  -w="/UxASDev/OpenUxAS"\
  --mount type=bind,source="${PWD}/../../..",target="/UxASDev" uxas_develop


docker exec -it uxas_develop  bash /UxASDev/OpenUxAS/docker/develop/runUxAS_tests.sh

docker stop uxas_develop
docker rm uxas_develop
