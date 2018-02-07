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

echo "##### DOCKER RUN #####"
docker run -it -d \
  --name uxas_develop  -w="/UxASDev/OpenUxAS"\
  --mount type=bind,source="${PWD}/../../..",target="/UxASDev" uxas_develop


echo "##### RunLmcpGen #####"
docker exec -it uxas_develop  bash /UxASDev/OpenUxAS/RunLmcpGen.sh
echo "##### buildUxAS #####"
docker exec -it uxas_develop  bash /UxASDev/OpenUxAS/docker/develop/buildUxAS.sh
