#!/bin/bash -e



cd Image
mkdir -p app
# copy the uxas executable to the local directory structure
if [ -e "../../../build/uxas" ] ; then
	cp ../../../build/uxas app/uxas;
else
	echo "OpenUxAS/build/uxas does not exist. Exiting!";
	exit 1;
fi

# build the image
docker build -f Dockerfile.UxAS_run -t uxas_run .
