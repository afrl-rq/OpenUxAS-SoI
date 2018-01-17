#! /bin/bash

_SUDO=$1


# exit on non-zero return
set -e
# not passing all of the tests
#set +e

BUILD_TYPE="AUTOTOOLS"
#BUILD_TYPE="CMAKE"

LIBRARY_NAME="zeromq"
LIBRARY_FOLDER_NAME="zeromq"
SOURCE_ARCHIVE_FILE="zeromq-4.2.3.zip"
SOURCE_ARCHIVE_ADDRESS="https://github.com/zeromq/libzmq/releases/download/v4.2.3/"
SOURCE_FOLDER_NAME="zeromq-4.2.3"

echo "Making Dirs"
CWD=$(pwd)
mkdir -p ./${LIBRARY_FOLDER_NAME}
cd ./${LIBRARY_FOLDER_NAME}

if [ -f ${SOURCE_ARCHIVE_FILE} ]
then
	echo "*** "${LIBRARY_NAME}":: Archive File ("${SOURCE_ARCHIVE_FILE}") Exists, Skipping Source Fetch! ***"
else 
	echo "Fetching Source"
	wget ${SOURCE_ARCHIVE_ADDRESS}${SOURCE_ARCHIVE_FILE}
fi

echo "Unpacking..."
unzip -o ${SOURCE_ARCHIVE_FILE}

# change to the source directory
cd ${SOURCE_FOLDER_NAME}

echo "Building..."


if [ $BUILD_TYPE == CMAKE ]
then
	mkdir -p ./build
	cd ./build
	cmake ..
	make -j8; make
	echo "Installing..."
	$_SUDO make install

elif [ $BUILD_TYPE == AUTOTOOLS ]
then
	./autogen.sh
	./configure && make check
	echo "Installing..."
	$_SUDO make install
	$_SUDO ldconfig

else
	echo "!!! UNKNOWN BUILD TYPE ["${BUILD_TYPE}"]"
fi

echo "Cleaning up..."
cd ${CWD}

# uncomment the following line to remove source code
#rm -rf ./${LIBRARY_FOLDER_NAME}

echo "Finished!"

