#! /bin/bash

_SUDO=$1


# exit on non-zero return
set -e


#BUILD_TYPE="AUTOCONFIG"
#BUILD_TYPE="AUTOTOOLS"
BUILD_TYPE="BOOST"
#BUILD_TYPE="CMAKE"
#BUILD_TYPE="MAKE"

LIBRARY_NAME="boost"
LIBRARY_FOLDER_NAME="boost"
SOURCE_ARCHIVE_FILE="boost_1_67_0.tar.bz2"
SOURCE_ARCHIVE_ADDRESS="https://dl.bintray.com/boostorg/release/1.67.0/source/"
SOURCE_FOLDER_NAME="boost_1_67_0"

ARCHIVE_COMMAND="tar xjf "

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
#unzip -o ${SOURCE_ARCHIVE_FILE}
${ARCHIVE_COMMAND} ${SOURCE_ARCHIVE_FILE}

# change to the source directory
cd ${SOURCE_FOLDER_NAME}

echo "Building..."


if [ $BUILD_TYPE == AUTOCONFIG ]
then
	chmod +x configure
	./configure --prefix=/usr/local
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

elif [ $BUILD_TYPE == BOOST ]
then
	#./bootstrap.sh --prefix=/usr/local --with-libraries=all
	#./bootstrap.sh --prefix=/usr/local cxxflags="-stdlib=libc++ -std=c++11 -DLINUX" linkflags="-stdlib=libc++ -std=c++11 -DLINUX"  --with-libraries=all
	./bootstrap.sh --prefix=/usr/local cxxflags="-stdlib=libc++ -std=c++11 -DLINUX" linkflags="-stdlib=libc++ -std=c++11 -DLINUX"  --with-libraries=filesystem,regex,system
 
	$_SUDO ./b2 install
	$_SUDO ldconfig

elif [ $BUILD_TYPE == CMAKE ]
then
	mkdir -p ./build
	cd ./build
	cmake ..
	make -j8; make
	echo "Installing..."
	$_SUDO make install

elif [ $BUILD_TYPE == MAKE ]
then
	make
	$_SUDO make install


else
	echo "!!! UNKNOWN BUILD TYPE ["${BUILD_TYPE}"]"
fi

echo "Cleaning up..."
cd ${CWD}

# uncomment the following line to remove source code
#$_SUDO rm -rf ./${LIBRARY_FOLDER_NAME}

echo "Finished!"



