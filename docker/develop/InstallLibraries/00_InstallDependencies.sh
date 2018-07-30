echo "Installing Basic Dependencies for UxAS..."

# exit on non-zero return
set -e

# set whether or not "sudo" is required
SUDO=sudo
if [ "$1" = "NO_SUDO" ]
then
	_SUDO=
fi

INSTALL_CWD=$(pwd)

mkdir -p ./temp
cd ./temp

 bash ../boost.sh $_SUDO
 # bash ../zeromq.sh $_SUDO
 # bash ../czmq.sh $_SUDO
 bash ../zyre.sh $_SUDO
 bash ../cppzmq.sh $_SUDO
 # bash ../sqlite3.sh $_SUDO
 bash ../sqlitecpp.sh $_SUDO
 # bash ../zlib.sh $_SUDO
 # bash ../minizip.sh $_SUDO
 # bash ../geographiclib.sh $_SUDO
 # bash ../googletest.sh $_SUDO
 # bash ../gdal.sh $_SUDO

 #../opencv.sh $_SUDO
 #../ffmpeg.sh $_SUDO

cd $INSTALL_CWD
$_SUDO rm -rf ./temp

echo "Finished installing  Basic UxAS dependencies!"
