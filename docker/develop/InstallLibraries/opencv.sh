OPENCV_VERSION=3.1.0
echo "Installing OpenCV $OPENCV_VERSION"
mkdir ./temp/OpenCV
cd ./temp/OpenCV
echo "Installing Dependenices"
# apt-get -y install libopencv-dev
# apt-get -y install build-essential checkinstall cmake pkg-config yasm
# apt-get -y install libtiff4-dev libjpeg-dev libjasper-dev
# apt-get -y install libavcodec-dev libavformat-dev libswscale-dev libdc1394-22-dev libxine-dev libgstreamer0.10-dev libgstreamer-plugins-base0.10-dev libv4l-dev qt*5-dev
# apt-get -y install python-dev python-numpy

 apt-get -y install build-essential
 apt-get -y install cmake git libgtk2.0-dev pkg-config libavcodec-dev libavformat-dev libswscale-dev
 apt-get -y install python-dev python-numpy libtbb2 libtbb-dev libjpeg-dev libpng-dev libtiff-dev libjasper-dev libdc1394-22-dev

echo "Downloading OpenCV $OPENCV_VERSION"
if [ -f "./opencv-$OPENCV_VERSION.zip" ]
then
	echo "File exists, skipping!"
else
	wget http://github.com/Itseez/opencv/archive/$OPENCV_VERSION.zip
	mv $OPENCV_VERSION.zip opencv-$OPENCV_VERSION.zip
fi

echo "Downloading OpenCV Contrib $OPENCV_VERSION"
if [ -f "./opencv-contrib-$OPENCV_VERSION.zip" ]
then
	echo "File exists, skipping!"
else
	wget http://github.com/Itseez/opencv_contrib/archive/$OPENCV_VERSION.zip
	mv $OPENCV_VERSION.zip opencv-contrib-$OPENCV_VERSION.zip
fi

echo "Installing OpenCV $OPENCV_VERSION"
unzip -o opencv-contrib-$OPENCV_VERSION.zip
unzip -o opencv-$OPENCV_VERSION.zip

if [ -d "./opencv-$OPENCV_VERSION" ]
then
	echo "Entering OpenCV Dir..."	
else
	echo "LAME"
	exit
fi

cd ./opencv-$OPENCV_VERSION
mkdir build
cd build
cmake -D CMAKE_BUILD_TYPE=DEBUG -D CMAKE_INSTALL_PREFIX=/usr/local -D WITH_CUDA=OFF -D OPENCV_EXTRA_MODULES_PATH=../../opencv_contrib-$OPENCV_VERSION/modules/ .. || exit "CMAKE FAILED TO CONFIGURE"
make -j4 || exit "BUILD FAILED"
 make install
 sh -c 'echo "/usr/local/lib" > /etc/ld.so.conf.d/opencv.conf'
 ldconfig

echo "Cleaning Up..."
cd ../../
 rm -rf opencv-contrib-$OPENCV_VERSION.zip
 rm -rf opencv-$OPENCV_VERSION.zip
cd ../
 rm -rf opencv-$OPENCV_VERSION
 rm -rf opencv_contrib-$OPENCV_VERSION

echo "OpenCV $OPENCV_VERSION ready to be used"
