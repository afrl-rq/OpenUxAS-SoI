set -ev

if [[ "$BUILD_FLAVOR" == "linux_docker" ]]; then
    source ci/travis_docker.sh;
elif [[ "$BUILD_FLAVOR" == "linux_native" ]]; then
    source ci/travis_linux.sh;
elif [[ "$BUILD_FLAVOR" == "osx_native" ]]; then
    source ci/travis_osx.sh;
else
    echo "Error: unexpected Travis build flavor: $BUILD_FLAVOR";
    false;
fi
