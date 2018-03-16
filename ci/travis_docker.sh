git clone https://github.com/afrl-rq/LmcpGen.git ../LmcpGen

(pushd docker/develop; ./01_buildImage_UxAS_build.sh && ./02_buildUxAS_WithDocker.sh && ./03_stopAndRemoveBuildContainer.sh && ./04_runUxAS_Tests.sh; popd)
(pushd docker/deploy; ./01_buildRun_Image.sh; popd)
