git clone https://github.com/afrl-rq/LmcpGen.git ../LmcpGen

(pushd docker; python3 ./99_construct_uxas-build.py && python3  ./01_PrepareAndBuildLmcp.py && python3  ./02_BuildDeploy_UxAS.py && python3  ./04_Run_UxAS-Tests.py; popd)
