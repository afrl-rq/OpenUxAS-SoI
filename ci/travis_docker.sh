git clone https://github.com/afrl-rq/LmcpGen.git ../LmcpGen

(pushd docker/develop; python3 ./01_construct_uxas-build.py && python3  ./02_PrepareAndBuildLmcp.py && python3  ./03_BuildDeploy_UxAS.py && python3  ./05_Run_UxAS-Tests.py; popd)
