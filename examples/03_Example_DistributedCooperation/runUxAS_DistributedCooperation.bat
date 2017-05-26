setlocal

:: save the current directory
SAVE_DIR=$(pwd)

:: location of the UxAS binary (executable)
set BIN=..\..\..\build\uxas.exe

:: set the UAV ID
set UAV=1000
:: define the runinnig directory
set RUN_DIR=UAV_%UAV%
:: remove old data
rmdir /S /Q %RUN_DIR%
:: add new data directory
mkdir %RUN_DIR%
:: change to the data directory
pushd %RUN_DIR%
:: run UxAS in a separate terminal.
start cmd /k "%BIN% -cfgPath ..\cfgDistributedCooperation_%UAV%.xml"
:: change back to the original directory
popd

:: set the UAV ID
set UAV=2000
:: define the runinnig directory
set RUN_DIR=UAV_%UAV%
:: remove old data
rmdir /S /Q %RUN_DIR%
:: add new data directory
mkdir %RUN_DIR%
:: change to the data directory
pushd %RUN_DIR%
:: run UxAS in a separate terminal.
start cmd /k "%BIN% -cfgPath ..\cfgDistributedCooperation_%UAV%.xml"
:: change back to the original directory
popd
