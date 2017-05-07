#! /bin/bash

#save the current directory
SAVE_DIR=$(pwd)

#location of the UxAS binary (executable)
BIN="../../../build/uxas"

#set the UAV ID
UAV=1000
#define the runinnig directory
RUN_DIR=UAV_${UAV}
#remove old data
rm -Rf ${RUN_DIR} 
#add new data directory
mkdir -p ${RUN_DIR}
# change to the data directory
cd ${RUN_DIR}
# run UxAS is a separate terminal. Note: requires "gnome-terminal"
/usr/bin/gnome-terminal -e $BIN" -cfgPath ../cfgDistributedCooperation_$UAV.xml"
# change back to the original directory
cd $SAVE_DIR

#set the UAV ID
UAV=2000
#define the runinnig directory
RUN_DIR=UAV_${UAV}
#remove old data
rm -Rf ${RUN_DIR} 
#add new data directory
mkdir -p ${RUN_DIR}
# change to the data directory
cd ${RUN_DIR}
# run UxAS is a separate terminal. Note: requires "gnome-terminal"
/usr/bin/gnome-terminal -e $BIN" -cfgPath ../cfgDistributedCooperation_$UAV.xml"
# change back to the original directory
cd $SAVE_DIR

