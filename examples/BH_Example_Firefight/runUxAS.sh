#! /bin/bash
/usr/bin/osascript -e 'tell application "System Events" to tell process "Terminal" to keystroke "k" using command down'
SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"


cd ../../
if ninja -C build all ;
then 
cd $SAVE_DIR
mkdir -p RUNDIR_AssignTasks
cd RUNDIR_AssignTasks
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg.xml
else 
cd $SAVE_DIR
echo 'FAILED TO COMPILE';
fi




