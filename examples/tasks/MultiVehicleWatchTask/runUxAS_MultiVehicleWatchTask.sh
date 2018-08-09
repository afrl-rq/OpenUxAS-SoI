#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../../build/uxas"

mkdir -p RUNDIR_MultiVehicleWatchTask
cd RUNDIR_MultiVehicleWatchTask
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg_MultiVehicleWatchTask.xml

