#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"

mkdir -p RUNDIR_AssignTasks
cd RUNDIR_AssignTasks
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../Scenario_Live_Demo_3_cfg.xml
