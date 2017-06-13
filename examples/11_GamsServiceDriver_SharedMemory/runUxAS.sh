#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="$UXAS_ROOT/build_debug/uxas"

mkdir -p RUNDIR
cd RUNDIR
mkdir checkpoints
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg_GamsServiceDriver_SharedMemory.xml

