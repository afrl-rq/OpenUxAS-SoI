#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -fR ./datawork"
RM_LOG="rm -fR ./log"

BIN="$UXAS_ROOT/build_debug/uxas"

function run_uxas {
    EID="$1"
    [ ! -e RUNDIR_$EID ] && mkdir -p RUNDIR_$EID
    cd RUNDIR_$EID
    [ ! -e checkpoints ] && mkdir checkpoints
    $RM_DATAWORK
    $RM_LOG
    $BIN -cfgPath ../cfg_GamsServiceDriver_SharedMemory_$EID.xml &> out.$EID
}

run_uxas 400 &
run_uxas 500 &
wait
