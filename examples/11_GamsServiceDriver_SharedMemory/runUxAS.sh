#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="$UXAS_ROOT/build_debug/uxas"

function run_uxas {
    EID="$1"
    mkdir -p RUNDIR_$EID
    cd RUNDIR_$EID
    mkdir checkpoints
    $RM_DATAWORK
    $RM_LOG
    $BIN -cfgPath ../cfg_GamsServiceDriver_SharedMemory_$EID.xml &> out.$EID
}

run_uxas 400 &
run_uxas 500 &
wait
