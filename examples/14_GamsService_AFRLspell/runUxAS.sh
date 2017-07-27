#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -fR ./datawork"
RM_LOG="rm -fR ./log"

BIN="$UXAS_ROOT/build/uxas"

function run_uxas {
    EID="$1"
    rm -rf RUNDIR_$EID
    [ ! -e RUNDIR_$EID ] && mkdir -p RUNDIR_$EID
    cd RUNDIR_$EID
    [ ! -e checkpoints ] && mkdir checkpoints
    $RM_DATAWORK
    $RM_LOG
    $BIN -cfgPath ../cfg_$EID.xml
}

run_uxas 400 &> /tmp/out.400 &
run_uxas 500 &> /tmp/out.500 &
run_uxas 600 &> /tmp/out.600 &
run_uxas 700 &> /tmp/out.700 &
run_uxas 900 &> /tmp/out.900 &
run_uxas 1000 &> /tmp/out.1000 &
run_uxas 1100 &> /tmp/out.1100 &
run_uxas 1200 &> /tmp/out.1200 &
run_uxas 1300 &> /tmp/out.1300 &
run_uxas 1400 &> /tmp/out.1400 &
run_uxas 1500 &> /tmp/out.1500 &
run_uxas 800 2>&1 | tee /tmp/out.800
wait
