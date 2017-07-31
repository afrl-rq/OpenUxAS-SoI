#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"
cd ../..
ninja -C build uxas
cd examples/08_Example_VipEscort
mkdir -p RUNDIR_VipEscort
cd RUNDIR_VipEscort
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg_VipEscort.xml

