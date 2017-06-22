#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"
cd ../..
ninja -C build all
cd examples/08_Example_VipEscort
mkdir -p RUNDIR_WaterwaySearch
cd RUNDIR_WaterwaySearch
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg_WaterwaySearch.xml

