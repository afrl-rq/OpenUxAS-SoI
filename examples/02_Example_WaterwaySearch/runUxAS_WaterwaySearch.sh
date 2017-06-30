#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"

mkdir -p RUNDIR_WaterwaySearch
cd RUNDIR_WaterwaySearch
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../cfg_WaterwaySearch.xml

