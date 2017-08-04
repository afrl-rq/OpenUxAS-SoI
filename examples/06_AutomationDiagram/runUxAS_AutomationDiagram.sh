#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"

mkdir -p RUNDIR_AutomationDiagram
cd RUNDIR_AutomationDiagram
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath ../AutomationDiagram_cfg.xml
