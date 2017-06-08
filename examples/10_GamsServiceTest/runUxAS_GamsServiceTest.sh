#! /bin/bash

SAVE_DIR=$(pwd)

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build_debug/uxas"

mkdir -p RUNDIR_GamsServiceTest
cd RUNDIR_GamsServiceTest
mkdir checkpoints
$RM_DATAWORK
$RM_LOG
$BIN -cfgPath $HOME/projects/OpenUxAS/OpenUxAS/OpenUxAS/examples/10_GamsServiceTest/cfg_GamsServiceTest.xml

