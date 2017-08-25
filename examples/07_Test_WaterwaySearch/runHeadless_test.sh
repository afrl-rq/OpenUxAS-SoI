#! /bin/bash

here=$PWD;

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build_debug/uxas"

echo "Cleaning RUNDIR ..."
mkdir -p RUNDIR_WaterwaySearch
cd RUNDIR_WaterwaySearch
$RM_DATAWORK
$RM_LOG

echo "Starting AMASE ..."
cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 1.0 --scenario "../../OpenUxAS/examples/06_Test_WaterwaySearch/Scenario_WaterwaySearch.xml" &
cd "$here";


echo "Starting UxAS ..."
mkdir -p log
$BIN -cfgPath ../cfg_WaterwaySearch.xml > log/consoleout.txt &
cd "$here";

echo "Completed."

