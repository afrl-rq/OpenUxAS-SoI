#! /bin/bash

here=$PWD;

RM_DATAWORK="rm -R ./datawork"
RM_LOG="rm -R ./log"

BIN="../../../build/uxas"

echo "Cleaning RUNDIR ..."
mkdir -p RUNDIR_WaterwaySearch
cd RUNDIR_WaterwaySearch
$RM_DATAWORK
$RM_LOG

echo "Starting UxAS ..."
$BIN -runUntil 40 -cfgPath ../cfg_WaterwaySearch.xml > consoleout.txt &
cd "$here";

echo "Starting AMASE ..."
cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 20.0 --scenario "../../OpenUxAS/examples/02_Example_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

echo "Completed."

