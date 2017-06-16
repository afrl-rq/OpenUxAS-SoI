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
mkdir -p log
$BIN -runUntil 43 -cfgPath ../cfg_WaterwaySearch.xml > log/consoleout.txt &
cd "$here";

sleep 3

echo "Starting AMASE ..."
cd ../../../OpenAMASE/OpenAMASE;
java -Xmx2048m -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase_headless --sim_rate 20.0 --scenario "../../OpenUxAS/examples/02_Example_WaterwaySearch/Scenario_WaterwaySearch.xml";
cd "$here";

echo "Completed."

