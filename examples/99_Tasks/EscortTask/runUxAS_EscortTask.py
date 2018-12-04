#!/usr/bin/env python
import os
import shutil
import subprocess

uxasPath = '../../../../build/uxas'
args = ["-cfgPath", "../cfg_EscortTask.xml"]

runFolder = "RUNDIR_EscortTask"

currentDir = os.path.dirname(os.path.realpath(__file__))
currentDir = os.getcwd()
runPath = os.path.join(currentDir,runFolder)

if(os.path.isdir(runPath)):
	shutil.rmtree(runPath)

os.mkdir(runPath)
os.chdir(runPath)
subprocess.call([uxasPath] + args)
