#!/usr/bin/env python
import os
import shutil
import subprocess

app = "java"
scenarioPath = "../../OpenUxAS/examples/99_Tasks/EscortTask/Scenario_EscortTask.xml"
runAmaseArgs = ["java", "-Xmx2048m", "-splash:./data/amase_splash.png", "-classpath", "./dist/*:./lib/*",  "avtas.app.Application", "--config", "config/amase", "--scenario", scenarioPath]

currentDir = os.path.dirname(os.path.realpath(__file__))
amaseRelativePath = os.path.join("..","..","..","..","OpenAMASE","OpenAMASE")
amasePath = os.path.join(currentDir,amaseRelativePath)

os.chdir(amasePath);

subprocess.call(runAmaseArgs)


