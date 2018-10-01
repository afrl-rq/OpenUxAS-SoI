#! /usr/bin/env python3

import os
from subprocess import call 

scenarioFile = 'Scenario_DistributedCooperation.xml'
amaseDirectory = '../../../OpenAMASE/OpenAMASE'

cmd = 'java -Xmx2048m -splash:./data/amase_splash.png -classpath ./dist/*:./lib/*  avtas.app.Application --config config/amase --scenario "{0}/{1}"'.format(os.getcwd(),scenarioFile)

os.chdir(amaseDirectory)
call(cmd,shell=True)

