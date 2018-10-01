#! /usr/bin/env python3

import os
from subprocess import call 
import platform
import shutil

dockerComposeFilename = 'docker-compose-waterway.yml'
containerLocalHostAddressOrg = '127.0.0.1'

def AddVehicle(composeFile,containerLocalHostAddress,vehicleId,amasePort,configurationFile):

	# add a sub-directory to run in
	runDir = 'Vehicle_{}'.format(vehicleId)
	if os.path.isdir(runDir):
		shutil.rmtree(runDir)
	os.mkdir(runDir)

	# fix container's host address
	fin = open(configurationFile, 'r')
	stringFileIn = fin.read()
	# fix container's host address in the config file
	stringFileIn = stringFileIn.replace(containerLocalHostAddressOrg,containerLocalHostAddress)
	#save the changes to a new file
	cfgFileNew = '{0}_new.xml'.format(configurationFile)
	fout = open('{0}/{1}'.format(runDir,cfgFileNew), 'w')
	fout.write(stringFileIn)
	fout.close()

	# build new docker service (new container)
	composeFile.write(' V{0}:\n'.format(vehicleId))
	composeFile.write('  image: "uxas/uxas-deploy:x86_64"\n')
	composeFile.write('  ports:\n')
	composeFile.write('   - "{1}:{0}::{1}"\n'.format(containerLocalHostAddress,amasePort))
	composeFile.write('  volumes:\n')
	composeFile.write('   - type: "bind"\n')
	composeFile.write('     source: "./"\n')
	composeFile.write('     target: "/working"\n')
	composeFile.write('  working_dir: /working/{0}\n'.format(runDir))
	composeFile.write('  entrypoint: ["/uxas","-cfgPath", "{0}"]\n'.format(cfgFileNew))
	composeFile.write('\n')

def BuildDockerComposeFile(dockerComposeFilename,containerLocalHostAddress):
	composeFile = open(dockerComposeFilename,'w')
	composeFile.write("version: '3.2'\n\n")
	composeFile.write('services:\n')

	vehicleId = 100
	amasePort = 5555
	cfgFile = 'cfg_WaterwaySearch.xml'
	AddVehicle(composeFile,containerLocalHostAddress,vehicleId,amasePort,cfgFile)

	composeFile.write('\n')
	composeFile.close()


def main():
    
	osType = platform.system()
	containerLocalHostAddress = containerLocalHostAddressOrg  # NOTE: see the file: `OpenUxAS/docker/00c_README_OS_Differences.md`
	if osType =='Linux':
		pass
	elif osType =='Darwin':
		containerLocalHostAddress = '192.168.65.2'
	elif osType =='Windows':
		containerLocalHostAddress = '10.0.75.1'

	BuildDockerComposeFile(dockerComposeFilename,containerLocalHostAddress)

	print('\n** close any running containers **')
	cmd = 'docker-compose -f {} kill'.format(dockerComposeFilename)
	print('{}\n'.format(cmd))
	call(cmd,shell=True)

	print('\n** start new containers **')
	cmd = 'docker-compose -f {} up'.format(dockerComposeFilename)
	print('{}\n'.format(cmd))
	call(cmd,shell=True)

 
if __name__ == '__main__':
	main()
