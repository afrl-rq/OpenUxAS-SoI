#! /usr/bin/env python3

import os
from subprocess import call 
import platform
import shutil
import time

dockerComposeFilename = 'docker-compose-coop.yml'
containerLocalHostAddressOrg = '127.0.0.1'

def AddVehicle(composeFile,containerLocalHostAddress,vehicleId,lastNetworkOctet,lastEndpointOctet,gossipBind,amasePort,configurationFile,tadPort1,tadPort2,tadPort3):
	# backup old run directory and create new one.

	runDir = 'Vehicle_{}'.format(vehicleId)
	if os.path.isdir(runDir):
		shutil.rmtree(runDir)
	os.mkdir(runDir)

	# fix container's host address and add gossip addresses
	fin = open(configurationFile, 'r')
	stringFileIn = fin.read()
	# fix container's host address in the config file
	stringFileIn = stringFileIn.replace(containerLocalHostAddressOrg,containerLocalHostAddress)
	# change zyre config to use gossip
	zyreEntryOrg = '<Bridge Type="LmcpObjectNetworkZeroMqZyreBridge" NetworkDevice="en0">'
	zyreEntryNew = '<Bridge Type="LmcpObjectNetworkZeroMqZyreBridge" ZyreEndpoint="tcp://172.28.6.{0}:39801" GossipEndpoint="tcp://172.28.6.{1}:39810" GossipBind="{2}">'.format(lastNetworkOctet,lastEndpointOctet,gossipBind)
	stringFileIn = stringFileIn.replace(zyreEntryOrg,zyreEntryNew)
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
	if tadPort1 and tadPort2:
		composeFile.write('   - "{1}:{1}"\n'.format(containerLocalHostAddress,tadPort1))
		composeFile.write('   - "{1}:{1}"\n'.format(containerLocalHostAddress,tadPort2))
	if tadPort3:
		composeFile.write('   - "{1}:{0}::{1}"\n'.format(containerLocalHostAddress,tadPort3))
	composeFile.write('  volumes:\n')
	composeFile.write('   - type: "bind"\n')
	composeFile.write('     source: "./"\n')
	composeFile.write('     target: "/working"\n')
	composeFile.write('  networks:\n')
	composeFile.write('   uxas_net_coop:\n')
	composeFile.write('    ipv4_address: "172.28.6.{0}"\n'.format(lastNetworkOctet))
	composeFile.write('  working_dir: /working/{0}\n'.format(runDir))
	composeFile.write('  entrypoint: ["/uxas","-cfgPath", "{0}"]\n'.format(cfgFileNew))
	composeFile.write('\n')

def BuildDockerComposeFile(dockerComposeFilename,containerLocalHostAddress):
	composeFile = open(dockerComposeFilename,'w')
	composeFile.write("version: '3.2'\n\n")
	composeFile.write('services:\n')

	vehicleId = 1000
	lastNetworkOctet = 10
	lastEndpointOctet = 10
	amasePort = 7056
	cfgFile = 'cfgDistributedCooperation_1000.xml'
	gossipBind = 'true'
	AddVehicle(composeFile,containerLocalHostAddress,vehicleId,lastNetworkOctet,lastEndpointOctet,gossipBind,amasePort,cfgFile,[],[],[])

	vehicleId = 2000
	lastNetworkOctet = 20
	lastEndpointOctet = lastEndpointOctet
	amasePort = 7057
	cfgFile = 'cfgDistributedCooperation_2000.xml'
	gossipBind = 'false'
	AddVehicle(composeFile,containerLocalHostAddress,vehicleId,lastNetworkOctet,lastEndpointOctet,gossipBind,amasePort,cfgFile,5560,5561,9876)

	composeFile.write('networks:\n')
	composeFile.write(' default:\n')
	composeFile.write('  external:\n')
	composeFile.write('    name: bridge\n')
	composeFile.write(' uxas_net_coop:\n')
	composeFile.write('  driver: bridge\n')
	composeFile.write('  ipam:\n')
	composeFile.write('   driver: default\n')
	composeFile.write('   config:\n')
	composeFile.write('   -\n')
	composeFile.write('     subnet: 172.28.6.0/24\n')
	composeFile.write('\n')
	composeFile.close()


def main():

	osType = platform.system()
	containerLocalHostAddress = containerLocalHostAddressOrg  # NOTE: see the file: `OpenUxAS/docker/00c_README_OS_Differences.md`
	if osType =='Linux':
		pass
	elif osType =='Darwin':
		containerLocalHostAddress = '192.168.65.2'
		networkCfg = ''
	elif osType =='Windows':
		containerLocalHostAddress = '10.0.75.1'
		networkCfg = ''

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
