#! /usr/bin/env python3

import os 
import sys
from subprocess import call 

cwdOpenUxas = '{0}'.format(os.getcwd())
lmcpGenDir = '../LmcpGen'

if os.path.isdir(lmcpGenDir):
	# build lmcpgen
	os.chdir(lmcpGenDir)
	# if not os.path.isfile('dist/LmcpGen.jar'):
	print('** building lmcpgen **')
	sys.stdout.flush()
	call('ant -q jar',shell=True)
	print( " ** finished building LmcpGen **")
	sys.stdout.flush()

	# auto-create documentation, c++, and python libraries
	os.chdir(cwdOpenUxas)
	print (" ** processing mdms **")
	sys.stdout.flush()
	cmd = 'java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -cpp -dir "src/LMCP"'
	call(cmd,shell=True)
	cmd = 'java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"'
	call(cmd,shell=True)
	cmd = 'java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -doc -dir "doc/LMCP"'
	call(cmd,shell=True)
	cmd = 'java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -py -dir "src/LMCP/py"'
	call(cmd,shell=True)
	print (" ** finished processing mdms **")
	sys.stdout.flush()

	if '-a' in  sys.argv:
		# build and install java library for AMASE
		print (" ** building java library for AMASE **")
		sys.stdout.flush()
		cmd = 'java -Xmx2048m -jar ../LmcpGen/dist/LmcpGen.jar -mdmdir "mdms" -java -dir "../OpenAMASE/OpenAMASE/lib/LMCP"'
		call(cmd,shell=True)
		os.chdir('../OpenAMASE/OpenAMASE/lib/LMCP')
		call('ant -q jar',shell=True)
		os.chdir('dist')
		call('cp lmcplib.jar ../..',shell=True)
		os.chdir('../../..')
		call('ant -q jar',shell=True)
		print (" ** finished building java library for AMASE **")
		sys.stdout.flush()
else:
	print("ERROR: LmcpGen must be present!!!")
	sys.stdout.flush()
