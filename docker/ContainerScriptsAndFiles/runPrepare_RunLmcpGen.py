#! /usr/bin/env python3

import os
import sys
from subprocess import call 
import time

if len(sys.argv) > 1:
	uxasDir = sys.argv[1]
else:
	uxasDir = 'OpenUxas'
    		


timeStartAll = time.time()

internalDirectory = 'UxAS-afrl_internal'
internalPresent = False
if os.path.isdir(internalDirectory):
    print('\n##### "UxAS-afrl_internal" is present #####\n')
    sys.stdout.flush()
    internalPresent = True

timeStartPrepare = time.time()
print("\n##### START Prepare #####\n")
sys.stdout.flush()
cmd = '/usr/bin/python3 prepare'
call(cmd,shell=True)
print('\n##### FINISHED- Prepare [{0}] #####\n'.format(time.time() - timeStartPrepare))
sys.stdout.flush()

timeStartLmcpGen = time.time()

print("\n##### START RunLmcpGen (UxAS) #####\n")
sys.stdout.flush()
cmd = '/usr/bin/python3 RunLmcpGen.py'
call(cmd,shell=True)
cmd = 'mkdir -p /tmp_build/src/LMCP'
call(cmd,shell=True)
print("\n##### syncronizing LMCP source with the docker volume #####\n")
sys.stdout.flush()
cmd = 'rsync -rt  /UxASDev/{}/src/LMCP/ /tmp_build/src/LMCP/'.format(uxasDir)
print(cmd)
call(cmd,shell=True)

if internalPresent :
	print("\n##### RunLmcpGen (UxAS-afrl_internal) #####\n")
	sys.stdout.flush()
	cmd = '/usr/bin/python3 UxAS-afrl_internal/RunLmcpGen.py'
	call(cmd,shell=True)
	cmd = 'mkdir -p /tmp_build/UxAS-afrl_internal/src/LMCP/'
	call(cmd,shell=True)
	print("\n##### syncronizing afrl_internal LMCP source with the docker volume #####\n")
	cmd = 'rsync -rt  /UxASDev/{}/UxAS-afrl_internal/src/LMCP/ /tmp_build/UxAS-afrl_internal/src/LMCP/'.format(uxasDir)
	call(cmd,shell=True)

print('\n##### FINISHED LMCPGen Time [{0}] #####\n'.format(time.time() - timeStartLmcpGen))
sys.stdout.flush()

