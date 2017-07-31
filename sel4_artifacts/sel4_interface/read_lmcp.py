#!/usr/bin/python

import mmap
import os
import subprocess
import zmq
import json
import string
import struct
import sys
from time import sleep
sys.path.insert(0, 'py')
from lmcp import LMCPFactory

factory = LMCPFactory.LMCPFactory()
context = zmq.Context()

print 'attempting zmq socket connect...'
socket_send = context.socket(zmq.PUSH)
socket_send.connect("tcp://127.0.0.1:5557")
print 'socket connected!'

def unpackData(data):
    global factory
    buf = []
    for i in xrange(0,len(data)-1,2):
        buf.append(int(data[i:i+2], 16))
    buf = bytearray(buf)
    return factory.getObject(buf)

def sendObj(obj):
    header = str(obj.FULL_LMCP_TYPE_NAME) + '$lmcp|' + str(obj.FULL_LMCP_TYPE_NAME) + '||0|0$'
    msg = LMCPFactory.packMessage(obj, True)
    socket_send.send(header + msg)

def main():
    while True:
        p = subprocess.Popen(["./read_all"], stdout=subprocess.PIPE)
        data = p.stdout.readline()
        obj = unpackData(data)
        print obj.toString()
        sendObj(obj)
        sleep(0.1)

main()
