#!/usr//bin/python

import serial
import socket
import signal
import sys

def signal_handler(signal, frame):
    print 'closing socket'
    s.close()
    sys.exit()

s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.connect(("127.0.0.1", 5555))

signal.signal(signal.SIGINT, signal_handler)

numBytes = 0
with serial.Serial('/dev/ttyUSB2', 57600, timeout=100) as ser:
    while True:
        c = ser.read();
        numBytes += 1
        s.send(c)
        sys.stdout.write(format(ord(c), "x"))
        sys.stdout.flush()
        #print numBytes


