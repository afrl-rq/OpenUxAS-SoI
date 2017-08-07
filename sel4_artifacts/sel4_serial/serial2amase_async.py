#!/usr//bin/python

import serial
import socket
import signal
import sys
import asyncore

sock_buf_size = 100000000
uart_buf_size = 1000

class Looper(asyncore.dispatcher):

    def __init__(self, host, port, ser):
        asyncore.dispatcher.__init__(self)
        self.create_socket(socket.AF_INET, socket.SOCK_STREAM)
        self.connect((host,port))
        self.ser = ser
        self.uart_buf = ""
        self.index = 0

    def handle_connect(self):
        pass

    def handle_close(self):
        self.close()

    def handle_read(self):
        data = self.recv(sock_buf_size)
        ser.write(data)

    def writable(self):
        bs = self.ser.read(uart_buf_size)
        self.uart_buf = self.uart_buf + bs
        return len(self.uart_buf) > 0

    def handle_write(self):
        sent = self.send(self.uart_buf)
        self.uart_buf = self.uart_buf[sent:]
        pass

ser = serial.Serial('/dev/ttyUSB1', 115200, timeout=1)
loop = Looper("127.0.0.1", 5555, ser)

#asyncore.loop(timeout=0.1)
asyncore.loop()
