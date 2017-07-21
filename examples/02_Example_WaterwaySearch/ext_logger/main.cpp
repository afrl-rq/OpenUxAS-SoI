// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// This file was auto-created by LmcpGen. Modifications will be overwritten.

// Utility libraries from standard c++
# ifdef LINUX
#include <arpa/inet.h>
#include <cstring> // memcpy
#endif
#include <string>
#include <cstdint>
#include <iostream>
#include <vector>

// Include appropriate socket implementation headers.
# ifdef WIN32
#include <winsock.h>
#endif
#define socklen_t int

#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"
#include "avtas/lmcp/Object.h"
#include "uxas/messages/uxnative/UXNATIVE.h"
#include "afrl/cmasi/perceive/PERCEIVE.h"
#include "uxas/messages/route/ROUTE.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "uxas/messages/task/UXTASK.h"


# ifdef LINUX
typedef int SOCKET;
int SOCKET_ERROR = -1;  // error return code for socket()
int INVALID_SOCKET = -1;  // error return code for connect()
#include <unistd.h>
#endif

bool EstablishConnection(SOCKET&, int, std::string&);

// Define the main method.
int main(int argc, char* argv[])
{
	int port = 9999;
	std::string host = "127.0.0.1";
  
	// create connection
	SOCKET connectionSocket;
	while( !EstablishConnection(connectionSocket,port,host) )
	{
		std::cout << "Could not establish connection!" << std::endl;
# ifdef LINUX
                usleep(1000000);
#endif
	}
        std::cout << "Connected!" << std::endl;

	// Create the buffer to hold incoming messages. Choosing an arbitrarily large sized
	// buffer big enough to hold any message we want to receive.
	uint32_t bufferSize = 1048576;
	char* buffer = new char[bufferSize];

	// display any messages coming across network
	avtas::lmcp::ByteBuffer buf;
	avtas::lmcp::Object* obj;
	for(;;)
	{
		int bytesReceived = recv(connectionSocket, buffer, bufferSize, 0);
                int bufferSize = bytesReceived;
                //std::cout << "Got " << bufferSize << " bytes!" << std::endl;

		if(bytesReceived <= 0)
		{
			std::cout << "Connection closed or message receive error. Reconnecting ..." << std::endl;
			while( !EstablishConnection(connectionSocket,port,host) )
			{
				std::cout << "Could not establish connection!" << std::endl;
# ifdef LINUX
                                usleep(1000000);
#endif
			}
			continue;
		}
		
		// potentially received multiple messages back-to-back
		int offsetindex = 0;
		while(bytesReceived > static_cast<int>(avtas::lmcp::Factory::HEADER_SIZE))
		{
                        while ((offsetindex+4) < bufferSize)
                        {
                           if(buffer[offsetindex+0] == 'L' &&
                              buffer[offsetindex+1] == 'M' &&
                              buffer[offsetindex+2] == 'C' &&
                              buffer[offsetindex+3] == 'P')
                           {
                              break;
                           }
                           offsetindex++;
                        }
                        bytesReceived -= offsetindex;
                        if(bytesReceived <= static_cast<int>(avtas::lmcp::Factory::HEADER_SIZE))
                           break;
			uint8_t* startByte = (uint8_t*) &buffer[offsetindex];
			uint32_t objsize = avtas::lmcp::Factory::getObjectSize(startByte, avtas::lmcp::Factory::HEADER_SIZE);
			objsize += avtas::lmcp::Factory::HEADER_SIZE + avtas::lmcp::Factory::CHECKSUM_SIZE;
				
			// process message
			buf.allocate(objsize);
                        buf.rewind();
			memcpy(buf.array(),startByte,objsize);
			bytesReceived -= objsize;
			offsetindex += objsize;
			obj = avtas::lmcp::Factory::getObject(buf);
			if(!obj)
			{
				std::cout << "Invalid message format" << std::endl;
                                std::cout << buf.toString() << std::endl;
				continue;
			}

			std::cout << "Received: " << obj->getFullLmcpTypeName() << std::endl;
			delete obj;
		}
	}
}

bool EstablishConnection(SOCKET& connectionSocket, int port, std::string& host)
{
# ifdef WIN32
	// Start Winsock
	WSAData wsaData;
	WSAStartup(MAKEWORD(1, 1), &wsaData);
#endif

	connectionSocket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
	if(connectionSocket == INVALID_SOCKET) 
		return false;
	sockaddr_in source;
	source.sin_family = AF_INET;
	source.sin_addr.s_addr = inet_addr(host.c_str());
	source.sin_port = htons((u_short)port);
	memset(&(source.sin_zero), '\0', 8);
	socklen_t source_len = sizeof(source);
	if( connect(connectionSocket, (sockaddr*)&source, source_len) == SOCKET_ERROR)
		return false;

	return true;
}
