/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   STaliroCommInterface.h
 * Author: etuncali
 *
 * Created on June 19, 2017, 10:21 AM
 */

#ifndef STALIROCOMMINTERFACE_H
#define STALIROCOMMINTERFACE_H

#include <stdio.h>
#include <sys/socket.h>
#include <stdlib.h>
#include <netinet/in.h>
#include <errno.h>
#include <string.h>
#include <iostream>
#include <vector>
#include <map>
#include "UxAS_Log.h"

#define STALIRO_SEND_BUFFER_SIZE 512
#define STALIRO_HEART_BEAT_PERIOD_MS 10000

namespace testgeneration
{
    namespace staliro
    {
        class c_CommunicationInterface final
        {
        public:
            static c_CommunicationInterface* getInstance();
            
            virtual ~c_CommunicationInterface(){};
            
            void createServer(int serverPort);
            bool acceptConnection();
            void closeConnection();
            bool receiveCommands();
            bool receiveTrajectoryRequest();
            bool sendTrajInfo(uint32_t numColumns, uint32_t numRows);
            bool sendTrajData(size_t length, void* data);
            bool receiveAck();
            void readInitCond();
            void readTask();
            bool sendHeartBeat(int64_t curTime);
            void setFileFieldMapPtr(std::map<std::string, 
                    std::map<std::string,
                    std::string> >* mapPtr);
            void setTaskFileFieldMapPtr(std::map<std::string, 
                    std::map<std::string,
                    std::vector<double>> >* mapPtr);
            void addTrajectoryRow(uint32_t curRowNumber, 
                    uint32_t totalNumOfRows, 
                    uint32_t numElementsInRow, 
                    double time,
                    double * row);
            bool isTrajectoryRequested();
            int64_t getMaxSimulationDuration();

        protected:
            int serverSocket;
            int clientSocket;
            bool isConnected;
            struct sockaddr_in serverAddress;
            std::map<std::string, std::map<std::string, std::string> >* fileFieldMapPtr;
            std::map<std::string, std::map<std::string, std::vector<double>> >* taskFileFieldMapPtr;
            std::string readFieldString();
            std::vector<double> readFieldArray();
            bool sendAck(uint32_t ackReply);
            void resetSendBuffer();
            bool addToSendBuffer(void * data, size_t dataLength);
            bool sendData();
            int64_t readMaxSimulationDuration();
            uint8_t sendBuffer[STALIRO_SEND_BUFFER_SIZE];
            void * sendBufferFillPtr;
            size_t sendBufferSize;
            double trajectoryBuffer[(STALIRO_SEND_BUFFER_SIZE-8)/8];
            void *trajectoryBufferPtr;
            bool trajectoryRequested;
            int64_t m_maxSimulationDuration_ms;
            int64_t m_lastHeartBeatTime_ms;
            
        private:
            /** \brief Public, direct construction not permitted (singleton pattern) */
            c_CommunicationInterface();
    
            /** \brief Copy construction not permitted */
            c_CommunicationInterface(c_CommunicationInterface const&) = delete;

            /** \brief Copy assignment operation not permitted */
            void operator=(c_CommunicationInterface const&) = delete;
            
            static c_CommunicationInterface* s_instance;
        };
        
        enum staliroCommand
        {
            STALIRO_INIT_COND = 1,
            STALIRO_INPUT_SIG = 2,
            STALIRO_START_SIM = 3,
            STALIRO_ACK = 4,
            STALIRO_NAK = 5,
            STALIRO_TASK = 6,
            STALIRO_TRAJ_INFO = 10,
            STALIRO_TRAJ_DATA = 11,
            STALIRO_REQUEST_TRAJECTORY = 12,
            STALIRO_HEART_BEAT = 20
        };
        struct s_StaliroMessage
        {
            int messageLength;
            std::string message;
        };
    }
}

#endif /* STALIROCOMMINTERFACE_H */

