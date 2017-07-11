#include "STaliroCommInterface.h"

namespace testgeneration
{
    namespace staliro
    {
        c_CommunicationInterface* c_CommunicationInterface::s_instance = nullptr;
        
        c_CommunicationInterface* c_CommunicationInterface::getInstance()
        {
            // first time/one time creation
            if (!c_CommunicationInterface::s_instance)
            {
                s_instance = new c_CommunicationInterface();
            }

            return s_instance;
        };

        
        c_CommunicationInterface::c_CommunicationInterface()
        {
            sendBufferFillPtr = (void *)sendBuffer;
            sendBufferSize = 0;
            isConnected = false;
            trajectoryRequested = false;
            m_lastHeartBeatTime_ms = 0;
        }
        
        void c_CommunicationInterface::createServer(int serverPort)
        {
            if (!isConnected)
            {
                if ((serverSocket = socket(AF_INET, SOCK_STREAM, 0)) > 0)
                {
                    int opt = 1;
                    if (setsockopt(serverSocket, SOL_SOCKET, SO_REUSEADDR | SO_REUSEPORT, 
                            &opt, 
                            sizeof(opt)) == 0)
                    {
                        serverAddress.sin_family = AF_INET;
                        serverAddress.sin_port = htons(serverPort);
                        serverAddress.sin_addr.s_addr = INADDR_ANY;
                        if (bind(serverSocket, 
                                (struct sockaddr *)&serverAddress, 
                                sizeof(serverAddress)) >= 0)
                        {
                            if (listen(serverSocket, 3) < 0)
                            {
                                UXAS_LOG_ERROR(
                                        "staliro::CommunicationInterface::Could not listen socket!");
                            }
                        }
                        else
                        {
                            UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not bind socket!");
                        }
                    }
                    else
                    {
                        UXAS_LOG_ERROR(
                                "staliro::CommunicationInterface::Could not set socket options!");
                    }
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not create socket!");
                }
            }
        }
        
        bool c_CommunicationInterface::acceptConnection()
        {
            int addrlen = sizeof(serverAddress);
            
            if ((clientSocket = accept(serverSocket, 
                    (struct sockaddr *)&serverAddress, 
                    (socklen_t*)&addrlen)) >= 0)
            {
                isConnected = true;
                shutdown(serverSocket, SHUT_RDWR);
            }
            else
            {
                UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not accept connection!");
                isConnected = false;
            }
            
            return isConnected;
        }
        
        void c_CommunicationInterface::closeConnection()
        {
            //shutdown(clientSocket, SHUT_RDWR);
            //isConnected = false;
        }
        
        void c_CommunicationInterface::resetSendBuffer()
        {
            sendBufferFillPtr = (void *) sendBuffer;
            sendBufferSize = 0;
        }
        
        bool c_CommunicationInterface::addToSendBuffer(void * data, 
                size_t dataLength)
        {
            bool retCode = true;
            
            if (((uint8_t *) sendBufferFillPtr - &sendBuffer[0] + dataLength) <= 
                    STALIRO_SEND_BUFFER_SIZE)
            {
                memcpy(sendBufferFillPtr, (const void *) data, dataLength);
                sendBufferSize += dataLength;
                sendBufferFillPtr = (uint8_t *)sendBufferFillPtr + dataLength;
            }
            else
            {
                retCode = false;
            }
            return retCode;
        }
        
        bool c_CommunicationInterface::sendData()
        {
            int retCode = true;
            void * curBufferPtr = (void *) sendBuffer;
            size_t totalSentSize = 0;
            ssize_t curSentSize;
            
            while (totalSentSize < sendBufferSize)
            {
                curSentSize = send(clientSocket, curBufferPtr, sendBufferSize - totalSentSize, 0);
                if (curSentSize >= 0)
                {
                    totalSentSize += (size_t) curSentSize;
                    curBufferPtr = (uint8_t *) curBufferPtr + (int) curSentSize;
                }
                else
                {
                    retCode = false;
                }
            }
            return retCode;
        }
        
        bool staliro::c_CommunicationInterface::sendAck(uint32_t ackReply)
        {
            resetSendBuffer();
            addToSendBuffer((void *) &ackReply, sizeof(ackReply));
            return sendData();
        }
        
        bool c_CommunicationInterface::receiveAck()
        {
            uint32_t ackMsg = 0;
            uint readCnt = 0;
            uint tmpReadCnt = 0;
            bool ackReceived = false;
            
            // Read ackMsg
            while (readCnt < sizeof(ackMsg))
            {
                tmpReadCnt = recv( clientSocket, &ackMsg + readCnt, sizeof(ackMsg) - readCnt, 0);
                if (tmpReadCnt >= 0)
                {
                    readCnt += tmpReadCnt;
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read Ack!");
                    ackMsg = 0;
                    break;
                }
            }
            if (ackMsg == testgeneration::staliro::STALIRO_ACK)
            {
                ackReceived = true;
            }
            else
            {
                ackReceived = false;
            }
            return ackReceived;
        }
        
        bool c_CommunicationInterface::receiveCommands() 
        {
            uint32_t cmd = 0;
            uint8_t ackReply = 0;
            uint readCnt = 0;
            uint tmpReadCnt = 0;
            bool retCode = true;
            bool allReceived = false;
            
            while (!allReceived)
            {
                while (readCnt < sizeof(cmd))
                {
                    tmpReadCnt = recv( clientSocket, &cmd+readCnt, sizeof(cmd)-readCnt, 0);
                    if (tmpReadCnt >= 0)
                    {
                        readCnt += tmpReadCnt;
                    }
                    else
                    {
                        UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read CMD!");
                        retCode = false;
                    }
                }
                readCnt = 0;

                if (cmd == testgeneration::staliro::STALIRO_INIT_COND)
                {
                    readInitCond();
                    sendAck(testgeneration::staliro::STALIRO_ACK);
                }
                else if (cmd == testgeneration::staliro::STALIRO_START_SIM)
                {
                    allReceived = true;
                    m_maxSimulationDuration_ms = readMaxSimulationDuration();
                    sendAck(testgeneration::staliro::STALIRO_ACK);
                    trajectoryRequested = true;
                }
            }
            return retCode;
        }
        
        int64_t c_CommunicationInterface::readMaxSimulationDuration()
        {
            int64_t maxSimDuration_ms = 0;
            double duration_sec = 0.0;
            uint readCnt = 0;
            uint tmpReadCnt = 0;
            
            while (readCnt < sizeof(duration_sec))
            {
                tmpReadCnt = recv( clientSocket, &duration_sec+readCnt, 
                        sizeof(duration_sec)-readCnt, 
                        0);
                if (tmpReadCnt >= 0)
                {
                    readCnt += tmpReadCnt;
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read Sim duration!");
                }
            }
            
            maxSimDuration_ms = (int64_t) (duration_sec * 1000.0);
            return maxSimDuration_ms;
        }
        
        bool c_CommunicationInterface::receiveTrajectoryRequest() 
        {
            uint32_t cmd = 0;
            uint readCnt = 0;
            uint tmpReadCnt = 0;
            bool retCode = false;
            
            while (readCnt < sizeof(cmd))
            {
                tmpReadCnt = recv( clientSocket, &cmd+readCnt, sizeof(cmd)-readCnt, 0);
                if (tmpReadCnt >= 0)
                {
                    readCnt += tmpReadCnt;
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read CMD!");
                    retCode = false;
                }
            }
            readCnt = 0;

            if (cmd == testgeneration::staliro::STALIRO_REQUEST_TRAJECTORY)
            {
                sendAck(testgeneration::staliro::STALIRO_ACK);
                retCode = true;
            }

            return retCode;
        }

        void c_CommunicationInterface::setFileFieldMapPtr(
                std::map<std::string, std::map<std::string, 
                std::string> >* mapPtr)
        {
            fileFieldMapPtr = mapPtr;
        }
        
        void c_CommunicationInterface::readInitCond()
        {
            std::string fileName = readFieldString();
            std::string fieldName = readFieldString();
            std::string value = readFieldString();
            
            (*fileFieldMapPtr)[fileName].insert(std::make_pair(fieldName, value));
        }
        
        std::string c_CommunicationInterface::readFieldString()
        {
            uint32_t msgLen = 0;
            uint readCnt = 0;
            uint tmpReadCnt = 0;
            char msgBuffer[1024] = {0};
            
            // Read Msg length
            while (readCnt < sizeof(msgLen))
            {
                tmpReadCnt = recv( clientSocket, &msgLen + readCnt, sizeof(msgLen) - readCnt, 0);
                if (tmpReadCnt >= 0)
                {
                    readCnt += tmpReadCnt;
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read msg length!");
                    msgLen = 0;
                }
            }
            readCnt = 0;
            if (msgLen > 1024)
            {
                UXAS_LOG_ERROR("staliro::CommunicationInterface::msg length larger than 1024!");
                msgLen = 0;
            }
            
            // Read Msg
            while (readCnt < msgLen)
            {
                tmpReadCnt = recv( clientSocket, &msgBuffer[readCnt], msgLen - readCnt, 0);
                if (tmpReadCnt >= 0)
                {
                    readCnt += tmpReadCnt;
                }
                else
                {
                    UXAS_LOG_ERROR("staliro::CommunicationInterface::Could not read msg length!");
                    msgLen = 0;
                }
            }
            std::string retStr(msgBuffer, (size_t) msgLen);
            return retStr;
        }
        
        
        bool c_CommunicationInterface::sendTrajInfo(uint32_t numColumns, 
                uint32_t numRows)
        {
            bool retCode = true;
            uint32_t cmd = testgeneration::staliro::STALIRO_TRAJ_INFO;
            
            resetSendBuffer();
            addToSendBuffer((void *) &cmd, sizeof(cmd));
            addToSendBuffer((void *) &numColumns, sizeof(numColumns));
            addToSendBuffer((void *) &numRows, sizeof(numRows));
            if (sendData())
            {
                retCode = receiveAck();
            }
            else
            {
                retCode = false;
            }
            return retCode;
        }
        
        void c_CommunicationInterface::addTrajectoryRow(
                    uint32_t curRowNumber, 
                    uint32_t totalNumOfRows, 
                    uint32_t numElementsInRow, 
                    double time,
                    double * row)
        {
            if (curRowNumber == 1)
            {
                trajectoryBufferPtr = (void *) trajectoryBuffer;
                sendTrajInfo((numElementsInRow+1), totalNumOfRows);
            }
            if (sizeof(double)*(numElementsInRow+1) + (uint8_t *) trajectoryBufferPtr - 
                    (uint8_t *) trajectoryBuffer > (STALIRO_SEND_BUFFER_SIZE-8))
            {
                // This row will cause overrun. First send out what was already received.
                sendTrajData((uint8_t *) trajectoryBufferPtr - (uint8_t *) trajectoryBuffer, 
                        (void *) trajectoryBuffer);
            }
            if (sizeof(double)*(numElementsInRow+1) < (STALIRO_SEND_BUFFER_SIZE-8))
            {
                memcpy(trajectoryBufferPtr, (void *)&time, sizeof(time));
                trajectoryBufferPtr = (uint8_t *)trajectoryBufferPtr + sizeof(time);
                memcpy(trajectoryBufferPtr, (void *)row, sizeof(double)*numElementsInRow);
                trajectoryBufferPtr = 
                        (uint8_t *) trajectoryBufferPtr + sizeof(double)*numElementsInRow;
            }
            if (curRowNumber >= totalNumOfRows || 
                    (sizeof(double)*(numElementsInRow+1) + (uint8_t *) trajectoryBufferPtr - 
                    (uint8_t *) trajectoryBuffer > (STALIRO_SEND_BUFFER_SIZE-8)))
            {
                // Either all the trajectory is received or the next row will cause overrun.
                // Send out what is already received.
                sendTrajData((uint8_t *) trajectoryBufferPtr - (uint8_t *) trajectoryBuffer, 
                        (void *) trajectoryBuffer);
            }
            if (curRowNumber >= totalNumOfRows)
            {
                trajectoryRequested = false;
            }
        }
        
        bool c_CommunicationInterface::sendTrajData(size_t length, void * data)
        {
            bool retCode = true;
            uint32_t cmd = testgeneration::staliro::STALIRO_TRAJ_DATA;
            
            resetSendBuffer();
            addToSendBuffer((void *) &cmd, sizeof(cmd));
            uint32_t trajLen = length;
            addToSendBuffer((void *) &trajLen, sizeof(trajLen));
            addToSendBuffer(data, length);
            if (sendData())
            {
                retCode = receiveAck();
                if (retCode)
                {
                    trajectoryBufferPtr = (void *) trajectoryBuffer;
                }
            }

            return retCode;
        }
        
        bool c_CommunicationInterface::sendHeartBeat(int64_t curTime)
        {
            double totalTimeInSec = (double) m_maxSimulationDuration_ms / 1000.0;
            double curTimeInSec = (double) curTime / 1000.0;
            bool retCode = true;
            uint32_t cmd = testgeneration::staliro::STALIRO_HEART_BEAT;
            
            if (curTime > m_lastHeartBeatTime_ms + STALIRO_HEART_BEAT_PERIOD_MS)
            {
                resetSendBuffer();
                addToSendBuffer((void *) &cmd, sizeof(cmd));
                addToSendBuffer((void *) &curTimeInSec, sizeof(curTimeInSec));
                addToSendBuffer((void *) &totalTimeInSec, sizeof(totalTimeInSec));
                if (!sendData())
                {
                    retCode = false;
                }
                m_lastHeartBeatTime_ms = curTime;
            }
            
            return retCode;
        }
        
        bool c_CommunicationInterface::isTrajectoryRequested()
        {
            return trajectoryRequested;
        }
        
        int64_t c_CommunicationInterface::getMaxSimulationDuration()
        {
            return m_maxSimulationDuration_ms;
        }
    }
}
