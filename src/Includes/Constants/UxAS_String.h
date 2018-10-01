// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_STRING_CONSTANT_H
#define UXAS_COMMON_STRING_CONSTANT_H

#include <string>

namespace uxas
{ 
namespace common
{ 
class StringConstant
{
public:


//
    static const std::string& Alias() { static std::string s_string("Alias"); return(s_string); };
    static const std::string& AlwaysSendPosition() { static std::string s_string("AlwaysSendPosition"); return(s_string); };
    static const std::string& BaudRate() { static std::string s_string("BaudRate"); return(s_string); };
    static const std::string& Bridge() { static std::string s_string("Bridge"); return(s_string); };
    static const std::string& Component() { static std::string s_string("Component"); return(s_string); };
    static const std::string& ComponentManager() { static std::string s_string("ComponentManager"); return(s_string); };
    static const std::string& Components() { static std::string s_string("Components"); return(s_string); };
    static const std::string& ConsoleLoggerSeverityLevel() { static std::string s_string("ConsoleLoggerSeverityLevel"); return(s_string); };
    static const std::string& EntityID() { static std::string s_string("EntityID"); return(s_string); };
    static const std::string& EntityType() { static std::string s_string("EntityType"); return(s_string); };
    static const std::string& FilterType() { static std::string s_string("FilterType"); return(s_string); };
    static const std::string& GapTime_ms() { static std::string s_string("GapTime_ms"); return(s_string); };
    static const std::string& isDataTimestamp() { static std::string s_string("isDataTimestamp"); return(s_string); };
    static const std::string& isLoggingThreadId() { static std::string s_string("isLoggingThreadId"); return(s_string); };
    static const std::string& LogFileMessageCountLimit() { static std::string s_string("LogFileMessageCountLimit"); return(s_string); };
    static const std::string& MainFileLoggerSeverityLevel() { static std::string s_string("MainFileLoggerSeverityLevel"); return(s_string); };
    static const std::string& MessageGroup() { static std::string s_string("MessageGroup"); return(s_string); };
    static const std::string& MessageType() { static std::string s_string("MessageType"); return(s_string); };
    static const std::string& NetworkDevice() { static std::string s_string("NetworkDevice"); return(s_string); };
    static const std::string& ZyreEndpoint() { static std::string s_string("ZyreEndpoint"); return(s_string); };
    static const std::string& GossipEndpoint() { static std::string s_string("GossipEndpoint"); return(s_string); };
    static const std::string& GossipBind() { static std::string s_string("GossipBind"); return(s_string); };
    static const std::string& ReceiveEntityId() { static std::string s_string("ReceiveEntityId"); return(s_string); };
    static const std::string& RunDuration_s() { static std::string s_string("RunDuration_s"); return(s_string); };
    static const std::string& SendAddress() { static std::string s_string("SendAddress"); return(s_string); };
    static const std::string& SendContentType() { static std::string s_string("SendContentType"); return(s_string); };
    static const std::string& SendDescriptor() { static std::string s_string("SendDescriptor"); return(s_string); };
    static const std::string& SendMessages() { static std::string s_string("SendMessages"); return(s_string); };
    static const std::string& SendSourceEntityId() { static std::string s_string("SendSourceEntityId"); return(s_string); };
    static const std::string& SendSourceGroup() { static std::string s_string("SendSourceGroup"); return(s_string); };
    static const std::string& SendSourceServiceId() { static std::string s_string("SendSourceServiceId"); return(s_string); };
    static const std::string& SerialPortAddress() { static std::string s_string("SerialPortAddress"); return(s_string); };
    static const std::string& SerialPollWaitTime_us() { static std::string s_string("SerialPollWaitTime_us"); return(s_string); };
    static const std::string& SerialTimeout_ms() { static std::string s_string("SerialTimeout_ms"); return(s_string); };
    static const std::string& Server() { static std::string s_string("Server"); return(s_string); };
    static const std::string& Service() { static std::string s_string("Service"); return(s_string); };
    static const std::string& StartDelay_ms() { static std::string s_string("StartDelay_ms"); return(s_string); };
    static const std::string& SubscribeToExternalMessage() { static std::string s_string("SubscribeToExternalMessage"); return(s_string); };
    static const std::string& SubscribeToMessage() { static std::string s_string("SubscribeToMessage"); return(s_string); };
    static const std::string& TcpAddress() { static std::string s_string("TcpAddress"); return(s_string); };
    static const std::string& TransformReceivedMessage() { static std::string s_string("TransformReceivedMessage"); return(s_string); };
    static const std::string& Type() { static std::string s_string("Type"); return(s_string); };
    static const std::string& UAV() { static std::string s_string("UAV"); return(s_string); };
    static const std::string& UxAS() { static std::string s_string("UxAS"); return(s_string); };

};

class ContentType
{
public:

    static const std::string& json() { static std::string s_string("json"); return(s_string); };
    static const std::string& lmcp() { static std::string s_string("lmcp"); return(s_string); };
    static const std::string& text() { static std::string s_string("text"); return(s_string); };
    static const std::string& xml() { static std::string s_string("xml"); return(s_string); };

};

class MessageGroup
{
public:

    static const std::string& RadarFilter() { static std::string s_string("RadarFilter"); return(s_string); };
    static const std::string& VicsLogger() { static std::string s_string("VicsLogger"); return(s_string); };
    static const std::string& AircraftPathPlanner() { static std::string s_string("AircraftPathPlanner"); return(s_string); };
    static const std::string& GroundPathPlanner() { static std::string s_string("GroundPathPlanner"); return(s_string); };
    static const std::string& PartialAirVehicleState() { static std::string s_string("PartialAirVehicleState"); return(s_string); };
};

class LmcpNetworkSocketAddress
{
public:

    static const std::string& strGetInProc_ThreadControl(){static std::string strString("inproc://thread_control");return(strString);};
    static const std::string& strGetInProc_FromMessageHub(){static std::string strString("inproc://from_message_hub");return(strString);};
    static const std::string& strGetInProc_ToMessageHub(){static std::string strString("inproc://to_message_hub");return(strString);};
    static const std::string& strGetInProc_ConfigurationHub(){static std::string strString("inproc://configuration_hub");return(strString);};
    static const std::string& strGetInProc_ManagerThreadControl(){static std::string strString("inproc://manager_thread_control");return(strString);};

};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_STRING_CONSTANT_H */
