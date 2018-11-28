// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   LoggedMessage.h
 * Author: jon
 *
 * Created on October 23, 2018, 2:12 PM
 */

#ifndef LOGGEDMESSAGE_H
#define LOGGEDMESSAGE_H
#include <string>
#include <iostream>
class LoggedMessage {
public:
//    LoggedMessage(int id, int time_ms, std::string descriptor, std::string groupID, int entityID, int serviceID, std::string xml);
//    LoggedMessage(const LoggedMessage& orig);
//    int GetId();
//    int GetTime();
//    std::string GetDescriptor();
//    std::string GetGroupId();
//    int GetEntityId();
//    int GetServiceId();
//    std::string GetXml();
//    virtual ~LoggedMessage();
    LoggedMessage(int id, int64_t time_ms, std::string descriptor, std::string groupID, int entityID, int serviceID, std::string xml) :
    id(id), time_ms(time_ms), descriptor(descriptor), groupID(groupID), entityID(entityID), serviceID(serviceID), xml(xml){
    }

    LoggedMessage(const LoggedMessage& orig) {
    }

    ~LoggedMessage() {
    }

    int GetId(){
        return id;
    }

    int64_t GetTime(){
        return time_ms;
    }

    std::string GetDescriptor(){
        return descriptor;
    }

    std::string GetGroupId(){
        return groupID;
    }

    int GetEntityId(){
        return entityID;
    }

    int GetServiceId(){
        return serviceID;
    }

    std::string GetXml(){
        return xml;
    }
    
private:
    int id;
    int64_t time_ms;
    std::string descriptor;
    std::string groupID;
    int entityID;
    int serviceID;
    std::string xml;
};

#endif /* LOGGEDMESSAGE_H */

