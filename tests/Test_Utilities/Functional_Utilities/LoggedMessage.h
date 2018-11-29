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
    
    LoggedMessage(int id, int64_t time_ms, std::string descriptor, std::string groupID, int entityID, int serviceID, std::string xml) :
    id(id), time_ms(time_ms), descriptor(descriptor), groupID(groupID), entityID(entityID), serviceID(serviceID), xml(xml){
    }

    LoggedMessage(const LoggedMessage& orig) {
    }

    ~LoggedMessage() {
    }

    // returns the id of the logged message
    int GetId(){
        return id;
    }

    // returns the time the logged message was sent
    int64_t GetTime(){
        return time_ms;
    }

    // returns the descriptor of the logged message
    std::string GetDescriptor(){
        return descriptor;
    }

    // returns the group id of the logged message
    std::string GetGroupId(){
        return groupID;
    }

    //returns the entity id of the logged message
    int GetEntityId(){
        return entityID;
    }

    //returns the service id of the logged message
    int GetServiceId(){
        return serviceID;
    }

    //returns the raw xml of the logged message
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

