// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   SensorFootprintResponseTests.h
 * Author: jon
 *
 * Created on October 23, 2018, 10:47 AM
 */

#ifndef SENSORFOOTPRINTRESPONSETESTS_H
#define SENSORFOOTPRINTRESPONSETESTS_H

#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/SensorFootprintRequests.h"

class SensorFootprintResponseTests{
public:
    SensorFootprintResponseTests(std::string dbLogPath) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedSensorFootprintResponses = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedSensorFootprintResponses){
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto sensorFootprintResponse = std::static_pointer_cast<uxas::messages::task::SensorFootprintResponse>(lmcpObj);
            timeVsSensorFootprintResponseMap[loggedMessage->GetTime()] = sensorFootprintResponse;
        }
    }
    
    //check that ResponseID matches the requestID of a sent SensorFootprintRequest
    bool DoResponsesHaveMatchingRequests(){
        //first get sensor footprint requests
        std::map<int64_t, std::shared_ptr<uxas::messages::task::SensorFootprintRequests>> timeVsSensorFootprintRequestMap;
        
        auto sensorFootprintRequestDescriptor = uxas::messages::task::SensorFootprintRequests::Subscription;
        auto loggedSensorFootprintRequests = dbHelper.GetLoggedMessagesByDescriptor(sensorFootprintRequestDescriptor);

        for(auto loggedMessage : loggedSensorFootprintRequests){
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto sensorFootprintRequest = std::static_pointer_cast<uxas::messages::task::SensorFootprintRequests>(lmcpObj);
            timeVsSensorFootprintRequestMap[loggedMessage->GetTime()] = sensorFootprintRequest;
        }
        
        for(auto const& timeVsSensorFootprintResponseItem : timeVsSensorFootprintResponseMap)
        {
            std::cerr << "The footprint response ID is: " << timeVsSensorFootprintResponseItem.second->getFootprints().at(0)->getFootprintResponseID() << std::endl;
            bool isMatchingSensorFootprintRequest = false;
           
            for(auto const& timeVsSensorFootprintRequestItem : timeVsSensorFootprintRequestMap)
            {
                std::cerr << "The footprint request ID is: " << timeVsSensorFootprintRequestItem.second->getFootprints().at(0)->getFootprintRequestID() << std::endl;
                if(timeVsSensorFootprintRequestItem.first > timeVsSensorFootprintResponseItem.first)
                {
                    continue;
                }
                if(timeVsSensorFootprintRequestItem.second->getRequestID() == timeVsSensorFootprintResponseItem.second->getResponseID()){
                    isMatchingSensorFootprintRequest = true;
                    break;
                }
            }
            if(!isMatchingSensorFootprintRequest)
            {
                return isMatchingSensorFootprintRequest;
            }
        } 
        return true;
    }
    
    
    //each SensorFootprintResponseID must match a SensorFootprintRequestID
    bool DoFootprintResponseIDsHaveMatchingRequestIDs()
    {
        //first get sensor footprint requests
        std::map<int64_t, std::shared_ptr<uxas::messages::task::SensorFootprintRequests>> timeVsSensorFootprintRequestMap;
        
        auto sensorFootprintRequestDescriptor = uxas::messages::task::SensorFootprintRequests::Subscription;
        auto loggedSensorFootprintRequests = dbHelper.GetLoggedMessagesByDescriptor(sensorFootprintRequestDescriptor);

        for(auto loggedMessage : loggedSensorFootprintRequests){
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto sensorFootprintRequest = std::static_pointer_cast<uxas::messages::task::SensorFootprintRequests>(lmcpObj);
            timeVsSensorFootprintRequestMap[loggedMessage->GetTime()] = sensorFootprintRequest;
        }
        
        for(auto const& timeVsSensorFootprintResponseItem : timeVsSensorFootprintResponseMap)
        {
            //iterate over footprints in sensor footprint response items
            for(auto const& responseFootprint : timeVsSensorFootprintResponseItem.second->getFootprints())
            {
                bool isMatchingFootprintRequest = false;
                //now iterate through the sensor footprint requests
                for(auto const& timeVsSensorFootprintRequestItem : timeVsSensorFootprintRequestMap)
                {
                    if(timeVsSensorFootprintRequestItem.first > timeVsSensorFootprintResponseItem.first){
                        continue;
                    }
                    for(auto const& requestFootprint : timeVsSensorFootprintRequestItem.second->getFootprints()){
                        if(requestFootprint->getFootprintRequestID() == responseFootprint->getFootprintResponseID()){
                            isMatchingFootprintRequest = true;
                        }
                    }
                    if(isMatchingFootprintRequest){
                        break;
                    } else {
                        return isMatchingFootprintRequest;
                    }
                }
            }
        }
        return true;
    }
    
    
    
private:
    //the descriptor the for this message type
    const std::string descriptor = uxas::messages::task::SensorFootprintResponse::Subscription;//"uxas.messages.task.SensorFootprintRequests";    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<uxas::messages::task::SensorFootprintResponse>> timeVsSensorFootprintResponseMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};

#endif /* SENSORFOOTPRINTRESPONSETESTS_H */

