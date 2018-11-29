// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   SensorFootprintRequestTests.h
 * Author: jon
 *
 * Created on October 23, 2018, 10:46 AM
 */

#ifndef SENSORFOOTPRINTREQUESTTESTS_H
#define SENSORFOOTPRINTREQUESTTESTS_H

#include "LoggedMessage.h"
#include <string>
#include <vector>
#include <memory>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "afrl/cmasi/AutomationRequest.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include <iostream>
#include "../GtestuxastestserviceServiceManagerStartAndRun.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include <algorithm>
#include "XmlHelper.h"
#include "DbHelper.h"
#include <map>

class SensorFootprintRequestTests{
public:
    SensorFootprintRequestTests(std::string dbLogPath ) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedSensorFootprintRequests = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedSensorFootprintRequests){
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto sensorFootprintRequest = std::static_pointer_cast<uxas::messages::task::SensorFootprintRequests>(lmcpObj);
            timeVsSensorFootprintRequestMap[loggedMessage->GetTime()] = sensorFootprintRequest;
        }
    }
    
    //checks for the RequestID must be unique
    bool AreRequestIdsUnique(){
        for (auto const& timeVsSensorFootprintRequestVals : timeVsSensorFootprintRequestMap){
            int count = 0;
            
            for(auto const& checkedTimeVsSensorFootprintRequestVals : timeVsSensorFootprintRequestMap){
                if(timeVsSensorFootprintRequestVals.second->getRequestID() == checkedTimeVsSensorFootprintRequestVals.second->getRequestID()){
                    count++;
                }
                if(count > 1){
                    return false;
                }
            }
        }
        return true;
    }
    
    //checks for each footprint's VehicleID must be represented as the EntityID of an EntityConfiguration
    bool DoFootprintVehiclesExist(){
        //make vector of all entity configuration subscription addresses (descriptors) to query db with
        std::vector<std::string> descriptors = afrl::cmasi::EntityConfigurationDescendants();
        descriptors.push_back(afrl::cmasi::EntityConfiguration::Subscription);
        
        //first get the entity configurations 
        std::map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration>> timeVsEntityConfigurationMap;
        
        for(auto const& entityDescriptor : descriptors){
            auto loggedEntityConfigurationMessages = dbHelper.GetLoggedMessagesByDescriptor(entityDescriptor);

            for(auto loggedMessage : loggedEntityConfigurationMessages){
                auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
                auto entityConfiguration = std::static_pointer_cast<afrl::cmasi::EntityConfiguration>(lmcpObj);
                timeVsEntityConfigurationMap[loggedMessage->GetTime()] = entityConfiguration;
            }
        }
        //Check if each sensor footprint request has a corresponding entity configuration
        //loop through the sensorFootprintRequestTests
        for(auto const& timeVsSensorFootprintRequestItem : timeVsSensorFootprintRequestMap)
        {
            //iterate over the footprints
            auto sensorFootprints = timeVsSensorFootprintRequestItem.second->getFootprints();
            for(auto const& footprint : sensorFootprints){
                bool isMatchingVehicleFound = false;
                //now check if a matching entity configuration exists for the footprint (vehice ID match)
                for(auto const& timeVsEntityConfigurationItem : timeVsEntityConfigurationMap){
                    if(timeVsEntityConfigurationItem.first > timeVsSensorFootprintRequestItem.first){
                        continue;
                    }
                   
                    if(footprint->getVehicleID() == timeVsEntityConfigurationItem.second->getID()){
                        isMatchingVehicleFound = true;
                        break; //continue searching at the next footrpint
                    }
                    
                }//end entity configuration map loop
                if(!isMatchingVehicleFound){
                    return isMatchingVehicleFound;
                }
            }//end sensor footprint loop 
        }//end sensor footprint map loop
        
        
        return true;
    }
    
    
    
private:
    //the descriptor the for this message type
    const std::string descriptor = uxas::messages::task::SensorFootprintRequests::Subscription;//"uxas.messages.task.SensorFootprintRequests";    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<uxas::messages::task::SensorFootprintRequests>> timeVsSensorFootprintRequestMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};

#endif /* SENSORFOOTPRINTREQUESTTESTS_H */
