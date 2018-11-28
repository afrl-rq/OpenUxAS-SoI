// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UniqueAutomationResponseTests.h
 * Author: jon
 *
 * Created on October 23, 2018, 10:47 AM
 */

#ifndef UNIQUEAUTOMATIONRESPONSETESTS_H
#define UNIQUEAUTOMATIONRESPONSETESTS_H

#include "LoggedMessage.h"
#include <string>
#include <vector>
#include <memory>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "afrl/cmasi/AutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include <iostream>
#include "../GtestuxastestserviceServiceManagerStartAndRun.h"
#include <algorithm>
#include "XmlHelper.h"
#include "DbHelper.h"
#include <map>


class UniqueAutomationResponseTests{
public:
    UniqueAutomationResponseTests(std::string dbLogPath) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedUniqueAutomationResponseMessages = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedUniqueAutomationResponseMessages){
            //
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto uniqueAutomationResponseMessage = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(lmcpObj);
            timeVsUniqueAutomationResponseMap[loggedMessage->GetTime()] = uniqueAutomationResponseMessage;
        }
    }
    
    //check for ResponseID must have a matching RequestID from a sent UniqueAutomationRequest
    bool DoMatchingRequestsExist(){
        std::map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>> timeVsUniqueAutomationRequestMap;
        //get unique automation requests and add to map
        auto loggedUniqueAutomationRequests = dbHelper.GetLoggedMessagesByDescriptor(uxas::messages::task::UniqueAutomationRequest::Subscription);
        
        for(auto loggedMessage : loggedUniqueAutomationRequests)
        {
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto uniqueAutomationRequestMessage = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(lmcpObj);
            timeVsUniqueAutomationRequestMap[loggedMessage->GetTime()] = uniqueAutomationRequestMessage;
        }
        
        //iterate over the unique atuomation responses
        for(auto const& timeVsUniqueAutomationResponseItem : timeVsUniqueAutomationResponseMap){
            bool isMatchingUniqueAutomationRequest = false;
            //iterate over automation requests sent before this unique automation request message
            for(auto const& timeVsUniqueAutomationRequestItem : timeVsUniqueAutomationRequestMap)
            {          
                if(timeVsUniqueAutomationRequestItem.first > timeVsUniqueAutomationResponseItem.first)// if time of automation request > time of unique automation request, dont check if automation requests match
                {
                    continue;
                }
                isMatchingUniqueAutomationRequest = timeVsUniqueAutomationRequestItem.second->getRequestID() == timeVsUniqueAutomationResponseItem.second->getResponseID();
                if(isMatchingUniqueAutomationRequest) //if the matching automation request was found, search with the next unique automation request
                {
                    break;
                }
            }
            if(!isMatchingUniqueAutomationRequest) //if match wasnt found by end of iteration over automation requests, return false
            { 
                return false;
            }
        }
        return true;

    }
private:
    //the descriptor the for this message type
    const std::string descriptor = uxas::messages::task::UniqueAutomationResponse::Subscription;
    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>> timeVsUniqueAutomationResponseMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};


#endif /* UNIQUEAUTOMATIONRESPONSETESTS_H */

