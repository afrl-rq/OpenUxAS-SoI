// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UniqueAutomationRequestTests.h
 * Author: jon
 *
 * Created on October 26, 2018, 11:36 AM
 */

#ifndef UNIQUEAUTOMATIONREQUESTTESTS_H
#define UNIQUEAUTOMATIONREQUESTTESTS_H

#include "LoggedMessage.h"
#include <string>
#include <vector>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "afrl/cmasi/AutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include <iostream>
#include "../GtestuxastestserviceServiceManagerStartAndRun.h"
#include <algorithm>
#include "XmlHelper.h"
#include "DbHelper.h"
#include <map>

class UniqueAutomationRequestTests {
public:
    UniqueAutomationRequestTests(const std::string& dbLogPath) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedUniqueAutomationRequestMessages = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedUniqueAutomationRequestMessages){            
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto uniqueAutomationRequestMessage = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(lmcpObj);
            timeVsUniqueAutomationRequestMap[loggedMessage->GetTime()] = uniqueAutomationRequestMessage;
        }

    }
    
    //checks for RequestID must be unique
    bool AreRequestIdsUnique(){
        for (auto const& timeUniqueAutomationRequestVals : timeVsUniqueAutomationRequestMap){
            int count = 0;
            
            for(auto const& checkedTimeUniqueAutomationRequestVals : timeVsUniqueAutomationRequestMap){
                if(timeUniqueAutomationRequestVals.second->getRequestID() == checkedTimeUniqueAutomationRequestVals.second->getRequestID()){
                    count++;
                }
                if(count > 1){
                    return false;
                }
            }
        }
        return true;
    }
    
    //checks for the OriginalRequest must match an automation request that was sent prior to teh unique automation request
    bool DoOriginalRequestsHaveMatchingAutomationRequests(){
        // General Overview
        // 1) get automation requests xml
        // 2) iterate through unique automation requests messages and check all automation requests for matching xml tags
        
        //get automation request messages from db and map with time
        std::map<int64_t, std::shared_ptr<afrl::cmasi::AutomationRequest>> timeVsAutomationRequestMessageMap; //setup map to store [time : automation request]
        
        auto loggedAutomationRequestMessages = dbHelper.GetLoggedMessagesByDescriptor(afrl::cmasi::AutomationRequest::Subscription); //get all automation request messages
        
        for(auto loggedMessage : loggedAutomationRequestMessages)  //populate the timVsAutomationRequestMessageMap [time : automation request]
        {
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto automationRequestMessage = std::static_pointer_cast<afrl::cmasi::AutomationRequest>(lmcpObj);
            timeVsAutomationRequestMessageMap[loggedMessage->GetTime()] = automationRequestMessage;
        }
  
        // Check For Matching Automation Requests
        //1) iterate over the unique automation request messages
        //2) create xml helper with root xml_node for the original automation request obtained from the unique automation request message
        //3) iterate over the automation requests in the automation request map that were sent prior to the checked unique automation request message
        //4) create xml helper with root xml_node for the automation requests obtained from the automation request messages
        //5) check if xml_nodes match with xml helper. if they do, break the loop and continue iterating through unique automation request messages
        //   if they dont, then return false
        //6)   return true if false was not returned by end of method
        for(auto const& timeVsUniqueAutomationRequestItem : timeVsUniqueAutomationRequestMap)
        {
            auto originalAutomationRequestXmlHelper = XmlHelper(timeVsUniqueAutomationRequestItem.second->getOriginalRequest()->toXML());
            bool isMatchingAutomationRequest = false;
            
            //iterate over automation requests sent before this unique automation request message
            for(auto const& timeVsAutomationRequestItem : timeVsAutomationRequestMessageMap)
            {          
                if(timeVsAutomationRequestItem.first > timeVsUniqueAutomationRequestItem.first)// if time of automation request > time of unique automation request, dont check if automation requests match
                {
                    continue;
                }
                auto automationRequestXmlHelper = XmlHelper(timeVsAutomationRequestItem.second->toXML());
                isMatchingAutomationRequest = XmlHelper::DoNodesMatch(originalAutomationRequestXmlHelper.GetRootNode(), automationRequestXmlHelper.GetRootNode());
                if(isMatchingAutomationRequest) //if the matching automation request was found, search with the next unique automation request
                {
                    break;
                }
            }
            if(isMatchingAutomationRequest == false) //if match wasnt found by end of iteration over automation requests, return false
            { 
                return false;
            }
        }
        return true;
    }
    
    virtual ~UniqueAutomationRequestTests(){};
private:
    //the descriptor the for this message type
    const std::string descriptor = uxas::messages::task::UniqueAutomationRequest::Subscription;
    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>> timeVsUniqueAutomationRequestMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};

#endif /* UNIQUEAUTOMATIONREQUESTTESTS_H */

