// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TaskOptionsTests.h
 * Author: jon
 *
 * Created on October 23, 2018, 10:47 AM
 */

#ifndef TASKPLANOPTIONSTESTS_H
#define TASKPLANOPTIONSTESTS_H

#include "LoggedMessage.h"
#include <string>
#include <vector>
#include <memory>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "afrl/cmasi/AutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include <iostream>
#include "../GtestuxastestserviceServiceManagerStartAndRun.h"
#include <algorithm>
#include "XmlHelper.h"
#include "DbHelper.h"
#include <map>

class TaskPlanOptionsTests{
public:
    TaskPlanOptionsTests(std::string dbLogPath) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedUniqueAutomationRequestMessages = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedUniqueAutomationRequestMessages){
            //
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto taskPlanOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(lmcpObj);
            timeVsTaskPlanOptionsMap[loggedMessage->GetTime()] = taskPlanOptions;
        }
    }
    
    //checks for the composition string must not be null
    bool DoCompositionStringsExist()
    {
        for(auto const& timeVsTaskPlanOptionsItem : timeVsTaskPlanOptionsMap){
            if(timeVsTaskPlanOptionsItem.second->getComposition() == ""){
                return false;
            }
        }
        return true;
    }
    
    //checks for the CorrespondingAutomationRequestID must match the RequestID of a sent UniqueAutomationRequest
    bool DoCorrespondingAutomationRequestsMatchUniqueAutomationRequests(){
        // first get the unique automation requests
        std::map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>> timeVsUniqueAutomationRequestMap;
        
        auto loggedUniqueAutomationRequestMessages = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedUniqueAutomationRequestMessages)
        {
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto uniqueAutomationRequestMessage = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(lmcpObj);
            timeVsUniqueAutomationRequestMap[loggedMessage->GetTime()] = uniqueAutomationRequestMessage;
        }
        
        for(auto const& timeVsTaskPlanOptionsItem : timeVsTaskPlanOptionsMap)
        {
            bool isMatchingUniqueAutomationRequest = false;
            
            //iterate over automation requests sent before this unique automation request message
            for(auto const& timeVsUniqueAutomationRequestItem : timeVsUniqueAutomationRequestMap)
            {
                //dont check items where the message was sent after the task plan options
                if(timeVsUniqueAutomationRequestItem.first > timeVsTaskPlanOptionsItem.first)// if time of automation request > time of unique automation request, dont check if automation requests match
                {
                    continue;
                }
                isMatchingUniqueAutomationRequest = timeVsUniqueAutomationRequestItem.second->getRequestID() == timeVsTaskPlanOptionsItem.second->getCorrespondingAutomationRequestID();
                if(isMatchingUniqueAutomationRequest) //if the matching automation request was found, search with the next unique automation request
                {
                    break;
                }
            }
            if(isMatchingUniqueAutomationRequest == false) //if match wasnt found by end of iteration over automation requests, return false
            { 
                return false;
            }
        }
        return true;
    }
    
    //checks for the TaskID must match an ID in a sent AutomationRequest
    bool DoTaskIDsMatchAutomationRequests()
    {
        //get automation requests
        std::map<int64_t, std::shared_ptr<afrl::cmasi::AutomationRequest>> timeVsAutomationRequestMap;
        
        auto loggedAutomationRequestMessages = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedAutomationRequestMessages)
        {
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto automationRequestMessage = std::static_pointer_cast<afrl::cmasi::AutomationRequest>(lmcpObj);
            timeVsAutomationRequestMap[loggedMessage->GetTime()] = automationRequestMessage;
        }
        
        //iterate over task plan options
        for(auto timeVsTaskPlanOptionItem : timeVsTaskPlanOptionsMap)
        {
            for(auto const& taskOption : timeVsTaskPlanOptionItem.second->getOptions())
            {
                bool isMatchingUniqueAutomationRequest = false;

                //iterate over automation requests sent before this unique automation request message
                for(auto const& timeVsAutomationRequestItem : timeVsAutomationRequestMap){
                    if(timeVsAutomationRequestItem.first > timeVsTaskPlanOptionItem.first){
                        continue;
                    }
                    for(auto const& taskID : timeVsAutomationRequestItem.second->getTaskList())
                    {
                        isMatchingUniqueAutomationRequest = taskID == taskOption->getTaskID();
                        if(isMatchingUniqueAutomationRequest){
                            break;
                        }
                    }
                    if(isMatchingUniqueAutomationRequest){
                        break;
                    }
                }
                if(!isMatchingUniqueAutomationRequest)
                { 
                    return false;
                }
            }
        }
        return true;
    }
    
private:
    //the descriptor the for this message type
    const std::string descriptor = uxas::messages::task::TaskPlanOptions::Subscription;
    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<uxas::messages::task::TaskPlanOptions>> timeVsTaskPlanOptionsMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};


#endif /* TASKOPTIONSTESTS_H */

