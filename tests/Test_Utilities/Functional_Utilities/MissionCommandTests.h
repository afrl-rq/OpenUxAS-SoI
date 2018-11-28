// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   MissionCommandTests.h
 * Author: jon
 *
 * Created on October 23, 2018, 10:46 AM
 */

#ifndef MISSIONCOMMANDTESTS_H
#define MISSIONCOMMANDTESTS_H


#include "LoggedMessage.h"
#include <string>
#include <vector>
#include <SQLiteCpp/Database.h>
#include <SQLiteCpp/SQLiteCpp.h>
#include "afrl/cmasi/MissionCommand.h"
#include <iostream>
#include "../GtestuxastestserviceServiceManagerStartAndRun.h"
#include <algorithm>
#include "XmlHelper.h"
#include "DbHelper.h"
#include <map>

class MissionCommandTests{
public:
    MissionCommandTests(std::string dbLogPath) : dbHelper(dbLogPath)
    {
        //get the logged unique automation request messages
        auto loggedMissionCommands = dbHelper.GetLoggedMessagesByDescriptor(descriptor);
        
        for(auto loggedMessage : loggedMissionCommands)
        {
            auto lmcpObj = std::shared_ptr<avtas::lmcp::Object>(avtas::lmcp::xml::readXML(loggedMessage->GetXml()));
            auto missionCommandMessage = std::static_pointer_cast<afrl::cmasi::MissionCommand>(lmcpObj);
            timeVsMissionCommandMap[loggedMessage->GetTime()] = missionCommandMessage;
        }
    }
    
    //checks for the first waypoint must match a waypoint's number in the mission command's waypoint list
    bool DoesFirstWaypointMatchWaypointInWaypointList()
    {
        for(auto const& timeVsMissionCommandItem : timeVsMissionCommandMap)
        {
            bool isMatchingWaypoint = false;
            int64_t firstWaypointId = timeVsMissionCommandItem.second->getFirstWaypoint();
            for(auto const& waypoint : timeVsMissionCommandItem.second->getWaypointList())
            {
                if(waypoint->getNumber() == firstWaypointId)
                {
                    isMatchingWaypoint = true;
                    break;
                }
                
            }
            if(!isMatchingWaypoint){
                return false;
            }
        }
        return true;
    }
    
    //checks for the CommandID must be unique to each mission command
    bool AreCommandIdsUnique(){
        for (auto const& timeVsMissionCommandItem : timeVsMissionCommandMap){
            int count = 0;
            
            for(auto const& checkedTimeVsMissionCommandItem : timeVsMissionCommandMap){
                if(timeVsMissionCommandItem.second->getCommandID() == checkedTimeVsMissionCommandItem.second->getCommandID()){
                    count++;
                }
                if(count > 1){
                    return false;
                }
            }
        }
        return true;
    }
    
private:
    
    //the descriptor the for this message type
    const std::string descriptor = afrl::cmasi::MissionCommand::Subscription;
    
    //store a map with time : uniqueAutomationReuqest?
    std::map<int64_t, std::shared_ptr<afrl::cmasi::MissionCommand>> timeVsMissionCommandMap;
    
    //the helper that pulls data from the db
    DbHelper dbHelper;
};


#endif /* MISSIONCOMMANDTESTS_H */
