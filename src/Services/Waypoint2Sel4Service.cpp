// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_WaypointPlanManager.cpp
 * Author: steve
 *
 * Created on December 16, 2014, 4:47 PM
 *
 */


#include "Waypoint2Sel4Service.h"
#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/MissionCommand.h"

//includes for writing to sel4
#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "pugixml.hpp"

#include <iostream>

#define STRING_XML_VEHICLE_ID "VehicleID"

#define COUT_INFO(MESSAGE) std::cout << "<>Waypoint2Sel4Service:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>Waypoint2Sel4Service:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>Waypoint2Sel4Service:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();


namespace uxas
{
namespace service
{
Waypoint2Sel4Service::ServiceBase::CreationRegistrar<Waypoint2Sel4Service>
Waypoint2Sel4Service::s_registrar(Waypoint2Sel4Service::s_registryServiceTypeNames());

Waypoint2Sel4Service::Waypoint2Sel4Service()
: ServiceBase(Waypoint2Sel4Service::s_typeName(), Waypoint2Sel4Service::s_directoryName()) { };

Waypoint2Sel4Service::~Waypoint2Sel4Service() { };

bool
Waypoint2Sel4Service::configure(const pugi::xml_node& ndComponent)
{
    m_vehicleID = m_entityId; // can be overridden below

    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
    }

    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription); 
    return true;
}

bool Waypoint2Sel4Service::initialize()
{
    return true;
}


bool Waypoint2Sel4Service::start()
{
    COUT_INFO("Started\n");
    return true;
}


bool Waypoint2Sel4Service::terminate()
{
    return true;
}

void Waypoint2Sel4Service::write2Sel4(afrl::cmasi::MissionCommand * mission){
    uint32_t i;
    uint8_t * pArray;

    COUT_INFO("in write2Sel4\n");

    if (mission->getVehicleID() == m_vehicleID)
    {
        mission->getVehicleActionList().clear();
        auto waypointList = mission->getWaypointList();
        for(auto waypoint : waypointList){
            waypoint->getVehicleActionList().clear();
            waypoint->getAssociatedTasks().clear();
        }
        avtas::lmcp::ByteBuffer* buf = avtas::lmcp::Factory::packMessage(mission, true);
        #if 1 == 1
        int fd = open("/dev/mem", O_RDWR | O_SYNC);
        uint8_t * mem = (uint8_t *)mmap(0, 1, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0xE0000000);

	COUT_INFO(mission->toString());
        COUT_INFO("Capacity: ");
        COUT_INFO(buf->capacity());
	pArray = buf->array();
	for(i = 0; i < buf->capacity(); i++){
            *mem = *(pArray++);
	}
//        buf->rewind();
//        while(buf->hasRemaining()){
//            *mem = buf->get();
//        }

        close(fd);
        #else
        FILE * f = fopen("/tmp/missioncommands", "wb");
        fwrite(buf->array(),1,buf->capacity(),f);
        fclose(f);
        #endif
    }
}

bool
Waypoint2Sel4Service::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{

    COUT_INFO("Got message!\n");
    if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object))
    {
        auto automationResponse = std::static_pointer_cast<afrl::cmasi::AutomationResponse> (receivedLmcpMessage->m_object);
        for (auto mission : automationResponse->getMissionCommandList())
        {
	    COUT_INFO("Writing message!\n");
            write2Sel4(mission);
        }
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object))
    {
        auto mission = std::static_pointer_cast<afrl::cmasi::MissionCommand> (receivedLmcpMessage->m_object);
	COUT_INFO("Writing message!\n");
        write2Sel4(mission.get());
    }
    return (false); // always false implies never terminating service from here
}

}; //namespace service
}; //namespace uxas
