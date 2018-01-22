// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LoiterLeash.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RoutePlanResponse.h"
#include "uxas/messages/uxnative/SafeHeadingAction.h"

namespace uxas
{
namespace service
{

// this entry registers the service in the service creation registry
LoiterLeash::ServiceBase::CreationRegistrar<LoiterLeash>
LoiterLeash::s_registrar(LoiterLeash::s_registryServiceTypeNames());

// service constructor
LoiterLeash::LoiterLeash()
: ServiceBase(LoiterLeash::s_typeName(), LoiterLeash::s_directoryName()) { };

// service destructor
LoiterLeash::~LoiterLeash() { };


bool LoiterLeash::configure(const pugi::xml_node& ndComponent)
{
    // subscribe to messages
    
    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);
    
    // route planning
    addSubscriptionAddress(uxas::messages::route::RoutePlanResponse::Subscription);
    
    // main message that drives this service
    addSubscriptionAddress(uxas::messages::uxnative::SafeHeadingAction::Subscription);

    return (true);
}

bool LoiterLeash::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    std::shared_ptr<avtas::lmcp::Object> messageObject = receivedLmcpMessage->m_object;
    auto entityConfiguration = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(messageObject);
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(messageObject);

    if (entityConfiguration)
    {
    }
    else if (entityState)
    {
    }
    else if(uxas::messages::route::isRoutePlanResponse(messageObject))
    { 
    }
    else if(uxas::messages::uxnative::isSafeHeadingAction(messageObject))
    { 
    }
    
    // sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);
    
    return false; // return false unless terminating
}

}; //namespace service
}; //namespace uxas
