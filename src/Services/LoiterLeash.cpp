// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "LoiterLeash.h"

#include "UnitConversions.h"
#include "Constants/Convert.h"


#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RoutePlanResponse.h"
#include "uxas/messages/route/RouteConstraints.h"
#include "uxas/messages/uxnative/SafeHeadingAction.h"
#include "afrl/cmasi/LoiterAction.h"

#define STRING_XML_VEHICLE_ID "VehicleID"
#define STRING_XML_RADIUS_BUFFER "RadiusBuffer"
#define STRING_XML_LEAD_DISTANCE "LeadDistance"

#define COUT_INFO(MESSAGE) std::cout << "<>LoiterLeash:: " << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE() std::cout << "<>LoiterLeash:: " << __FILE__ << ":" << __LINE__ << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>LoiterLeash:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>LoiterLeash:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();


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
    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
    }
    if (!ndComponent.attribute(STRING_XML_RADIUS_BUFFER).empty())
    {
        m_radiusBuffer = ndComponent.attribute(STRING_XML_RADIUS_BUFFER).as_double(m_radiusBuffer);
        if(m_radiusBuffer < 1e-4) m_radiusBuffer = 0.0;
    }
    if (!ndComponent.attribute(STRING_XML_LEAD_DISTANCE).empty())
    {
        m_leadDistance = ndComponent.attribute(STRING_XML_LEAD_DISTANCE).as_double(m_leadDistance);
    }

    // subscribe to messages

    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for (auto child : childconfigs)
        addSubscriptionAddress(child);

    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for (auto child : childstates)
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

    if (entityState)
    {
        if (entityState->getID() == m_vehicleID)
        {
            m_lastEntityState = entityState;
        }
    }
    else if (entityConfiguration)
    {
        if (entityConfiguration->getID() == m_vehicleID)
        {
            // add turn rate constraints ????
            m_entityConfiguration = entityConfiguration;
        }
    }
    else if (uxas::messages::route::isRoutePlanResponse(messageObject))
    {
        auto routePlanResponse = std::static_pointer_cast<uxas::messages::route::RoutePlanResponse>(messageObject);
        if(m_nextVehicleActionCommand && (routePlanResponse->getResponseID() == m_currentRouteId) && (!routePlanResponse->getRouteResponses().empty()))
        {
            //COUT_FILE_LINE_MSG("routePlanResponse->getRouteResponses().front()->getWaypoints().size()[" << routePlanResponse->getRouteResponses().front()->getWaypoints().size() << "]")
            if((!routePlanResponse->getRouteResponses().front()->getWaypoints().empty()) && (routePlanResponse->getRouteResponses().front()->getWaypoints().size() < 3))
            {
                sendSharedLmcpObjectBroadcastMessage(m_nextVehicleActionCommand);
                m_nextVehicleActionCommand.reset();
            }
        }
        
    }
    else if (uxas::messages::uxnative::isSafeHeadingAction(messageObject))
    {
        auto safeHeadingAction = std::static_pointer_cast<uxas::messages::uxnative::SafeHeadingAction>(messageObject);
        if ((safeHeadingAction->getVehicleID() == m_vehicleID) && (m_lastEntityState) && (m_entityConfiguration))
        {
            // convert vehicle position to linear coordinates
            uxas::common::utilities::CUnitConversions cUnitConversions;
            double vehicleNorth_m(0.0);
            double vehicleEast_m(0.0);
            cUnitConversions.ConvertLatLong_degToNorthEast_m(m_lastEntityState->getLocation()->getLatitude(),
                                                             m_lastEntityState->getLocation()->getLongitude(),
                                                             vehicleNorth_m, vehicleEast_m);

            // center of loiter, calculated below
            double loiterCenterLatitude_deg{0.0};
            double loiterCenterLongitude_deg{0.0};

            if (safeHeadingAction->getUseHeadingRate())
            {
                // use heading rate

            }
            else
            {
                // use DesiredHeading
                // calculate desired loiter position
                double leadDistance = safeHeadingAction->getLeadAheadDistance();
                if(m_leadDistance > 1e-4)
                    leadDistance = m_leadDistance; // override from config
                double loiterCenterEast_m = vehicleEast_m + leadDistance * sin(n_Const::c_Convert::toRadians(safeHeadingAction->getDesiredHeading()));
                double loiterCenterNorth_m = vehicleNorth_m + leadDistance * cos(n_Const::c_Convert::toRadians(safeHeadingAction->getDesiredHeading()));
                cUnitConversions.ConvertNorthEast_mToLatLong_deg(loiterCenterNorth_m, loiterCenterEast_m, loiterCenterLatitude_deg, loiterCenterLongitude_deg);
            }

            afrl::cmasi::LoiterAction* pLoiterAction = new afrl::cmasi::LoiterAction();
            afrl::cmasi::Location3D* loiterLoc = new afrl::cmasi::Location3D();
            float commandedAltitude_m{m_entityConfiguration->getNominalAltitude()};
            if(safeHeadingAction->getUseAltitude())
            {
                commandedAltitude_m = safeHeadingAction->getAltitude();
                loiterLoc->setAltitude(safeHeadingAction->getAltitude());
                loiterLoc->setAltitude(safeHeadingAction->getAltitudeType());
            }
            else
            {
                loiterLoc->setAltitude(m_entityConfiguration->getNominalAltitude());
                loiterLoc->setAltitudeType(m_entityConfiguration->getNominalAltitudeType());
            }
            loiterLoc->setLatitude(loiterCenterLatitude_deg);
            loiterLoc->setLongitude(loiterCenterLongitude_deg);
            pLoiterAction->setLocation(loiterLoc);
            loiterLoc = 0; // gave up ownership
            
            if(safeHeadingAction->getUseSpeed())
            {
                pLoiterAction->setAirspeed(safeHeadingAction->getSpeed());
            }
            else
            {
                pLoiterAction->setAirspeed(m_entityConfiguration->getNominalSpeed());
            }
            pLoiterAction->setRadius(safeHeadingAction->getLoiterRadius());
            pLoiterAction->getAssociatedTaskList() = safeHeadingAction->getAssociatedTaskList();
            pLoiterAction->setAxis(0.0);
            pLoiterAction->setDirection(afrl::cmasi::LoiterDirection::Clockwise);
            pLoiterAction->setDuration(-1.0);
            pLoiterAction->setLength(0.0);
            pLoiterAction->setLoiterType(afrl::cmasi::LoiterType::Circular);

            auto vehicleActionCommand = std::make_shared<afrl::cmasi::VehicleActionCommand>();
            vehicleActionCommand->setVehicleID(m_lastEntityState->getID());
            vehicleActionCommand->getVehicleActionList().push_back(pLoiterAction);
            pLoiterAction = 0;
            
            m_nextVehicleActionCommand = vehicleActionCommand;
            
            // send out the route request
            
            m_currentRouteId++;
            
            double safeDistance_m =  safeHeadingAction->getLeadAheadDistance() + m_radiusBuffer*safeHeadingAction->getLoiterRadius();
            if(m_leadDistance > 1e-4)
                safeDistance_m = m_leadDistance + m_radiusBuffer*safeHeadingAction->getLoiterRadius(); // override from config
            double safePointEast_m = vehicleEast_m + safeDistance_m * sin(n_Const::c_Convert::toRadians(safeHeadingAction->getDesiredHeading()));
            double safePointNorth_m = vehicleNorth_m + safeDistance_m * cos(n_Const::c_Convert::toRadians(safeHeadingAction->getDesiredHeading()));
            double safePointLatitude_deg{0.0};
            double safePointLongitude_deg{0.0};
            cUnitConversions.ConvertNorthEast_mToLatLong_deg(safePointNorth_m, safePointEast_m, safePointLatitude_deg, safePointLongitude_deg);
            
            //TODO:: need to plan past the end of the farthest point on the loiter
            auto routePlanRequest = std::make_shared<uxas::messages::route::RoutePlanRequest>();
            routePlanRequest->setRequestID(m_currentRouteId);
            routePlanRequest->setIsCostOnlyRequest(false);
            routePlanRequest->setOperatingRegion(safeHeadingAction->getOperatingRegion());
            routePlanRequest->setVehicleID(m_lastEntityState->getID());
            auto routeConstraints = new uxas::messages::route::RouteConstraints;
            routeConstraints->setRouteID(m_currentRouteId);
            routeConstraints->setStartLocation(m_lastEntityState->getLocation()->clone());
            routeConstraints->setUseStartHeading(false);
            
            auto endLocation = new afrl::cmasi::Location3D;
            endLocation->setLatitude(safePointLatitude_deg);
            endLocation->setLongitude(safePointLongitude_deg);
            endLocation->setAltitude(commandedAltitude_m);
            routeConstraints->setEndLocation(endLocation);
            endLocation = nullptr;   //just gave up ownership   
            routeConstraints->setUseEndHeading(false);
            routePlanRequest->getRouteRequests().push_back(routeConstraints);
            routeConstraints = nullptr; //just gave up ownership                                
            
            
            sendSharedLmcpObjectBroadcastMessage(routePlanRequest);
        }
    }

    // sendSharedLmcpObjectBroadcastMessage(keyValuePairOut);

    return false; // return false unless terminating
}

}; //namespace service
}; //namespace uxas
