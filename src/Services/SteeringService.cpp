// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2018 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "SteeringService.h"

#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/cmasi/AirVehicleConfigurationDescendants.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/FlightDirectorAction.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/LoiterAction.h"
#include "afrl/cmasi/LoiterDirection.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/SpeedType.h"
#include "afrl/cmasi/VehicleAction.h"
#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/Waypoint.h"
#include "uxas/messages/uxnative/SafeHeadingAction.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"

#include "Constants/Convert.h"
#include "Constants/UxAS_String.h"
#include "FlatEarth.h"
#include "UxAS_Log.h"
#include "UxAS_Time.h"
#include "visilibity.h"

#include "stdUniquePtr.h"

#include <algorithm>
#include <vector>

#include <cassert>
#include <cmath>

//  Reference paper:
//      Nelson, D. R., Barber, D. B., McLain, T. W., & Beard, R. W. (2007). Vector field path following
//      for miniature air vehicles. IEEE Transactions on Robotics, 23(3), 519-529.

namespace
{

#define STRING_XML_VEHICLE_ID "VehicleID"

// #define STRING_XML_ALPHA "Alpha"

#define STRING_XML_ACCEPTANCE_TIME "AcceptanceTime_ms"
#define STRING_XML_MAXIMUM_COURSE_ANGLE_DEG "MaxCourseAngleDeg"
#define STRING_XML_K_LINE "KLine"
// #define STRING_XML_KAPPA_LINE "KappaLine"
// #define STRING_XML_EPSILON_LINE "EpsilonLine"

#define STRING_XML_K_ORBIT "KOrbit"
// #define STRING_XML_KAPPA_ORBIT "KappaOrbit"
// #define STRING_XML_EPSILON_ORBIT "EpsilonOrbit"

const double DISTANCE_TRESHOLD_M = 1.0;

double mag(const VisiLibity::Point& point)
{
    return sqrt(point.x()*point.x() + point.y()*point.y());
}

double dot(const VisiLibity::Point& point1, const VisiLibity::Point& point2)
{
    return (point1.x()*point2.x() + point1.y()*point2.y());
}

void configureDoubleOptionIfPositive(double& option, const pugi::xml_node& ndComponent, const char* optionString, double defaultValue)
{
    option = defaultValue;

    if (!ndComponent.attribute(optionString).empty())
    {
        const double value = ndComponent.attribute(optionString).as_double();

        if (value > 0.0)
        {
            option = value;
        }
    }
}

// double sat(double x)
// {
//     return (x > 1.0) ? 1.0 : ((x < -1.0) ? -1.0 : x);
// }

afrl::cmasi::Waypoint* getWaypoint(const std::unique_ptr<afrl::cmasi::MissionCommand>& pMission, int64_t id)
{
    if (pMission)
    {
        const std::vector<afrl::cmasi::Waypoint*>& waypoints = pMission->getWaypointList();

        const auto it_waypoint = std::find_if(waypoints.cbegin(), waypoints.cend(),
            [&](afrl::cmasi::Waypoint* pWaypoint) { return (pWaypoint->getNumber() == id); } );

        if (it_waypoint != waypoints.cend())
        {
            return *it_waypoint;
        }
    }

    return nullptr;
}

bool withinDistance(const VisiLibity::Point& point1, const VisiLibity::Point& point2, double threshold)
{
    return (distance(point1, point2) <= threshold);
}

bool isOrbitType(afrl::cmasi::Waypoint* pWaypoint)
{
    assert(pWaypoint != nullptr);

    std::vector<afrl::cmasi::VehicleAction*>& actions = pWaypoint->getVehicleActionList();

    // NOTE: no consideration given to LoiterType; all loiters are being considered circular
    const auto it_loiter = std::find_if(actions.cbegin(), actions.cend(),
        [&](afrl::cmasi::VehicleAction* pAction) { return afrl::cmasi::isLoiterAction(pAction); } );

    return (it_loiter != actions.cend());
}

afrl::cmasi::LoiterAction* getAssociatedLoiter(afrl::cmasi::Waypoint* pWaypoint)
{
    assert(pWaypoint != nullptr);

    // NOTE: returns first loiter action if more than one exist in the vehicle action list
    std::vector<afrl::cmasi::VehicleAction*>& actions = pWaypoint->getVehicleActionList();

    auto it_loiter = std::find_if(actions.begin(), actions.end(),
        [&](afrl::cmasi::VehicleAction* pAction) { return afrl::cmasi::isLoiterAction(pAction); } );

    if (it_loiter != actions.end())
    {
        return static_cast<afrl::cmasi::LoiterAction*>(*it_loiter);
    }

    return nullptr;
}

VisiLibity::Point convertLocation3DToNorthEast_m(const afrl::cmasi::Location3D* pLocation, uxas::common::utilities::FlatEarth& flatEarth)
{
    assert(pLocation != nullptr);

    double north_m, east_m;
    flatEarth.ConvertLatLong_degToNorthEast_m(pLocation->getLatitude(), pLocation->getLongitude(), north_m, east_m);

    return VisiLibity::Point(north_m, east_m);
}

VisiLibity::Point getNorthEast_m(afrl::cmasi::Waypoint* pWaypoint, uxas::common::utilities::FlatEarth& flatEarth)
{
    assert(pWaypoint != nullptr);

    if (isOrbitType(pWaypoint))
    {
        afrl::cmasi::LoiterAction* pLoiterAction = getAssociatedLoiter(pWaypoint);
        assert(pLoiterAction != nullptr);

        const afrl::cmasi::Location3D* pLocation = pLoiterAction->getLocation();

        if (pLocation != nullptr) // shouldn't ever happen; fallback to waypoint's location
        {
            return convertLocation3DToNorthEast_m(pLocation, flatEarth);
        }
    }

    return convertLocation3DToNorthEast_m(static_cast<const afrl::cmasi::Location3D*>(pWaypoint), flatEarth);
}

bool CheckLineAcceptance(VisiLibity::Point position, VisiLibity::Point previous, VisiLibity::Point current)
{
    return (dot(previous - current, position - current) <= 0.0);
}

bool CheckOrbitAcceptance(afrl::cmasi::Waypoint* pWaypoint, int64_t startTimestamp_ms)
{
    assert(pWaypoint != nullptr);

    const afrl::cmasi::LoiterAction* pLoiterAction = getAssociatedLoiter(pWaypoint);
    assert(pLoiterAction != nullptr);

    const int64_t loiterDuration_ms = pLoiterAction->getDuration();

    if (loiterDuration_ms != -1) // finite duration
    {
        const int64_t currentTimestamp_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();

        if ((currentTimestamp_ms - startTimestamp_ms) >= loiterDuration_ms)
        {
            return true;
        }
    }

    return false;
}

} // namespace

namespace uxas
{
namespace service
{

SteeringService::SteeringService::CreationRegistrar<SteeringService>
    SteeringService::s_registrar(SteeringService::s_registryServiceTypeNames());

SteeringService::SteeringService()
    : ServiceBase(SteeringService::s_typeName(), SteeringService::s_directoryName()) { };

bool SteeringService::configure(const pugi::xml_node& ndComponent)
{
    m_vehicleID = m_entityId;

    if (!ndComponent.attribute(STRING_XML_VEHICLE_ID).empty())
    {
        m_vehicleID = ndComponent.attribute(STRING_XML_VEHICLE_ID).as_uint();
    }
    
    if (!ndComponent.attribute(STRING_XML_ACCEPTANCE_TIME).empty())
    {
        m_acceptanceTimeToArrive_ms = ndComponent.attribute(STRING_XML_ACCEPTANCE_TIME).as_uint(0);
    }
    
    if (!ndComponent.attribute("OverrideRegion").empty())
    {
        m_overrideRegion = true;
        m_operatingRegionDefault = ndComponent.attribute("OverrideRegion").as_uint();
        m_operatingRegion = m_operatingRegionDefault;
    }

    // configureDoubleOptionIfPositive(m_alpha, ndComponent, STRING_XML_ALPHA, 1.0);

    m_courseInf_rad = n_Const::c_Convert::dPiO2();

    if (!ndComponent.attribute(STRING_XML_MAXIMUM_COURSE_ANGLE_DEG).empty())
    {
        const double maxCourse_rad = n_Const::c_Convert::toRadians(ndComponent.attribute(STRING_XML_MAXIMUM_COURSE_ANGLE_DEG).as_double());

        if ((maxCourse_rad > 0.0) && (maxCourse_rad <= n_Const::c_Convert::dPiO2()))
        {
            m_courseInf_rad = maxCourse_rad;
        }
    }

    configureDoubleOptionIfPositive(m_kLine, ndComponent, STRING_XML_K_LINE, 0.01);
    // configureDoubleOptionIfPositive(m_kappaLine, ndComponent, STRING_XML_KAPPA_LINE, 1.0);
    // configureDoubleOptionIfPositive(m_epsilonLine, ndComponent, STRING_XML_EPSILON_LINE, 0.1);

    configureDoubleOptionIfPositive(m_kOrbit, ndComponent, STRING_XML_K_ORBIT, 0.01);
    // configureDoubleOptionIfPositive(m_kappaOrbit, ndComponent, STRING_XML_KAPPA_ORBIT, 1.0);
    // configureDoubleOptionIfPositive(m_epsilonOrbit, ndComponent, STRING_XML_EPSILON_ORBIT, 0.1);

    // TODO: ensure parameterization meets Eq. 13 & Eq. 24
    // TODO: implement relevant options from WaypointPlanManagerService?

    // track all air vehicle configurations
    addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::AirVehicleConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);
    
    addSubscriptionAddress(uxas::common::MessageGroup::PartialAirVehicleState());
    addSubscriptionAddress(afrl::cmasi::AutomationResponse::Subscription);
    addSubscriptionAddress(afrl::cmasi::MissionCommand::Subscription);
    
    // update operating region
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);

    return (true);
}

bool SteeringService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    auto avconfig = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object);
    auto pState = std::dynamic_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object);
    if(avconfig && avconfig->getID() == m_vehicleID)
    {
        // update loiter radius and lead-ahead distance based on configuration
        double g = n_Const::c_Convert::dGravity_mps2();
        double V = avconfig->getNominalSpeed();
        double phi = fabs(avconfig->getNominalFlightProfile()->getMaxBankAngle());
        if(phi < 1.0) phi = 1.0; // bounded away from 0
        double Rmin = V*V/g/tan(phi*n_Const::c_Convert::dDegreesToRadians());
        m_loiterRadius_m = 1.2*Rmin; // 20% bigger than min-turn radius
        m_leadAheadDistance_m = 3.0*m_loiterRadius_m;
        
        if(m_acceptanceTimeToArrive_ms > 0)
        {
            m_acceptanceDistance = m_acceptanceTimeToArrive_ms/1000.0*V;
        }
    }
    else if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
    {
        const auto req = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        if(!req->getSandBoxRequest() && req->getOriginalRequest())
        {
            m_requestToRegionMap[req->getRequestID()] = req->getOriginalRequest()->getOperatingRegion();
        }
        else
        {
            m_requestToRegionMap.erase(req->getRequestID());
        }
    }
    else if (uxas::messages::task::isUniqueAutomationResponse(receivedLmcpMessage->m_object.get()))
    {
        const auto resp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);
        if(resp->getOriginalResponse())
        {
            const std::vector<afrl::cmasi::MissionCommand*> missionCommands = resp->getOriginalResponse()->getMissionCommandList();

            const auto it_mission = std::find_if(missionCommands.cbegin(), missionCommands.cend(),
                [&](const afrl::cmasi::MissionCommand* pMission){ return pMission->getVehicleID() == m_vehicleID; } );

            const auto regionid = m_requestToRegionMap.find(resp->getResponseID());
            
            // if the vehicle is a participant in this request
            if (it_mission != missionCommands.cend())
            {
                m_operatingRegion = m_operatingRegionDefault;
                if(!m_overrideRegion && regionid != m_requestToRegionMap.cend())
                {
                    m_operatingRegion = regionid->second;
                }
            }
            
            // clear out map
            if(regionid != m_requestToRegionMap.cend())
            {
                m_requestToRegionMap.erase(regionid->first);
            }
        }
    }
    else if (afrl::cmasi::isAutomationResponse(receivedLmcpMessage->m_object.get()))
    {
        const auto pResponse = std::static_pointer_cast<afrl::cmasi::AutomationResponse>(receivedLmcpMessage->m_object);
        const std::vector<afrl::cmasi::MissionCommand*> missionCommands = pResponse->getMissionCommandList();

        const auto it_mission = std::find_if(missionCommands.cbegin(), missionCommands.cend(),
            [&](const afrl::cmasi::MissionCommand* pMission){ return pMission->getVehicleID() == m_vehicleID; } );

        if (it_mission != missionCommands.cend())
        {
            reset(*it_mission);
        }
    }
    else if (afrl::cmasi::isMissionCommand(receivedLmcpMessage->m_object.get()))
    {
        const auto pMission = std::static_pointer_cast<afrl::cmasi::MissionCommand>(receivedLmcpMessage->m_object);

        if (pMission->getVehicleID() == m_vehicleID)
        {
            reset(pMission.get());
        }
    }
    else if (pState && pState->getID() == m_vehicleID) // aliased version of AirVehicleState
    {   
        afrl::cmasi::Waypoint* pCurrentWp = getWaypoint(m_pMissionCmd, m_currentWpID);

        if (pCurrentWp != nullptr)
        {
            const afrl::cmasi::Location3D* pLocation = pState->getLocation();

            if (!m_previousLocation)
            {
                m_previousLocation.reset(pLocation->clone());
            }

            uxas::common::utilities::FlatEarth flatEarth;

            // TODO: don't need to calculate at linearization point and can remove identity operations from subsequent calculations
            VisiLibity::Point position_m = convertLocation3DToNorthEast_m(pLocation, flatEarth);
            VisiLibity::Point previous_m = convertLocation3DToNorthEast_m(m_previousLocation.get(), flatEarth);
            VisiLibity::Point current_m = getNorthEast_m(pCurrentWp, flatEarth);

            int64_t nextWpID = pCurrentWp->getNextWaypoint();
            afrl::cmasi::Waypoint* pNextWp = getWaypoint(m_pMissionCmd, nextWpID);

            // from current (target), a non-positive dot-product indicates crossing/acceptance
            bool isWithinAcceptanceDistance = false;
            if(m_acceptanceTimeToArrive_ms > 0 && pCurrentWp->getTurnType() == afrl::cmasi::TurnType::TurnShort)
                isWithinAcceptanceDistance = withinDistance(current_m, position_m, m_acceptanceDistance);
    
            // waypoint acceptance check
            while (!m_isLastWaypoint &&
                   ((!isOrbitType(pCurrentWp) && (CheckLineAcceptance(position_m, previous_m, current_m) || withinDistance(current_m, previous_m, DISTANCE_TRESHOLD_M) || isWithinAcceptanceDistance)) ||
                    (isOrbitType(pCurrentWp) && CheckOrbitAcceptance(pCurrentWp, m_currentStartTimestamp_ms))))
            {
                UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedLmcpMessage - Vehicle Id [", m_vehicleID, "] accepted Waypoint ", m_currentWpID);

                m_previousLocation.reset(pCurrentWp->clone());
                previous_m = current_m;

                if ((pNextWp != nullptr) && (nextWpID != m_currentWpID))
                {
                    m_currentWpID = nextWpID;
                    pCurrentWp = pNextWp;
                    m_currentStartTimestamp_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();

                    current_m = getNorthEast_m(pCurrentWp, flatEarth);

                    nextWpID = pCurrentWp->getNextWaypoint();
                    pNextWp = getWaypoint(m_pMissionCmd, nextWpID);
                }
                else
                {
                    m_isLastWaypoint = true;
                }
            }

            // const double course_rad = n_Const::c_Convert::toRadians(static_cast<double>(pState->getCourse()));
            // const double groundSpeed_mps = static_cast<double>(pState->getGroundspeed());

            double desiredHeading_deg;
            float speed_mps;
            afrl::cmasi::SpeedType::SpeedType speedType;

            if (isOrbitType(pCurrentWp))
            {
                afrl::cmasi::LoiterAction* pLoiterAction = getAssociatedLoiter(pCurrentWp);
                assert(pLoiterAction != nullptr);

                const VisiLibity::Point orbitRelativePosition_m = position_m - current_m;
                const double gamma_rad = atan2(orbitRelativePosition_m.y(), orbitRelativePosition_m.x()); // angular position of uav

                const double d_m = mag(orbitRelativePosition_m); // radial distance of uav

                const double r_m = pLoiterAction->getRadius();
                // const double beta = m_kOrbit / (r_m * (1 + pow(m_kOrbit * (d_m - r_m) / r_m, 2.0)));

                double desiredCourse_rad;
                // const double commandedCourse_deg;

                if (pLoiterAction->getDirection() == afrl::cmasi::LoiterDirection::Clockwise)
                {
                    desiredCourse_rad = gamma_rad + n_Const::c_Convert::dPiO2() + atan(m_kOrbit * (d_m - r_m) / r_m); // Nelson et al., Eq. 17 in clockwise
                }
                else // CounterClockwise
                {
                    // TODO: handle VehicleDefault, for now treating as CounterClockwise
                    desiredCourse_rad = gamma_rad - n_Const::c_Convert::dPiO2() - atan(m_kOrbit * (d_m - r_m) / r_m); // Nelson et al., Eq. 17

                    // TODO: discretized version of Eq. 23, for now using Eq. 17 and assuming autopilot can achieve
                    // commandedCourse_deg = n_Const::c_Convert::toDegrees( course_rad
                    //     + (groundspeed_mps * sin(course_rad - gamma_rad) / (m_alpha * d_m))
                    //     - (beta * groundspeed_mps * cos(course_rad - gamma_rad) / m_alpha)
                    //     - (m_kappaOrbit * sat((course_rad - desiredCourse_rad) / m_epsilonOrbit) / m_alpha)); // Nelson et al., Eq. 23
                }

                desiredHeading_deg = n_Const::c_Convert::dNormalizeAngleDeg(n_Const::c_Convert::toDegrees(desiredCourse_rad));
                speed_mps = pLoiterAction->getAirspeed();
                speedType = afrl::cmasi::SpeedType::Airspeed;
            }
            else // line type
            {
                // handle last waypoint (self-looping or invalid next waypoint) by always considering self on path
                if (m_isLastWaypoint)
                {
                    previous_m = position_m;
                }

                const VisiLibity::Point path_m = current_m - previous_m;
                const double pathAngle_rad = atan2(path_m.y(), path_m.x());
                // const double pathRelativeCourse_rad = n_Const::c_Convert::dNormalizeAngleRad(course_rad - pathAngle_rad);

                // path's normal is in clockwise direction (matches local frame's handedness)
                // NOTE: rotation sign opposite as our point is in NE frame (XY)
                const VisiLibity::Point pathNormal_m = VisiLibity::Point::rotate(VisiLibity::Point::normalize(path_m), n_Const::c_Convert::dPiO2());

                // NOTE: positive distance corresponds to normal's side (clockwise)
                const double y_m = dot(pathNormal_m, position_m - previous_m);
                const double desiredCourse_rad = -2.0 * m_courseInf_rad / n_Const::c_Convert::dPi() * atan(m_kLine * y_m); // Nelson et al., Eq. 8

                // TODO: discretized version of Eq. 12, for now using Eq. 8 and assuming autopilot can achieve
                // const double commandedCourse_deg = n_Const::c_Convert::toDegrees( pathRelativeCourse_rad
                //     - ((m_courseInf_rad * 2.0 * m_kLine * groundSpeed_mps * sin(pathRelativeCourse_rad)) / (m_alpha * n_Const::c_Convert::dPi() * (1.0 + pow(m_kLine * y_m, 2.0))))
                //     - (m_kappaLine * sat((pathRelativeCourse_rad - desiredCourse_rad) / m_epsilonLine) / m_alpha) ); // Nelson et al., Eq. 12

                // Calculations are relative to path so need to add back in to commanded
                desiredHeading_deg = n_Const::c_Convert::dNormalizeAngleDeg(n_Const::c_Convert::toDegrees(desiredCourse_rad + pathAngle_rad));
                speed_mps = pCurrentWp->getSpeed();
                speedType = pCurrentWp->getSpeedType();
            }
#ifdef USE_FLIGHT_DIRECTOR_ACTION
            auto pAction = uxas::stduxas::make_unique<afrl::cmasi::FlightDirectorAction>();
            pAction->setSpeed(speed_mps);
            pAction->setSpeedType(speedType);
            pAction->setHeading(static_cast<float>(desiredHeading_deg)); // true heading in degrees
            pAction->setAltitude(pCurrentWp->getAltitude());
            pAction->setAltitudeType(pCurrentWp->getAltitudeType());
            pAction->setClimbRate(pCurrentWp->getClimbRate());

            auto pCommand = uxas::stduxas::make_unique<afrl::cmasi::VehicleActionCommand>();
            pCommand->setCommandID(getUniqueEntitySendMessageId());
            pCommand->setVehicleID(m_vehicleID);
            pCommand->getVehicleActionList().push_back(pAction.release());
            pCommand->setStatus(afrl::cmasi::CommandStatusType::Approved);

            sendLmcpObjectBroadcastMessage(std::move(pCommand));
#else
            auto safeHeadingAction = uxas::stduxas::make_unique<uxas::messages::uxnative::SafeHeadingAction>();
            safeHeadingAction->setVehicleID(pState->getID());
            safeHeadingAction->setOperatingRegion(m_operatingRegion);
            safeHeadingAction->setLeadAheadDistance(m_leadAheadDistance_m);
            safeHeadingAction->setLoiterRadius(m_loiterRadius_m);
            safeHeadingAction->setDesiredHeading(static_cast<float>(desiredHeading_deg));
            safeHeadingAction->setDesiredHeadingRate(0.0);
            safeHeadingAction->setUseHeadingRate(false);
            safeHeadingAction->setAltitude(pCurrentWp->getAltitude());
            safeHeadingAction->setAltitudeType(pCurrentWp->getAltitudeType());
            safeHeadingAction->setUseAltitude(true);
            safeHeadingAction->setSpeed(speed_mps);
            safeHeadingAction->setUseSpeed(true);
            sendSharedLmcpObjectBroadcastMessage(std::move(safeHeadingAction));
#endif
        }

        // Always send out the corresponding AirVehicleState with its waypoint number and associated task list correctly populated
        pState->setCurrentWaypoint(m_currentWpID);
        auto associatedTasks = pState->getAssociatedTasks();
        associatedTasks.clear();

        if (pCurrentWp != nullptr)
        {
            // Note: only waypoint associated tasks are included, not those from other actions
            associatedTasks = pCurrentWp->getAssociatedTasks();
        }

        sendSharedLmcpObjectBroadcastMessage(pState);
    }

    return false;
}

void SteeringService::reset(const afrl::cmasi::MissionCommand* pMissionCmd)
{
    assert(pMissionCmd != nullptr);

    m_pMissionCmd.reset(pMissionCmd->clone());
    m_currentWpID = m_pMissionCmd->getFirstWaypoint();
    m_currentStartTimestamp_ms = uxas::common::Time::getInstance().getUtcTimeSinceEpoch_ms();
    m_isLastWaypoint = false;
    m_previousLocation.reset(nullptr);
    
    // look for waypoint previous to the "FirstWaypoint" to form original segment to track
    for(auto prev_wp : m_pMissionCmd->getWaypointList())
    {
        if(prev_wp && prev_wp->getNextWaypoint() == m_pMissionCmd->getFirstWaypoint())
        {
            m_previousLocation.reset(prev_wp->clone());
            break;
        }
    }

    UXAS_LOG_DEBUGGING(s_typeName(), "::processReceivedLmcpMessage - Vehicle Id [", m_vehicleID, "received mission command");
}

} // namespace service
} // namespace uxas