// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2018 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_STEERING_SERVICE_H
#define UXAS_STEERING_SERVICE_H

#include "ServiceBase.h"

#include "Constants/Constant_Strings.h"

#include <memory>
#include <unordered_map>

namespace afrl
{
namespace cmasi
{

class Location3D;
class MissionCommand;

} // namespace cmasi
} // namespace afrl

namespace uxas
{
namespace service
{

class SteeringService : public ServiceBase
{
public:
    SteeringService();

    virtual ~SteeringService() { }

    static ServiceBase* create()
    {
        return new SteeringService;
    }

    static const std::string& s_typeName()
    {
        static std::string s_string("SteeringService");
        return s_string;
    };

    static const std::vector<std::string> s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return registryServiceTypeNames;
    };

    static const std::string& s_directoryName()
    {
        static std::string s_string("");
        return s_string;
    };

private:
    SteeringService(const SteeringService&) = delete;
    SteeringService& operator=(const SteeringService&) = delete;

    bool configure(const pugi::xml_node& serviceXmlNode) override;

    bool processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    static ServiceBase::CreationRegistrar<SteeringService> s_registrar;

    void reset(const afrl::cmasi::MissionCommand* pMissionCmd);

    int64_t m_vehicleID;

    std::unique_ptr<afrl::cmasi::MissionCommand> m_pMissionCmd;
    int64_t m_currentWpID = {0};
    int64_t m_currentStartTimestamp_ms;
    bool m_isLastWaypoint;
    
    int64_t m_operatingRegion{0};
    int64_t m_operatingRegionDefault{0};
    bool m_overrideRegion{false};
    std::unordered_map<int64_t, int64_t> m_requestToRegionMap;
    double m_leadAheadDistance_m{1000.0};
    double m_loiterRadius_m{250.0};
    int64_t m_acceptanceTimeToArrive_ms{0};
    double m_acceptanceDistance{0.0};

    std::unique_ptr<afrl::cmasi::Location3D> m_previousLocation;

    // double m_alpha; // constant for first-order approximation

    double m_courseInf_rad; // maximum directed course angle when 'far away' from path
    double m_kLine; // rate of transition between m_courseInf_rad and 0
    // double m_kappaLine;
    // double m_epsilonLine; // width of boundary region around sliding surface

    double m_kOrbit; // rate of transition from gamma-pi to gamma-pi/2
    // double m_kappaOrbit;
    // double m_epsilonOrbit; // width of boundary region around sliding mode
};

} // namespace service
} // namespace uxas

#endif // UXAS_STEERING_SERVICE_H