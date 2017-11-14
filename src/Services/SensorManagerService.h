// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_SensorManager.h
 * Author: steve
 *
 * Created on January 26, 2016, 6:17 PM
 */



#ifndef UXAS_SERVICE_SENSOR_MANAGER_SERVICE_H
#define UXAS_SERVICE_SENSOR_MANAGER_SERVICE_H

#include "ServiceBase.h"

#include "afrl/cmasi/EntityConfiguration.h"
#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/task/SensorFootprint.h"

#include <set>
#include <cstdint> // int64_t


namespace uxas
{
namespace service
{


/*! \class SensorManagerService
    \brief A service that constructs sensor footprints, calculates GSDs, determine sensor settings.
 * 
 * Configuration String: 
 *  <Service Type="SensorManagerService" StringToSend="Hello World!" SendPeriod_ms="1000" />
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::RemoveTasks
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::task::SensorFootprintRequests
 * 
 * Sent Messages:
 *  - uxas::messages::task::SensorFootprintResponse
 * 
 */

class SensorManagerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("SensorManagerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName() {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new SensorManagerService;
    };

    SensorManagerService();

    virtual
    ~SensorManagerService();

private:

    static
    ServiceBase::CreationRegistrar<SensorManagerService> s_registrar;

    /** brief Copy construction not permitted */
    SensorManagerService(SensorManagerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(SensorManagerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


public:




public: //virtual





protected:

public:


public:

private:
    void ProcessSensorFootprintRequests(const std::shared_ptr<uxas::messages::task::SensorFootprintRequests>& sensorFootprintRequests);
    void FindSensorFootPrint(const std::shared_ptr<afrl::cmasi::EntityConfiguration>& entityConfiguration,
            const afrl::cmasi::WavelengthBand::WavelengthBand& wavelength, const float& groundSampleDistance,
            const float& aglAltitude, const float& elevationAngle, uxas::messages::task::SensorFootprint* sensorFootprint);
    void CalculateSensorFootprint(const double& horizantalFov_rad, const double& dAspectRatio, const double& dGimbalAngle_rad,
            const double altitudeAgl_m, uxas::messages::task::SensorFootprint* sensorFootprint);

private:
    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_idVsEntityConfiguration;

private:




};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_SENSOR_MANAGER_SERVICE_H */

