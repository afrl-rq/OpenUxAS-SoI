// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DosAttack.h
 * Author: steve
 *
 * Created on May 8, 2017, 5:55 PM
 */

#ifndef UXAS_DOS_ATTACK_H
#define UXAS_DOS_ATTACK_H

#include "afrl/cmasi/VehicleActionCommand.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"
#include <fstream>
#include "afrl/cmasi/MissionCommand.h"
namespace uxas
{
namespace service
{

/*! \class DosAttack
 *\brief This is a basic example of a UxAS service that receives AirVehicleState
 * messages and sends camera pointing messages when videorecord messages are received. 
 * 
 * Configuration String:
 *  <Service Type="DosAttack"/>
 * 
 * Subscribed Messages:
 *  - uxas.messages.uxnative.VideoRecord
 *  - afrl.cmasi.AirVehicleState
 * 
 * Sent Messages:
 *  - afrl.cmasi.GimbalStareAction
 * 
 */

class DosAttack : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="DosAttack". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("DosAttack");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };

    /** \brief If this string is not empty, it is used to create a data 
     * directory to be used by the service. The path to this directory is
     * accessed through the ServiceBase variable m_workDirectoryPath. */
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create()
    {
        return new DosAttack;
    };

    DosAttack();

    virtual
    ~DosAttack();

private:

    static
    ServiceBase::CreationRegistrar<DosAttack> s_registrar;

    /** brief Copy construction not permitted */
    DosAttack(DosAttack const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(DosAttack const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;
    //bool isInitializePlan(std::shared_ptr<afrl::cmasi::MissionCommand>& ptr_MissionCommand);
    void OnSendNewMissionTimer();
//    bool
//    initialize() override;
    bool
    initialize() override;
    
    bool
    start() override;
    
    bool
    terminate() override;
    
    private:
        std::shared_ptr<avtas::lmcp::Object> airVehicleState;
        std::shared_ptr<avtas::lmcp::Object> vehicleActionCommand;
        uint64_t m_sendNewMissionTimerId{0};
        int64_t _timeBetweenMissionCommandsMin_ms = 0;
        int64_t count = 0;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_OFF_ROAD_ATTACK_H */

