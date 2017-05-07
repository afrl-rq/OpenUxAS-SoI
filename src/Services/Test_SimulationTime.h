// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_TEST_SIMULATION_TIME
#define UXAS_TEST_SIMULATION_TIME



#include "ServiceBase.h"

namespace uxas
{
namespace service
{
namespace test
{

/** \class Test_SimulationTime
 * 
 * @par Description:     
 * 
 * Configuration String: 
 * <Service Type="Test_SimulationTime"/>
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::AirVehicleState
 * 
 * Sent Messages:
 *  - NONE
 * 
 */


class Test_SimulationTime : public ServiceBase
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("Test_SimulationTime"); return (s_string); };

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
    create()
    {
        return new Test_SimulationTime;
    };

    Test_SimulationTime();

    virtual
    ~Test_SimulationTime();

private:

    static
    ServiceBase::CreationRegistrar<Test_SimulationTime> s_registrar;

    /** \brief Copy construction not permitted */
    Test_SimulationTime(Test_SimulationTime const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(Test_SimulationTime const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;
    
    bool
    initialize() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

    bool m_discreteTimeInitialized{false};
};

}; //namespace test
}; //namespace service
}; //namespace uxas

#endif /* UXAS_TEST_SIMULATION_TIME */
