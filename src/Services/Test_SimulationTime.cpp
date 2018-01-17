// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Test_SimulationTime.h"

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/EntityStateDescendants.h"

#include "UxAS_Time.h"

//#define STRING_XML_NUMBER_PLANS_MAX "NumberPlansMax"


#define COUT_INFO(MESSAGE) std::cout << "<>Test_SimulationTime:" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>Test_SimulationTime:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>Test_SimulationTime:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

namespace uxas
{
namespace service
{
namespace test
{
Test_SimulationTime::ServiceBase::CreationRegistrar<Test_SimulationTime> Test_SimulationTime::s_registrar(Test_SimulationTime::s_registryServiceTypeNames());

Test_SimulationTime::Test_SimulationTime() :
ServiceBase(Test_SimulationTime::s_typeName(), "") 
{
};

Test_SimulationTime::~Test_SimulationTime() { };

bool
Test_SimulationTime::configure(const pugi::xml_node& serviceXmlNode)
{
    bool isSuccess{true};
    
    // ENTITY STATES
    addSubscriptionAddress(afrl::cmasi::EntityState::Subscription);
    std::vector< std::string > childstates = afrl::cmasi::EntityStateDescendants();
    for(auto child : childstates)
        addSubscriptionAddress(child);

    return (isSuccess);
};
    
bool
Test_SimulationTime::initialize()
{
    bool isSuccess{true};
        
    uxas::common::Time::setTimeMode(uxas::common::Time::DISCRETE_TIME);
    uxas::common::Time::getInstance().resetDiscreteTime_ms(); // set start time to 0
    m_discreteTimeInitialized = true;
    
    return (isSuccess);
};

bool
Test_SimulationTime::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    bool isFinished(false);
    auto entityState = std::dynamic_pointer_cast<afrl::cmasi::EntityState>(receivedLmcpMessage->m_object);
    if (entityState)
    {
        uxas::common::Time::getInstance().setDiscreteTime_ms(entityState->getTime());
    }
    return (isFinished);
};


}; //namespace test
}; //namespace service
}; //namespace uxas
