// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_AutomationDiagram.h
 * Author: steve
 *
 * Created on February 1, 2016, 6:17 PM
 */



#ifndef UXAS_SERVICE_DATA_AUTOMATION_DIAGRAM_DATA_SERVICE_H
#define UXAS_SERVICE_DATA_AUTOMATION_DIAGRAM_DATA_SERVICE_H

#include "ServiceBase.h"

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/OperatingRegion.h"
#include "afrl/cmasi/AbstractZone.h"

#include "afrl/impact/AreaOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/PointOfInterest.h"

#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/task/SensorFootprint.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"

#include <set>
#include <cstdint> // int64_t


namespace uxas
{
namespace service
{
namespace data
{

/*! \class AutomationDiagramDataService
    \brief A component that constructs sensor footprints, calculates GSDs, determine sensor settings.

 * 
 * Configuration String: 
 * 
 * Options:
 *  - 
 * 
 * Subscribed Messages:
 *  - 
 * 
 * Sent Messages:
 *  - 
 * 
 */


class AutomationDiagramDataService : public ServiceBase
{
public:

    static const std::string&
    s_typeName() {
        static std::string s_string("AutomationDiagramDataService");
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
        static std::string s_string("AutomationDiagramDataService");
        return (s_string);
    };

    static ServiceBase*
    create() {
        return new AutomationDiagramDataService;
    };

    AutomationDiagramDataService();

    virtual
    ~AutomationDiagramDataService();

private:

    static
    ServiceBase::CreationRegistrar<AutomationDiagramDataService> s_registrar;

    /** brief Copy construction not permitted */
    AutomationDiagramDataService(AutomationDiagramDataService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(AutomationDiagramDataService const&) = delete;

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
        void ProcessUniqueAutomationResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>& uniqueAutomationResponse);
        void SavePythonScripts(const std::string & path);

        private:
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_idVsLastEntityState;
        std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_idVsAutomationRequest;
        std::unordered_map<int64_t, int64_t > m_idVsTimeAutomationRequest_ms;
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Task> > m_idVsTask;
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_idVsOperatingRegion;
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::AbstractZone> > m_idVsZone;
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::AreaOfInterest> > m_idVsAreaOfInterest;
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::LineOfInterest> > m_idVsLineOfInterest;
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::PointOfInterest> > m_idVsPointOfInterest;

        std::string m_basePath;


        private:



};

}; //namespace data
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_DATA_AUTOMATION_DIAGRAM_DATA_SERVICE_H */

