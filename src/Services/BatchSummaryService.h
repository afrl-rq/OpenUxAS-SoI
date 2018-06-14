// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_BatchSummary.h
 * Author: derek
 *
 * Created on Oct 25, 2015, 3:56 PM
 */



#ifndef UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H
#define UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H

#include "ServiceBase.h"
#include "afrl/cmasi/CMASI.h"
#include "afrl/impact/IMPACT.h"
#include "uxas/messages/route/ROUTE.h"

#include "visilibity.h"

#include <memory>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <cstdint>
#include "uxas/messages/task/TaskAutomationResponse.h"
#include "uxas/messages/task/TaskAutomationRequest.h"

namespace uxas
{
    namespace service
    {

        /*! \class c_Component_BatchSummary
        \brief A component that incrementally queries the route planner to build
        *   a matrix of plans between all tasks and entity initial points
        */

        class BatchSummaryService : public ServiceBase
        {
        public:

            static const std::string&
                s_typeName() {
                static std::string s_string("BatchSummaryService");
                return (s_string);
            };

            static const std::vector<std::string>
                s_registryServiceTypeNames()
            {
                std::vector<std::string> registryServiceTypeNames = { s_typeName() };
                return (registryServiceTypeNames);
            };

            static const std::string&
                s_directoryName() {
                static std::string s_string("");
                return (s_string);
            };

            static ServiceBase*
                create() {
                return new BatchSummaryService;
            };

            BatchSummaryService();

            virtual
                ~BatchSummaryService();

            static void UpdateSummaryUtil(afrl::impact::VehicleSummary * sum, const std::vector<afrl::cmasi::Waypoint*>::iterator& task_begin, const std::vector<afrl::cmasi::Waypoint*>::iterator& task_end);
            static void UpdateTaskSummariesUtil(std::vector<afrl::impact::TaskSummary*> taskSummaries, std::vector<afrl::cmasi::MissionCommand*> missions);
            static std::shared_ptr<VisiLibity::Polygon> FromAbstractGeometry(afrl::cmasi::AbstractGeometry* geom);
            static bool LinearizeBoundary(afrl::cmasi::AbstractGeometry* boundary, std::shared_ptr<VisiLibity::Polygon>& poly);

        private:

            static
                ServiceBase::CreationRegistrar<BatchSummaryService> s_registrar;

            /** brief Copy construction not permitted */
            BatchSummaryService(BatchSummaryService const&) = delete;

            /** brief Copy assignment operation not permitted */
            void operator=(BatchSummaryService const&) = delete;

            bool
                configure(const pugi::xml_node& serviceXmlNode) override;

            bool
                initialize() override;


            bool
                processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


        private:


            void HandleBatchSummaryRequest(std::shared_ptr<afrl::impact::BatchSummaryRequest>);
            void HandleEgressRouteResponse(std::shared_ptr<uxas::messages::route::EgressRouteResponse>);
            void UpdateVehicleSummary(afrl::impact::VehicleSummary * vehicleSum);
            bool FinalizeBatchRequest(int64_t);
            void HandleTaskAutomationResponse(const std::shared_ptr<messages::task::TaskAutomationResponse>& object);


            // parameters
            bool m_fastPlan{ false };

            // storage
            std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityStates;
            std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigs;
            std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Location3D> > m_towerLocations;
            std::unordered_map<int64_t, std::pair<float, bool> > m_towerRanges;


            int64_t m_responseId = 1; // internal tracking of numerous batch requests
            int64_t m_taskAutomationRequestId = 1;
            std::unordered_map<int64_t, std::list<int64_t>> m_batchSummaryRequestVsTaskAutomation;
            //               response id,             partial response
            std::unordered_map<int64_t, std::shared_ptr<afrl::impact::BatchSummaryResponse> > m_workingResponse;
            std::unordered_map<int64_t, std::shared_ptr<afrl::impact::BatchSummaryRequest> > m_workingRequests;

            std::unordered_map<int64_t, std::shared_ptr<messages::task::TaskAutomationRequest>> m_pendingTaskAutomationRequests;

            std::unordered_map<int64_t, std::shared_ptr<VisiLibity::Polygon> > m_keepOutZones;


        };

    }; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_BATCH_SUMMARY_SERVICE_H */
