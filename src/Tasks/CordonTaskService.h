// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_CordonTask.h
 * Author: derek
 * 
 * Created on March 7, 2016, 4:44 PM
 */

#ifndef UXAS_SERVICE_TASK_CORDON_TASK_SERVICE_H
#define UXAS_SERVICE_TASK_CORDON_TASK_SERVICE_H

#include "TaskServiceBase.h"
#include "UnitConversions.h"

#include "uxas/messages/task/SensorFootprintRequests.h"
#include "uxas/messages/route/RouteRequest.h"
#include "afrl/impact/CordonTask.h"

#include <cstdint> // int64_t
#include <unordered_map>

namespace uxas
{
namespace service
{
namespace task
{

/*! \class CordonTaskService
    \brief A service that implements the IMPACT CordonTask message
 * 
 * Options:
 *  - NONE
 * 
 * Subscribed Messages:
 *  - uxas::messages::route::EgressRouteResponse
 *  - uxas::messages::route::RouteResponse
 *
 * Sent Messages:
 *  - uxas::messages::route::EgressRouteRequest
 * 
 * TASK: Subscribed Messages:
 *  - afrl::cmasi::EntityState
 *  - afrl::cmasi::EntityConfiguration
 *  - afrl::cmasi::AirVehicleState
 *  - afrl::cmasi::AirVehicleConfiguration
 *  - afrl::vehicles::GroundVehicleState
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - afrl::vehicles::SurfaceVehicleState
 *  - afrl::vehicles::SurfaceVehicleConfiguration
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::UniqueAutomationResponse
 *  - uxas::messages::route::RoutePlanResponse
 *  - uxas::messages::task::TaskImplementationRequest
 * 
 * TASK: Sent Messages:
 *  - uxas::messages::task::TaskInitialized
 *  - uxas::messages::task::TaskActive
 *  - uxas::messages::task::TaskComplete
 *  - uxas::messages::route::RoutePlanRequest
 *  - uxas::messages::task::TaskPlanOptions
 *  - uxas::messages::task::TaskImplementationResponse
 * 
 */

class CordonTaskService : public TaskServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("CordonTaskService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName(), "afrl.impact.CordonTask"};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new CordonTaskService;
    };

    CordonTaskService();

    virtual
    ~CordonTaskService();

private:

    static
    ServiceBase::CreationRegistrar<CordonTaskService> s_registrar;

    /** brief Copy construction not permitted */
    CordonTaskService(CordonTaskService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(CordonTaskService const&) = delete;

    bool
    configureTask(const pugi::xml_node& serviceXmlNode) override;

    bool
    processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject) override;

public:
    const double m_defaultElevationLookAngle_rad = 60.0 * n_Const::c_Convert::dDegreesToRadians(); //60 deg down


    virtual void buildTaskPlanOptions() override;

    /** \class PairHash
     * 
     * \par The <B><i>PairHash</i></B> is aStruct used to implement  a hash 
     * function that creates a (relatively unique) hash from two double arguments.
     * The hash is used by the <B><i>std::unordered_map</i></B> class to permit
     * the use of <B><i>std::pair</i></B> in the index.
     * 
     * @n
     */
    struct PairHashInt64
    {
        typedef std::pair<int64_t, int64_t> argument_type;
        typedef std::size_t result_type;

        result_type operator()(argument_type const& s) const
        {
            result_type const h1(std::hash<int64_t>()(s.first));
            result_type const h2(std::hash<int64_t>()(s.second));
            result_type returnValue = h1 ^ (h2 << 1);
            //std::cout << "Hash[" << returnValue << "] s.first[" << s.first << "] s.second[" << s.second << "]" << std::endl;
            return returnValue;
        }
    };

private:

    std::unordered_map<std::pair<int64_t, int64_t>, int64_t, PairHashInt64> m_vehicleIdNodeIdVsOptionId;

    void calculateOption(const std::vector<int64_t>& eligibleEntities,
            afrl::cmasi::Location3D* location, int64_t& locationId, int64_t& optionId);
    std::string calculateCompositionString(std::vector<int64_t>& locationIds, std::vector<int64_t>& vehicleIds);

private:
    std::shared_ptr<afrl::impact::CordonTask> m_cordonTask;

};

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_CORDON_TASK_SERVICE_H */

