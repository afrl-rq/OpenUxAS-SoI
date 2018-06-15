// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Task_Base.h
 * Author: steve
 *
 * Created on September 2, 2015, 4:17 PM
 */

#ifndef UXAS_SERVICE_TASK_TASK_SERVICE_BASE_H
#define UXAS_SERVICE_TASK_TASK_SERVICE_BASE_H

#include "ServiceBase.h"
#include "Constants/Convert.h"

#include "avtas/lmcp/Object.h"
#include "afrl/cmasi/AltitudeType.h"
#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/impact/AreaOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/PointOfInterest.h"
#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "uxas/messages/task/TaskImplementationResponse.h"
#include "uxas/messages/task/TaskImplementationRequest.h"
#include "uxas/messages/task/TaskOption.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/route/RoutePlan.h"
#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RoutePlanResponse.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/OperatingRegion.h"
#include <afrl/cmasi/SearchTask.h>

#include "pugixml.hpp"

#include <memory>       //std::shared_ptr
#include <unordered_set>
#include <unordered_map>
#include <map>


namespace uxas
{
namespace service
{
namespace task
{

    /** \class TaskOptionClass
     * 
     * \par The <B><i>TaskOptionClass</i></B> A class that aggregates functionality
     * required to implement TaskOptions.
     * 
     * @n
     */
    class TaskOptionClass
    {
    public:

        /** \brief The <B><i>TaskOptionClass</i></B> constructor. 
         * 
         * @param taskOption is the <B><i>uxas::messages::task::TaskOption</i></B>
         * that is represent by the values stored in this instance class
         */
        TaskOptionClass(std::shared_ptr<uxas::messages::task::TaskOption>& taskOption);

        virtual ~TaskOptionClass() { };
    private:
        /** \brief Copy construction not permitted */
        TaskOptionClass(TaskOptionClass const&) = delete;

        /** \brief Copy assignment operation not permitted */
        void operator=(TaskOptionClass const&) = delete;
    public:
        /** \brief the <B><i>uxas::messages::task::TaskOption</i></B>
         * that is represented by the values stored in this instance class.  */
        std::shared_ptr<uxas::messages::task::TaskOption> m_taskOption;
        /** \brief the <B><i>uxas::messages::task::TaskOption</i></B>
         * used when restarting this task.  */
        std::shared_ptr<uxas::messages::task::TaskOption> m_restartTaskOption;
        /** \brief IDs of the routes the have not yet been received, but are required
         * to construct the option.  */
        std::unordered_set<int64_t> m_pendingRouteIds;
        /** \brief RoutePlans that will be used to implement the option.  */
        std::map<int64_t, std::shared_ptr<uxas::messages::route::RoutePlan>> m_orderedRouteIdVsPlan;
        /** \brief RoutePlan that will be used to implement the option during a restart.  */
        std::shared_ptr<uxas::messages::route::RoutePlan> m_restartRoutePlan;
        /** \brief starting option of the tasks.  */
        static const int64_t m_firstOptionId;
        /** \brief id of the route from the last position to the start of this task option  */
        static const int64_t m_routeIdFromLastTask;  
        /** \brief first id to use for the implementation routes in this task option  */
        ////////////////////////////////////////////////////////////////////////////////////////////////////
        // NOTE: implementation route response IDs are added to the final route in order of the ID from smallest to largest
        // these route IDs are returned in the implementation response
        static const int64_t m_firstImplementationRouteId; // 
        /** \brief IDs of entities that are eligible to perform this option. If
         is this vector is empty, then all entities are eligible*/
        std::vector<int64_t> m_eligibleEntities;
        /** \brief Stores the <B><i>RoutePlanRequest</i></B> that will be used to
         generate route costs for the option*/
        std::shared_ptr<uxas::messages::route::RoutePlanRequest> m_routePlanRequest;
        /** \brief Stores the waypoint ID of the first, implemented, task active 
         * waypoint. This is used to map the option waypoint IDs to the implemented
          waypoint IDs. Added to use when restarting uncompleted tasks. Defaults
         to 'uninitialized' (-1)*/
        int64_t m_firstTaskActiveWaypointID{-1};

        // TASK SPECIFIC PARAMETERS
        /** \brief altitude of the entity (agl?) for this option*/
        double m_altitude_m = 0.0;
        /** \brief speed of the entity (ground speed?) for this option*/
        double m_speed_mps = 0.0;
        /** \brief the heading of the search axis for this option*/
        double m_searchAxisHeading_rad = 0.0;
        /** \brief the gimbal elevation (depression) angle for this option*/
        double m_elevationLookAngle_rad = 0.0;
        /** \brief the distance between search lanes for this option*/
        double m_laneSpacing_m = 0.0;
        /** \brief the distance, based on the sensor footprint, to add to the 
         * beginning, and subtract from the end, to account for the sensor 
         * footprint this option*/
        double m_sensorHorizontalToLeadingEdge_m = 0.0;
    };

    
    /*! \class TaskServiceBase
        \brief A base service that implements storage/functions common to all tasks.

     */
    
    /** \class TaskServiceBase
     * 
     * \par The <B><i>TaskServiceBase</i></B> is a base class that implements 
     * storage/functions common to all tasks.
     * 
     *
     * ASSUMPTIONS:
     *  - can handle one 'UniqueAutomationRequest' at a time
      * 
     * OPERATIONS
     * 1) When an 'EntityConfiguration', ('AirVehicleConfiguration', 'GroundVehicleConfiguration', 
     *  'SurfaceVehicleConfiguration') for an entity listed in the task's eligible 
     *  entities is received, it is stored in 'm_entityConfigurations' and its ID 
     *  is entered into the map 'm_speedAltitudeVsEligibleEntityIds', based on its
     *  nominal speed and altitude.
     * 
     * 2) When an 'UniqueAutomationRequest' is received, call the virtual function 
     *  'buildTaskPlanOptions()'.
     * 
     * 3) When a 'TaskImplementationRequest' is received call the function 
     *  'buildAndSendImplementationRouteRequestBase'.
     * 
     * 4) When a 'UniqueAutomationResponse' is received, save the VehicleIDs for
     *  the vehicles assigned to this task.
     * 
     * 
     * 
     * TASK SPECIFIC VIRTUAL FUNCTIONS:
     * 
     * THE FOLLOWING 5 FUNCTIONS ARE CALLED FROM THE CORRESPONDING VIRTUAL
     * FUNCTIONS FROM 'ServiceBase':
     * 
     *  configureTask(...)
     *  initializeTask(...)
     *  startTask(...)
     *  terminateTask(...)
     *  processReceivedLmcpMessageTask(...)
     * 
     *  activeEntityState(...) the task is active
     *      called each time::
     *      - an 'afrl::cmasi::EntityState' message received
     *      - the entityID, from the message, is found in 'm_assignedVehicleIds'
     *      - this taskID is included in the message's 'AssociatedTasks'
     *  taskComplete(...) the task has just completed
     *      called each time:
     *      - an 'afrl::cmasi::EntityState' message received
     *      - the entityID, from the message, is found in 'm_assignedVehicleIds'
     *      - this taskID is NOT included in the message's 'AssociatedTasks'
     *      - the entityID, from the message, is found in 'm_activeEntities',
     *          indicating that the task was active last time an 'EntityState' 
     *          message was received from this entity.
     * 
     *  buildTaskPlanOptions(...) the task's function that builds the 
     *      'uxas::messages::task::TaskPlanOptions' message. This is a pure 
     *      virtual function and must be overridden by the task.
     *      called each time:
     *          - a 'uxas::messages::task::UniqueAutomationRequest' is received.
     * 
     *  isHandleOptionsRouteResponse(...) overridden by the task to add custom
     *      reponses to 'uxas::messages::route::RoutePlanResponse' messages
     *      (SHOULD BE DEPRECATED ??)
     * 
     *  isBuildAndSendImplementationRouteRequest(...) overridden by the task to 
     *      add custom Implementation Route Planning
     *      (SHOULD BE DEPRECATED ??)
     * 
     *  isProcessTaskImplementationRouteResponse(...)  overridden by the task to 
     *      add custom task Implementation actions
     * 
     *  
     * @n
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
     *  - uxas::messages::task::TaskInitialized - sent out when the task have successfully started.
     *  - uxas::messages::task::TaskActive - sent once each time the task becomes active.
     *  - uxas::messages::task::TaskComplete - sent once each time the task becomes inactive.
     *  - uxas::messages::route::RoutePlanRequest - sent to build the routes necessary to implement the task
     *  - uxas::messages::task::TaskPlanOptions - the options are constructed by the task and sent to the assignment algorithm
     *  - uxas::messages::task::TaskImplementationResponse - the implemented option
     */
    class TaskServiceBase: public ServiceBase
    {
    public:
        /** \brief The <B><i>TaskServiceBase</i></B> constructor. 
         * 
         * @param serviceName is the type of service. This is passed to the
         * <B><i>c_Component_Base</i></B> constructor
         */
        TaskServiceBase(const std::string& typeName,const std::string& directoryName);
        virtual ~TaskServiceBase();
        

    protected:
        /** \brief Copy construction not permitted */
        TaskServiceBase(TaskServiceBase const&) = delete;

        /** \brief Copy assignment operation not permitted */
        void operator=(TaskServiceBase const&) = delete;

        virtual bool configure(const pugi::xml_node& serviceXmlNode) override;
        virtual bool initialize() override;
        virtual bool start() override;
        virtual bool terminate() override;
        virtual bool processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

        virtual bool configureTask(const pugi::xml_node& serviceXmlNode){return(true);};
        virtual bool initializeTask(){return(true);};
        virtual bool startTask(){return(true);};
        virtual bool terminateTask(){return(true);};
        virtual bool processReceivedLmcpMessageTask(std::shared_ptr<avtas::lmcp::Object>& receivedLmcpObject){return(false);};

    protected:

        /** \brief Used to assign values to the different type of routes. A
         * mapping is maintained from <B><i>RoutePlanRequest</i></B> ID to 
         * differentiate type of request made (see m_routeType) */
        enum class RouteTypeEnum
        {
            UNKNOWN = 0,
            OPTION = 1,
            IMPLEMENTATION = 2,
            NUMBER_OF_VALUES = 3
        };

    public: //XML TAG STRINGS
        /** \brief the XML tag used to enclose the options for the task in the 
         * XML configuration string.*/
        const static std::string m_taskOptions_XmlTag;

    protected:

        virtual void activeEntityState(const std::shared_ptr<afrl::cmasi::EntityState>& entityState) { };
        
        virtual void taskComplete() { };

        virtual void buildTaskPlanOptions() = 0;

        /*! \brief user can override this function to provide their own handler for option route responses */
        virtual bool isHandleOptionsRouteResponse(const int64_t& vehicleId, const int64_t& optionId,
                const int64_t& operatingRegion, std::shared_ptr<uxas::messages::route::RoutePlan>& route) {
            return (false);
        };

        virtual bool isBuildAndSendImplementationRouteRequest(const int64_t& optionId,
                const std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& taskImplementationRequest,
                const std::shared_ptr<uxas::messages::task::TaskOption>& taskOption) {
            return (false);
        };

        virtual bool isProcessTaskImplementationRouteResponse(std::shared_ptr<uxas::messages::task::TaskImplementationResponse>& taskImplementationResponse,
                std::shared_ptr<TaskOptionClass>& taskOptionClass,
                int64_t& waypointId, std::shared_ptr<uxas::messages::route::RoutePlan>& route) {
            return (false);
        };

    protected:
        /** \brief Used by children of the base class to perform base class configuration . 
         * 
         * @param ptr_zmqContext is the zeroMQ context
         */
        std::shared_ptr<afrl::cmasi::Task> generateTaskObject(const pugi::xml_node& taskNode);
        std::shared_ptr<afrl::cmasi::EntityConfiguration> generateEntityConfiguration(pugi::xml_node& entityConfigNode);
        void processOptionsRoutePlanResponseBase(const std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse);
        void processImplementationRoutePlanResponseBase(const std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse);
        void buildAndSendImplementationRouteRequestBase(const int64_t& optionId,
                const std::shared_ptr<uxas::messages::task::TaskImplementationRequest>& taskImplementationRequest,
                const std::shared_ptr<uxas::messages::task::TaskOption>& taskOption);
        /*! \brief builds a RouteId, from the taskId and optionId, for use with routes requested by options */
        int64_t getOptionRouteId(const int64_t& OptionId);
        /*! \brief builds a RouteId, from the taskId and m_implementationRouteCount, for use with routes requested for task implementation */
        int64_t getImplementationRouteId(const int64_t& OptionId);
        /*! \brief parses a RouteId, response to find the OptionId */
        int64_t getOptionIdFromRouteId(const int64_t& routeId);
        /*! \brief parses a RouteId, response to find the RouteType (enum) */
        RouteTypeEnum getRouteTypeFromRouteId(const int64_t& routeId);

        
    protected:
        /** \class PairHash
         * 
         * \par The <B><i>PairHash</i></B> is aStruct used to implement  a hash 
         * function that creates a (relatively unique) hash from two double arguments.
         * The hash is used by the <B><i>std::unordered_map</i></B> class to permit
         * the use of <B><i>std::pair</i></B> in the index.
         * 
         * @n
         */
        struct PairHash
        {
            typedef std::pair<double, double> argument_type;
            typedef std::size_t result_type;

            result_type operator()(argument_type const& s) const {
                result_type const h1(std::hash<double>()(s.first));
                result_type const h2(std::hash<double>()(s.second));
                result_type returnValue = h1 ^ (h2 << 1);
                //std::cout << "Hash[" << returnValue << "] s.first[" << s.first << "] s.second[" << s.second << "]" << std::endl;
                return returnValue;
            }
        };

    protected:
        /*! \brief  path to a directory that this task can use to store data */
        std::string m_strSavePath;
        /*! \brief  the task object */
        std::shared_ptr<afrl::cmasi::Task> m_task;
        /*! \brief all entities assigned to this task*/
        std::unordered_set<int64_t> m_assignedVehicleIds;
        /*! \brief the last active task waypoint passed by the vehicle*/
        std::unordered_map<int64_t,int64_t> m_assignedVehicleIdVsLastTaskWaypoint;
        /*! \brief the option that was assigned to the vehicle*/
        std::unordered_map<int64_t,int64_t> m_assignedVehicleIdVsAssignedOptionId;
        /*! \brief  a container for <B><i>TaskOptionClass</i></B>es used to construct
         * task options.
         *  once all the options have been created*/
        std::unordered_map<int64_t, std::shared_ptr<TaskOptionClass> > m_optionIdVsTaskOptionClass;
        /*! \brief  the <B><i>TaskPlanOptions</i></B> object that will be sent out,
         *  once all the options have been created*/
        std::shared_ptr<uxas::messages::task::TaskPlanOptions> m_taskPlanOptions;
        /*! \brief  IDs of all entities declared eligible by the Task, 
         * <B><i>afrl::cmasi::Task::getEligibleEntities()</i></B> with a corresponding 
         * <B><i>EntityConfiguration</i></B>. These are grouped by speed and altitude.*/
        std::unordered_map<std::pair<double, double>, std::vector<int64_t>, PairHash > m_speedAltitudeVsEligibleEntityIds;
        /*! \brief  IDs of all eligible entities, from <B><i>m_speedAltitudeVsEligibleEntityIds</i></B>,
         * requested in an <B><i>AutomationRequest</i></B>. These are grouped by speed and altitude.*/
        std::unordered_map<std::pair<double, double>, std::vector<int64_t>, PairHash > m_speedAltitudeVsEligibleEntityIdsRequested;
        /*! \brief  copy of the latest  <B><i>UniqueAutomationRequest</i></B>*/
        std::unordered_map<int64_t,std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_idVsUniqueAutomationRequest;
        /*! \brief  id of the latest  <B><i>UniqueAutomationRequest</i></B> NOTE: 
         * this is a work around in the process of switching to multiple automation requests*/
        int64_t m_latestUniqueAutomationRequestId{0};
        
        /*! \brief  copy of all known  <B><i>EntityConfiguration</i></B>s*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigurations;
        /*! \brief  copy of all known  <B><i>EntityConfiguration</i></B>s*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityState> > m_entityStates;

        //ROUTING
        /*! \brief map from route IDs to (task, option) IDs */
        std::unordered_map<int64_t, int64_t > m_routeOption;
        /*! \brief map from route IDs to route type */
        std::unordered_map<int64_t, RouteTypeEnum > m_routeType;
        /*! \brief storage for route implementation requests, used to build 
         * <B><i>TaskImplementationResonse</i></B>s  */
        std::unordered_map<int64_t, std::shared_ptr<uxas::messages::task::TaskImplementationRequest>> m_routeIdVsTaskImplementationRequest;
        /** \brief IDs of the <B><i>RoutePlanResponse</i></B>s that have not yet
         * been received, but are required to construct the options.  */
        std::unordered_set<int64_t> m_pendingOptionRouteRequests;
        /** \brief IDs of the <B><i>RoutePlanResponse</i></B>s that have not yet
         * been received, but are required to construct the <B><i>TaskImplementationResonse</i></B>s.  */
        std::unordered_set<int64_t> m_pendingImplementationRouteRequests;
        /*! \brief used to differentiate between routes that transition from the
         * last task to this task, and routes that are part of this task. Note::
         * I've assumed that this is only one of these per implementation route request */
        int64_t m_transitionRouteRequestId{0};
        
        //ACTIVE TASK
        /*! \brief indicates whether the waypoints from the last task to this one 
         * should be added to the active waypoints list (m_taskActiveWaypoints) */
        bool m_isMakeTransitionWaypointsActive{false};
        /*! \brief all entities assigned to this task, that are currently actively
         * performing this task */
        std::unordered_set<int64_t> m_activeEntities;
        
        /*! \brief  all <B><i>AreaOfInterest</i></B> objects. 
         * NOTE: Object received before task creation are only available when 
         * configured in the @ref c_Component_TaskManager*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::AreaOfInterest> > m_areasOfInterest;
        /*! \brief  all <B><i>LineOfInterest</i></B> objects. 
         * NOTE: Object received before task creation are only available when 
         * configured in the @ref c_Component_TaskManager*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::LineOfInterest> > m_linesOfInterest;
        /*! \brief  all <B><i>PointOfInterest</i></B> objects. 
         * NOTE: Object received before task creation are only available when 
         * configured in the @ref c_Component_TaskManager*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::impact::PointOfInterest> > m_pointsOfInterest;
        /*! \brief  the current <B><i>MissionCommand</i></B> for all entities. 
         * NOTE: Object received before task creation are only available when 
         * configured in the @ref c_Component_TaskManager*/
        std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::MissionCommand> > m_currentMissions;

        /*! \brief  all <B><i>KeepInZone</i></B> objects.
        * NOTE: Object received before task creation are only available when
        * configured in the @ref c_Component_TaskManager*/
        std::unordered_map < int64_t, std::shared_ptr<afrl::cmasi::KeepInZone> > m_keepInZones;
        /*! \brief  all <B><i>KeepOutZone</i></B> objects.
        * NOTE: Object received before task creation are only available when
        * configured in the @ref c_Component_TaskManager*/
        std::unordered_map < int64_t, std::shared_ptr<afrl::cmasi::KeepOutZone> > m_keepOutZones;
        /*! \brief  all <B><i>OperatingRegion</i></B> objects.
        * NOTE: Object received before task creation are only available when
        * configured in the @ref c_Component_TaskManager*/
        std::unordered_map < int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_OperatingRegions;

        /*! \brief Map from waypoint Ids from implemented option and final way[point Ids.
         * This map is constructed during 'processImplementationRoutePlanResponseBase' */
        std::unordered_map<int64_t,int64_t> m_optionWaypointIdVsFinalWaypointId;
        
        int64_t m_uniqueRouteRequestId{1};
    };

}; //namespace task
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_TASK_TASK_SERVICE_BASE_H */

