// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AssignmentTreeBranchBoundBase.h
 * Author: steve
 *
 * Created on August 31, 2015, 6:17 PM
 */


#ifndef UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_BASE_H
#define UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_BASE_H

#include "Algebra.h"

#include "ServiceBase.h"

#include "uxas/messages/task/UniqueAutomationRequest.h"
#include "uxas/messages/task/AssignmentCostMatrix.h"
#include "uxas/messages/task/TaskPlanOptions.h"
#include "uxas/messages/task/TaskAssignment.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "uxas/project/pisr/AssignmentType.h"
#endif

#include <cstdint> // int64_t
#include <map>

#define MAX_COST_MS (INT64_MAX / 10000)

namespace uxas
{
namespace service
{

///////////////////////////////////////////////////////////////////////////////////////////////////

class c_VehicleInformationStatic
{
public:
    c_VehicleInformationStatic(const int64_t& vehicleId);
    virtual ~c_VehicleInformationStatic() { };
public:
    int64_t getTravelTime_ms(const int64_t& fromId, const int64_t& toId);
    /*! \brief  vehicle specific costs for shortest paths*/
    std::unordered_map<int64_t, std::unique_ptr<std::unordered_map<int64_t, int64_t>>> m_FromIdVsToIdVsTravelTime;
    /*! \brief  this is the maximum mission travel time (ms), -1 -> no maximum travel time*/
    int64_t m_maxVehicleTravelTime_ms = {-1};
protected:
    /*! \brief  vehicle ID*/
    int64_t m_vehicleId = {0};
private:
    /*! @name Private: No Copying*/
    c_VehicleInformationStatic(const c_VehicleInformationStatic& rhs) = delete; //no copying
    c_VehicleInformationStatic operator=(const c_VehicleInformationStatic&) = delete; //no copying
};
///////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////

class c_TaskInformationStatic
{
public:
    c_TaskInformationStatic();
    virtual ~c_TaskInformationStatic() { };
public:
    int64_t getTravelTime_ms(const int64_t& VehicleId);
    /*! \brief  the task cost for each vehicle*/
    std::unordered_map<int64_t, int64_t> m_VehicleIdVsTaskTravelTime;
private:
    /*! @name Private: No Copying*/
    c_TaskInformationStatic(const c_TaskInformationStatic& rhs) = delete; //no copying
    c_TaskInformationStatic operator=(const c_TaskInformationStatic&) = delete; //no copying
};
///////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////

class c_VehicleAssignmentState
{
public:
    c_VehicleAssignmentState(const int64_t& vehicleId);

    virtual ~c_VehicleAssignmentState() { };

    std::unique_ptr<c_VehicleAssignmentState> clone();

public:

    int64_t getLastTaskId() {
        int64_t lastTaskId(m_vehicleId); // if no assignments then the initial vehicle position is the last task
        if (!m_taskAssignments.empty()) {
            lastTaskId = m_taskAssignments.back()->getTaskID();
        }
        return (lastTaskId);
    }
public:
    int64_t m_vehicleId = {0};
    /*! \brief  ordered list of task assignments for this vehicle*/
    std::vector<std::unique_ptr<uxas::messages::task::TaskAssignment>> m_taskAssignments;
    /*! \brief  only add new assignments if this flag is set. .e.g False if max range reached*/
    bool m_isAcceptingNewAssignments = true;
    /*! \brief  this is the sum of the travel times of the current assignments including
     * inter-task travel-times, task-times, and prerequisite-times*/
    int64_t m_travelTimeTotal_ms = {0};

private:
    /*! @name Private: No Copying*/
    c_VehicleAssignmentState(const c_VehicleAssignmentState& rhs); //no direct copying
    c_VehicleAssignmentState& operator=(const c_VehicleAssignmentState&) = delete; //no copying
};
///////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////

class c_StaticAssignmentParameters
{
public:

    enum class CostFunction
    {
        CUMULATIVE,
        MINMAX
    };
public:

    c_StaticAssignmentParameters() { };

    virtual ~c_StaticAssignmentParameters() { };

public:
    std::unordered_map<int64_t, std::unique_ptr<c_VehicleInformationStatic>> m_vehicleIdVsInformation;
    std::unordered_map<int64_t, std::unique_ptr<c_TaskInformationStatic>> m_taskOptionIdVsInformation;
    int64_t m_minimumAssignmentCostCandidate = {INT64_MAX};
    int64_t m_minimumAssignmentTravelTimeCandidate_ms = {INT64_MAX};
    int64_t m_numberNodesVisited = {0};
    int64_t m_numberNodesAdded = {0};
    int64_t m_numberNodesPruned = {0};
    int64_t m_numberNodesRemoved = {0};
    int64_t m_numberCompleteAssignments = {0};

    uxas::common::utilities::CAlgebra algebra; // ALGEBRA:: Algebra class definition

    bool m_isStopCondition = {false};

    int64_t m_numberNodesMaximum = {0};  // default to best-first search
    CostFunction m_CostFunction = {CostFunction::MINMAX};
    int64_t m_assignmentStartTime_ms = {0};

    std::stringstream m_reasonsForNoAssignment;
    
    /*! \brief  these are vehicle assignment parameters that do change during the assignment*/
    std::unordered_map<int64_t, std::unique_ptr< c_VehicleAssignmentState> > m_candidateVehicleIdVsAssignmentState;

private:
    /*! @name Private: No Copying*/
    c_StaticAssignmentParameters(const c_StaticAssignmentParameters& rhs) = delete; //no copying
    c_StaticAssignmentParameters operator=(const c_StaticAssignmentParameters&) = delete; //no copying
};
///////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////

class c_TaskAssignmentState
{
public:
    c_TaskAssignmentState(const int64_t& taskOptionId);

    virtual ~c_TaskAssignmentState() { };

    std::unique_ptr<c_TaskAssignmentState> clone();

public:

    static int64_t getTaskAndOptionId(const int64_t& taskId, const int64_t& optionId) {
        return ((taskId * 100000) + optionId);
    };

    static int64_t getTaskID(const int64_t& taskAndOptionId) {
        return (taskAndOptionId / 100000);
    };

    static int64_t getOptionID(const int64_t& taskAndOptionId) {
        return (taskAndOptionId % 100000);
    };

public:
    /*! \brief  the identification number of this task*/
    int64_t m_taskOptionId = {0};
    /*! \brief  after this time, this task is assumed to be complete (-1 -> unassigned)*/
    int64_t m_taskCompletionTime_ms = {0};

private:
    /*! @name Private: No Copying*/
    c_TaskAssignmentState(const c_TaskAssignmentState& rhs); //no direct copying
    c_TaskAssignmentState& operator=(const c_TaskAssignmentState&) = delete; //no copying
};
///////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////
////////////////////////////////////////////////////

class c_Node_Base
{
public: //constructors/destructors
    
    c_Node_Base();
    virtual ~c_Node_Base();

    c_Node_Base(const c_Node_Base& rhs);
    
public: //member functions - prototypes
    virtual void ExpandNode();
protected: //member functions - prototypes
    virtual std::unique_ptr<c_Node_Base> clone();
    virtual void NodeAssignment(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId, const int64_t& prerequisiteTaskOptionId);
    virtual void calculateAssignmentCost(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId,
                                            const int64_t& taskTime_ms, const int64_t& travelTime_ms,
                                            int64_t& nodeCost, int64_t& evaluationOrderCost){};
    virtual void calculateFinalAssignment(){};                                        

public: // member functions - prototypes
    void PruneChildren();
    void printStatus(const std::string& Message);

private:    // base member functions
    void calculateAssignmentCostBase(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId,
                                            const int64_t& taskTime_ms, const int64_t& travelTime_ms,
                                            int64_t& nodeCost, int64_t& evaluationOrderCost);
    
public:
    /*! \brief  these are assignment parameters that do not change during the assignment*/
    static std::unique_ptr<c_StaticAssignmentParameters> m_staticAssignmentParameters;
    /*! \brief  this flag controls calling the calculateFinalAssignment function only once */
    static bool m_isFinalAssignmentCalculated;
    /*! \brief  these are vehicle assignment parameters that do change during the assignment*/
    std::unordered_map<int64_t, std::unique_ptr< c_VehicleAssignmentState> > m_vehicleIdVsAssignmentState; //available vehicle and their state for this node
    /*! \brief  these are task assignment parameters that do change during the assignment*/
    std::unordered_map<int64_t, std::unique_ptr< c_TaskAssignmentState> > m_taskIdVsAssignmentState; //tasks and their state for this node
#ifdef AFRL_INTERNAL_ENABLED
    /*! \brief  this is used to determine the type of cost calculation to call */
    static uxas::project::pisr::AssignmentType::AssignmentType m_assignmentType;
#endif
    
protected: //member storage
    /*! \brief map of children of this node, sorted by cost */
    std::multimap<int64_t, std::unique_ptr<c_Node_Base> > m_costVsChildren;
    std::vector<int64_t> m_viObjectiveIDs_Assigned;

    // added for information
    int64_t m_vehicleID{0};
    int64_t m_taskOptionID{0};
    
    /*! \brief  this is the travel time of the assignments, including this node and
     *  it's predecessors from the trunk to the current node*/
    int64_t m_travelTimeTotal_ms = {0};
    
    bool m_isPruneable = {true}; //can this node be pruned
    bool m_isLeafNode = {false}; //is this a leaf node

    int64_t m_nodeCost{0};
    
    
private:
    /*! @name Private: No Copying*/
    c_Node_Base& operator=(const c_Node_Base&) = delete; //no copying
};


///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////

/*! \class AssignmentTreeBranchBoundBase
            \brief The base class for services that calculate assignments.
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




class AssignmentTreeBranchBoundBase : public ServiceBase
{
public:

    AssignmentTreeBranchBoundBase(const std::string& serviceType, const std::string& workDirectoryName);

    virtual
    ~AssignmentTreeBranchBoundBase();

private:

    /** brief Copy construction not permitted */
    AssignmentTreeBranchBoundBase(AssignmentTreeBranchBoundBase const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(AssignmentTreeBranchBoundBase const&) = delete;

    bool configure(const pugi::xml_node& serviceXmlNode) override;

    bool start() override;

    bool terminate() override;

    bool processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;

protected: //virtual
    class AssigmentPrerequisites
    {
    public:
        /** brief checks to make sure that all of the parameters 
         * required to generate an assignment are available. */
        bool isAssignmentReady(const bool& isUsingAssignmentTypes);
#ifdef AFRL_INTERNAL_ENABLED        
        void setAssignmentType(const uxas::project::pisr::AssignmentType::AssignmentType& assignmentType)
        {
            m_isNewAssignmentType = true;
            m_assignmentType = assignmentType;
        };
        uxas::project::pisr::AssignmentType::AssignmentType m_assignmentType;
#endif
    public:
        std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> m_uniqueAutomationRequest;
        std::shared_ptr<uxas::messages::task::AssignmentCostMatrix> m_assignmentCostMatrix;
        std::unordered_map<int64_t, std::shared_ptr < uxas::messages::task::TaskPlanOptions>> m_taskIdVsTaskPlanOptions;
        bool m_isNewAssignmentType{false};
    };
    
    /** brief Children classes can override this to perform
     * configuration after the base class is configured. */
    virtual bool configureAssignment(const pugi::xml_node& serviceXmlNode){ return true; };
    /** brief Children classes can override this to
     * perform start up functions */
    virtual bool isStartAssignment(){return(true);};
    /** brief Children classes can override this to
     * perform terminate functions */
    virtual bool isTerminateAssignment(){return(true);};
    /** brief Children classes can override this to handle
     * messages after they are processed by the base class. */
    virtual void processReceivedLmcpMessageAssignment(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage){};
    /** brief this function is called to initialize the algebra functions. */
    virtual bool isInitializeAlgebra(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites);
    /** brief starts the branch and bound assignment from the base class. */
    virtual void runCalculateAssignment(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites);
    /** brief starts the branch and bound assignment. */
    virtual void calculateAssignment(std::unique_ptr<c_Node_Base> nodeAssignment,const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites);
    void sendErrorMsg(std::string& errStr);


protected:
    
    
    bool m_isUsingAssignmentTypes{false};
    std::unordered_map<int64_t,std::shared_ptr<AssigmentPrerequisites> > m_idVsAssigmentPrerequisites;
    int64_t m_numberNodesMaximum = {0}; // default to best-first search
    c_StaticAssignmentParameters::CostFunction m_CostFunction = {c_StaticAssignmentParameters::CostFunction::MINMAX};

};
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_BASE_H */
