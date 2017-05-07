// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   c_Node_TreeBranchAndBound.h
 * Author: steve
 *
 * Created on August 11, 2016, 6:17 PM
 */



#ifndef UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_SERVICE_H
#define UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_SERVICE_H

#include "AssignmentTreeBranchBoundBase.h"

namespace uxas
{
namespace service
{

class c_Node_TreeBranchAndBound : public c_Node_Base
{
public: //constructors/destructors

    c_Node_TreeBranchAndBound() { };

    virtual ~c_Node_TreeBranchAndBound() { };

protected: //member functions - prototypes
    /** brief used by the base class to make copies of this object */
    virtual std::unique_ptr<c_Node_Base> clone() override;
    void calculateAssignmentCost(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId,
                                    const int64_t& taskTime_ms, const int64_t& travelTime_ms,
                                            int64_t& nodeCost, int64_t& evaluationOrderCost) override;

private: // member functions - prototypes

private:
    c_Node_TreeBranchAndBound(const c_Node_TreeBranchAndBound& rhs); //no direct copying
    c_Node_TreeBranchAndBound& operator=(const c_Node_TreeBranchAndBound&) = delete; //no copying
};

/*! \class AssignmentTreeBranchBoundService
 *\brief This service calculates assignments of vehicles to tasks based on cost inputs. 
 * 
 * Configuration String: 
 *  <Service Type="AssignmentTreeBranchBoundService" NumberNodesMaximum="0",CostFunction="MINMAX" />
 * 
 * Options:
 *  - NumberNodesMaximum
 *  - CostFunction
 * 
 * Subscribed Messages:
 *  - uxas::messages::task::UniqueAutomationRequest
 *  - uxas::messages::task::TaskPlanOptions
 *  - uxas::messages::task::AssignmentCostMatrix
 *  - uxas::project::pisr::PSIR_AssignmentType
 * 
 * Sent Messages:
 *  - afrl::cmasi::ServiceStatus
 *  - uxas::messages::task::TaskAssignmentSummary
 * 
 */

class AssignmentTreeBranchBoundService : public AssignmentTreeBranchBoundBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("AssignmentTreeBranchBoundService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
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
        return new AssignmentTreeBranchBoundService;
    };

    AssignmentTreeBranchBoundService();

    virtual
    ~AssignmentTreeBranchBoundService();

    /** brief Copy assignment operation not permitted */
    void operator=(AssignmentTreeBranchBoundService const&) = delete;


public: //virtual
    void runCalculateAssignment(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites) override;

private:
    static ServiceBase::CreationRegistrar<AssignmentTreeBranchBoundService> s_registrar;

    /** brief Copy construction not permitted */
    AssignmentTreeBranchBoundService(AssignmentTreeBranchBoundService const&) = delete;
};
}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_ASSIGNMENT_TREE_BRANCH_BOUND_SERVICE_H */
