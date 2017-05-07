// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   AssignmentTreeBranchBoundService.cpp
 * Author: steve
 * 
 * Created on August 11, 2016, 6:17 PM
 */


#include "AssignmentTreeBranchBoundService.h"

#include <iostream>     // std::cout, cerr, etc


#define COUT_INFO_MSG(MESSAGE) std::cout << "<>AssignmentTreeBB:" << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>AssignmentTreeBB:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>AssignmentTreeBB:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{

AssignmentTreeBranchBoundService::ServiceBase::CreationRegistrar<AssignmentTreeBranchBoundService>
AssignmentTreeBranchBoundService::s_registrar(AssignmentTreeBranchBoundService::s_registryServiceTypeNames());

AssignmentTreeBranchBoundService::AssignmentTreeBranchBoundService()
: AssignmentTreeBranchBoundBase(AssignmentTreeBranchBoundService::s_typeName(), AssignmentTreeBranchBoundService::s_directoryName()) { };

AssignmentTreeBranchBoundService::~AssignmentTreeBranchBoundService() { };

void AssignmentTreeBranchBoundService::runCalculateAssignment(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites)
{
    std::unique_ptr<c_Node_Base> nodeAssignment(new c_Node_TreeBranchAndBound);
    AssignmentTreeBranchBoundBase::calculateAssignment(std::move(nodeAssignment),assigmentPrerequisites);
}



//////////////////////////////////////////////////////////////////////////
// node function overrides
//////////////////////////////////////////////////////////////////////////

std::unique_ptr<c_Node_Base> c_Node_TreeBranchAndBound::clone()
{
    return (std::unique_ptr<c_Node_Base>(new c_Node_TreeBranchAndBound(*this)));
}

c_Node_TreeBranchAndBound::c_Node_TreeBranchAndBound(const c_Node_TreeBranchAndBound & rhs) //copy constructor
: c_Node_Base(rhs) { };

void c_Node_TreeBranchAndBound::calculateAssignmentCost(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId,
                                                           const int64_t& taskTime_ms, const int64_t& travelTime_ms,
                                                            int64_t& nodeCost, int64_t& evaluationOrderCost)
{
    nodeCost = INT64_MAX / 1000; // this is an error!!
    evaluationOrderCost = nodeCost;

#ifdef AFRL_INTERNAL_ENABLED
    LOG_ERROR("ERROR:: calculateAssignmentCost was called for a  m_assignmentType[", m_assignmentType, "] that was not implemented for this [",AssignmentTreeBranchBoundService::s_typeName(),"] service.");
#endif
    
}


}; //namespace service
}; //namespace uxas
