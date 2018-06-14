// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_AssignmentTreeBB.cpp
 * Author: steve
 * 
 * Created on September 2, 2015, 6:17 PM
 */


#include "AssignmentTreeBranchBoundBase.h"

#include "TimeUtilities.h"
#include "Constants/Constant_Strings.h"

#include "afrl/cmasi/ServiceStatus.h"
#include "uxas/messages/task/TaskAssignmentSummary.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "uxas/project/pisr/PSIR_AssignmentType.h"
#endif

#include "pugixml.hpp"


#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>     // std::ifstream
#include <cstdint>      //int64_t
#include <memory>       // make_unique
#include <set>       // set


#define STRING_COMPONENT_NAME "AssignmentTreeBB"

#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

#define STRING_XML_NUMBER_NODES_MAXIMUM "NumberNodesMaximum"
#define STRING_XML_COST_FUNCTION "CostFunction"

#define COUT_INFO_MSG(MESSAGE) std::cout << MESSAGE << std::endl;std::cout.flush();
#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "<>AssignmentTreeBB:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "<>AssignmentTreeBB:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();


namespace uxas
{
namespace service
{


bool c_Node_Base::m_isFinalAssignmentCalculated = false;
#ifdef AFRL_INTERNAL_ENABLED
uxas::project::pisr::AssignmentType::AssignmentType c_Node_Base::m_assignmentType{uxas::project::pisr::AssignmentType::MinMaxTime};
#endif

AssignmentTreeBranchBoundBase::AssignmentTreeBranchBoundBase(const std::string& serviceType, const std::string& workDirectoryName)
: ServiceBase(serviceType, workDirectoryName) { };

AssignmentTreeBranchBoundBase::~AssignmentTreeBranchBoundBase() { };

bool AssignmentTreeBranchBoundBase::start()
{
    return (isStartAssignment());
}

bool AssignmentTreeBranchBoundBase::terminate()
{
    return (isTerminateAssignment());
}

bool
AssignmentTreeBranchBoundBase::configure(const pugi::xml_node& ndComponent)

{
    bool bSuccess{true};

    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();

    if (!ndComponent.attribute(STRING_XML_NUMBER_NODES_MAXIMUM).empty())
    {
        m_numberNodesMaximum = ndComponent.attribute(STRING_XML_NUMBER_NODES_MAXIMUM).as_int64();
    }

    if (!ndComponent.attribute(STRING_XML_COST_FUNCTION).empty())
    {
        std::string costFunctionString = ndComponent.attribute(STRING_XML_COST_FUNCTION).value();
        if (costFunctionString == "CUMULATIVE")
        {
            m_CostFunction = c_StaticAssignmentParameters::CostFunction::CUMULATIVE;
        }
        else if (costFunctionString == "MINMAX")
        {
            m_CostFunction = c_StaticAssignmentParameters::CostFunction::MINMAX;
        }
        else
        {
            m_CostFunction = c_StaticAssignmentParameters::CostFunction::MINMAX;
        }
    }

    addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
    addSubscriptionAddress(uxas::messages::task::TaskPlanOptions::Subscription);
    addSubscriptionAddress(uxas::messages::task::AssignmentCostMatrix::Subscription);
#ifdef AFRL_INTERNAL_ENABLED
    addSubscriptionAddress(uxas::project::pisr::PSIR_AssignmentType::Subscription);
#endif

    configureAssignment(ndComponent);

    return (bSuccess);
}

bool
AssignmentTreeBranchBoundBase::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    std::shared_ptr<AssigmentPrerequisites> assigmentPrerequisites;
    if (uxas::messages::task::isUniqueAutomationRequest(receivedLmcpMessage->m_object.get()))
    {
        auto uniqueAutomationRequest = std::static_pointer_cast<uxas::messages::task::UniqueAutomationRequest>(receivedLmcpMessage->m_object);
        if (m_idVsAssigmentPrerequisites.find(uniqueAutomationRequest->getRequestID()) == m_idVsAssigmentPrerequisites.end())
        {
            m_idVsAssigmentPrerequisites.insert(std::make_pair(uniqueAutomationRequest->getRequestID(), std::make_shared<AssigmentPrerequisites>()));
        }
        m_idVsAssigmentPrerequisites[uniqueAutomationRequest->getRequestID()]->m_uniqueAutomationRequest = uniqueAutomationRequest;
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "uniqueAutomationRequest->getRequestID()[", uniqueAutomationRequest->getRequestID(), "]");
        if (m_idVsAssigmentPrerequisites[uniqueAutomationRequest->getRequestID()]->isAssignmentReady(m_isUsingAssignmentTypes))
        {
            assigmentPrerequisites = m_idVsAssigmentPrerequisites[uniqueAutomationRequest->getRequestID()];
            m_idVsAssigmentPrerequisites.erase(uniqueAutomationRequest->getRequestID());
        }
    }
    else if (uxas::messages::task::isTaskPlanOptions(receivedLmcpMessage->m_object.get()))
    {
        auto taskPlanOptions = std::static_pointer_cast<uxas::messages::task::TaskPlanOptions>(receivedLmcpMessage->m_object);
        if (m_idVsAssigmentPrerequisites.find(taskPlanOptions->getCorrespondingAutomationRequestID()) == m_idVsAssigmentPrerequisites.end())
        {
            m_idVsAssigmentPrerequisites.insert(std::make_pair(taskPlanOptions->getCorrespondingAutomationRequestID(), std::make_shared<AssigmentPrerequisites>()));
        }
        m_idVsAssigmentPrerequisites[taskPlanOptions->getCorrespondingAutomationRequestID()]->m_taskIdVsTaskPlanOptions [taskPlanOptions->getTaskID()] = taskPlanOptions;
        if (m_idVsAssigmentPrerequisites[taskPlanOptions->getCorrespondingAutomationRequestID()]->isAssignmentReady(m_isUsingAssignmentTypes))
        {
            assigmentPrerequisites = m_idVsAssigmentPrerequisites[taskPlanOptions->getCorrespondingAutomationRequestID()];
            m_idVsAssigmentPrerequisites.erase(taskPlanOptions->getCorrespondingAutomationRequestID());
        }
    }
    else if (uxas::messages::task::isAssignmentCostMatrix(receivedLmcpMessage->m_object.get()))
    {
        auto assignmentCostMatrix = std::static_pointer_cast<uxas::messages::task::AssignmentCostMatrix>(receivedLmcpMessage->m_object);
        if (m_idVsAssigmentPrerequisites.find(assignmentCostMatrix->getCorrespondingAutomationRequestID()) == m_idVsAssigmentPrerequisites.end())
        {
            m_idVsAssigmentPrerequisites.insert(std::make_pair(assignmentCostMatrix->getCorrespondingAutomationRequestID(), std::make_shared<AssigmentPrerequisites>()));
        }
        m_idVsAssigmentPrerequisites[assignmentCostMatrix->getCorrespondingAutomationRequestID()]->m_assignmentCostMatrix = assignmentCostMatrix;
        if (m_idVsAssigmentPrerequisites[assignmentCostMatrix->getCorrespondingAutomationRequestID()]->isAssignmentReady(m_isUsingAssignmentTypes))
        {
            assigmentPrerequisites = m_idVsAssigmentPrerequisites[assignmentCostMatrix->getCorrespondingAutomationRequestID()];
            m_idVsAssigmentPrerequisites.erase(assignmentCostMatrix->getCorrespondingAutomationRequestID());
        }
    }
#ifdef AFRL_INTERNAL_ENABLED
    else if (uxas::project::pisr::isPSIR_AssignmentType(receivedLmcpMessage->m_object.get()))
    {
        m_isUsingAssignmentTypes = true;
        auto pisrAssignmentType = std::static_pointer_cast<uxas::project::pisr::PSIR_AssignmentType>(receivedLmcpMessage->m_object);
        if (m_idVsAssigmentPrerequisites.find(pisrAssignmentType->getAutomationRequestID()) == m_idVsAssigmentPrerequisites.end())
        {
            m_idVsAssigmentPrerequisites.insert(std::make_pair(pisrAssignmentType->getAutomationRequestID(), std::make_shared<AssigmentPrerequisites>()));
        }
        m_idVsAssigmentPrerequisites[pisrAssignmentType->getAutomationRequestID()]->setAssignmentType(pisrAssignmentType->getAssignmentType());
        if (m_idVsAssigmentPrerequisites[pisrAssignmentType->getAutomationRequestID()]->isAssignmentReady(m_isUsingAssignmentTypes))
        {
            assigmentPrerequisites = m_idVsAssigmentPrerequisites[pisrAssignmentType->getAutomationRequestID()];
            m_idVsAssigmentPrerequisites.erase(pisrAssignmentType->getAutomationRequestID());
        }
        UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "!!! Received an AssigmentType for automation Id [", pisrAssignmentType->getAutomationRequestID(), "]");
    }
#endif
    else
    {
        //CERR_FILE_LINE_MSG("WARNING::AssignmentTreeBranchBoundBase::ProcessMessage: MessageType [" << receivedLmcpMessage->m_object->getLmcpTypeName() << "] not processed.")
    }
    if (assigmentPrerequisites)
    {
        runCalculateAssignment(assigmentPrerequisites);
        c_Node_Base::m_staticAssignmentParameters.reset(new c_StaticAssignmentParameters);
    }

    processReceivedLmcpMessageAssignment(std::move(receivedLmcpMessage));

    return (false); // always false implies never terminating service from here
};

bool AssignmentTreeBranchBoundBase::AssigmentPrerequisites::isAssignmentReady(const bool& isUsingAssignmentTypes)
{
    bool isHavePrerequisites(false);

    /* 1 - do we have an automation request, cost matrix, task  options, and
    are there tasks and vehicles in the automation request */
    bool isAssignmentTypeReady(true);
#ifdef AFRL_INTERNAL_ENABLED
    if(isUsingAssignmentTypes)
    {   isAssignmentTypeReady = false;
        if(m_isNewAssignmentType)
        {
            isAssignmentTypeReady = true;
        }
    }
#endif
    
    if (m_uniqueAutomationRequest && isAssignmentTypeReady && m_assignmentCostMatrix)
    {
        if (!m_uniqueAutomationRequest->getOriginalRequest()->getTaskList().empty())
        {
            //3 - do we have the required task plan options
            for (auto itTaskId = m_uniqueAutomationRequest->getOriginalRequest()->getTaskList().begin();
                    itTaskId != m_uniqueAutomationRequest->getOriginalRequest()->getTaskList().end(); itTaskId++)
            {
                isHavePrerequisites = true;
                if (m_taskIdVsTaskPlanOptions.find(*itTaskId) == m_taskIdVsTaskPlanOptions.end())
                {
                    isHavePrerequisites = false;
                    UXAS_LOG_INFORM_ASSIGNMENT(s_typeName(), "isAssignmentReady:: NO!, Don't Have the options for TaskId[", *itTaskId, "], yet");
                    break;
                }
                else
                {
                    //bool hasFeasibleEntity{false};
                    for (auto& option : m_taskIdVsTaskPlanOptions[*itTaskId]->getOptions())
                    {
                        if (option->getEligibleEntities().empty())
                        {
                            UXAS_LOG_WARN(s_typeName(), "isAssignmentReady:: TaskId[", *itTaskId, "], Option[", option->getOptionID() , "] has no eligible entities");
                        }
                        /*else
                        {
                            hasFeasibleEntity = true;
                        }*/
                    }
                    // TODO: check 'hasFeasibleEntity', if false, then no option has a feasible entity and task cannot be completed.
                    //       Should immediately should return an error reporting that *itTaskId cannot be accomplished as there are
                    //       no eligible vehicles.
                }
            }
        }
    }

    return (isHavePrerequisites);
}

void AssignmentTreeBranchBoundBase::sendErrorMsg(std::string& errStr)
{
    auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
    serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
    auto keyValuePair = new afrl::cmasi::KeyValuePair;
    keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
    keyValuePair->setValue("AssignmentTree: " + errStr);
    serviceStatus->getInfo().push_back(keyValuePair);
    sendSharedLmcpObjectBroadcastMessage(serviceStatus);
}

bool AssignmentTreeBranchBoundBase::isInitializeAlgebra(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites)
{
    bool isSuccess(true);

    std::unordered_map<int64_t, std::string> taskIdVsAlgebraString;

    for (auto itTaskPlanOptions = assigmentPrerequisites->m_taskIdVsTaskPlanOptions.begin();
            itTaskPlanOptions != assigmentPrerequisites->m_taskIdVsTaskPlanOptions.end();
            itTaskPlanOptions++)
    {
        std::string algebraCompositionTaskOptionId;
        std::string compositionString = itTaskPlanOptions->second->getComposition();
        bool isFinished(false);
        while (!isFinished)
        {
            if (!compositionString.empty())
            {
                // 1) find the atomic element ID's
                size_t position = compositionString.find('p');
                if (position != std::string::npos)
                {
                    position++; // move past the 'p'
                    algebraCompositionTaskOptionId += compositionString.substr(0, position); //add the sub-string including the 'p'

                    size_t positionAfterId = std::string::npos;
                    size_t positionSpace = compositionString.find(' ', position);
                    size_t positionParen = compositionString.find(')', position);
                    if ((positionSpace != std::string::npos) && (positionParen != std::string::npos))
                    {
                        if (positionSpace < positionParen)
                        {
                            positionAfterId = positionSpace;
                        }
                        else
                        {
                            positionAfterId = positionParen;
                        }
                    }
                    else if (positionSpace != std::string::npos)
                    {
                        positionAfterId = positionSpace;
                    }
                    else if (positionParen != std::string::npos)
                    {
                        positionAfterId = positionParen;
                    }
                    try
                    {
                        int64_t optionId = std::stoll(compositionString.substr(position, positionAfterId));
                        int64_t taskOptionId = c_TaskAssignmentState::getTaskAndOptionId(itTaskPlanOptions->first, optionId);
                        algebraCompositionTaskOptionId += std::to_string(taskOptionId);
                        // 2) calculate the TaskOptionId and add it to the string
                        compositionString = compositionString.substr(positionAfterId);
                    }
                    catch (std::exception& e)
                    {
                        std::string errMsg = "Exception Encountered while converting the string [" + compositionString.substr(position, positionAfterId) + "] to a number!";
                        UXAS_LOG_ERROR(errMsg);
                        sendErrorMsg(errMsg);
                        isFinished = true;
                        isSuccess = false;
                    }

                }
                else
                {
                    algebraCompositionTaskOptionId += compositionString; // add whats left
                    taskIdVsAlgebraString[itTaskPlanOptions->first] = algebraCompositionTaskOptionId;
                    //                    COUT_FILE_LINE_MSG("TaskId[" << itTaskPlanOptions->first << "] Composition[" << algebraCompositionTaskOptionId << "]")
                    isFinished = true;
                }
            }
            else //if(!compositionString.empty())
            {
                isFinished = true;
            } //if(!compositionString.empty())
        } //while(!isFinished)
    }


    //Construct the requested algebra string    
    std::string algebraString;
    if (!assigmentPrerequisites->m_uniqueAutomationRequest->getOriginalRequest()->getTaskRelationships().empty())
    {
        std::string taskRelationships = assigmentPrerequisites->m_uniqueAutomationRequest->getOriginalRequest()->getTaskRelationships();
        bool isFinished(false);
        while (!isFinished)
        {
            if (!taskRelationships.empty())
            {
                // 1) find the atomic element ID's
                size_t position = taskRelationships.find('p');
                if (position != std::string::npos)
                {
                    algebraString += taskRelationships.substr(0, position); //add the sub-string, don't include the 'p'
                    position++; // move past the 'p'

                    size_t positionAfterId = std::string::npos;
                    size_t positionSpace = taskRelationships.find(' ', position);
                    size_t positionParen = taskRelationships.find(')', position);
                    if ((positionSpace != std::string::npos) && (positionParen != std::string::npos))
                    {
                        if (positionSpace < positionParen)
                        {
                            positionAfterId = positionSpace;
                        }
                        else
                        {
                            positionAfterId = positionParen;
                        }
                    }
                    else if (positionSpace != std::string::npos)
                    {
                        positionAfterId = positionSpace;
                    }
                    else if (positionParen != std::string::npos)
                    {
                        positionAfterId = positionParen;
                    }
                    int64_t taskId = std::stoll(taskRelationships.substr(position, positionAfterId));
                    auto itAlgebraString = taskIdVsAlgebraString.find(taskId);
                    if (itAlgebraString != taskIdVsAlgebraString.end())
                    {
                        algebraString += itAlgebraString->second;
                    }
                    else
                    {
                        std::string errMsg = "Composition not found for Task Id[!" + std::to_string(taskId) + "]";
                        UXAS_LOG_ERROR(errMsg);
                        sendErrorMsg(errMsg);
                        isSuccess = false;
                        isFinished = true;
                    }
                    taskRelationships = taskRelationships.substr(positionAfterId);
                }
                else
                {
                    algebraString += taskRelationships; // add whats left
                    isFinished = true;
                }
            }
            else //if(!compositionString.empty())
            {
                isFinished = true;
            } //if(!compositionString.empty())
        } //while(!isFinished)
    }
    else
    {
        // add all of the requested task/options as "parallel" options
        algebraString += "|(";
        for (auto itOptions = assigmentPrerequisites->m_taskIdVsTaskPlanOptions.begin(); itOptions != assigmentPrerequisites->m_taskIdVsTaskPlanOptions.end(); itOptions++)
        {
            auto itAlgebraString = taskIdVsAlgebraString.find(itOptions->first);
            if (itAlgebraString != taskIdVsAlgebraString.end())
            {
                algebraString += itAlgebraString->second + " ";
            }
            else
            {
                std::string errMsg = "Composition not found for Task Id[!" + std::to_string(itOptions->first) + "]";
                UXAS_LOG_ERROR(errMsg);
                sendErrorMsg(errMsg);
                isSuccess = false;
            }
        }
        algebraString += ")";
    }

    if (isSuccess)
    {
        // find set of unique TaskOption IDs
        std::set<int64_t> uniqueTaskIds;
        for (auto itOptions = assigmentPrerequisites->m_taskIdVsTaskPlanOptions.begin(); itOptions != assigmentPrerequisites->m_taskIdVsTaskPlanOptions.end(); itOptions++)
        {
            for (auto itOption = itOptions->second->getOptions().begin(); itOption != itOptions->second->getOptions().end(); itOption++)
            {
                int64_t taskOptionId = c_TaskAssignmentState::getTaskAndOptionId((*itOption)->getTaskID(), (*itOption)->getOptionID());
                uniqueTaskIds.insert(taskOptionId);
            }
        }
        std::vector<int64_t> taskIds;
        for (auto itId = uniqueTaskIds.begin(); itId != uniqueTaskIds.end(); itId++)
        {
            taskIds.push_back(*itId);
        }

        if (!algebraString.empty())
        {
            if (!c_Node_Base::m_staticAssignmentParameters->algebra.initAtomicObjectives(taskIds))
            {
                //sstreamErrors << "Error:: error encountered while initializing algebra objectives.]\n";
                //errReturn = static_cast<enReturnErrorAssignment> (errReturn | eassignFailed);
                std::string errStr = "Error:: error encountered while initializing algebra objectives.";
                sendErrorMsg(errStr);
                isSuccess = false;
            }
            else if (!c_Node_Base::m_staticAssignmentParameters->algebra.initAlgebraString(algebraString))
            {
                //sstreamErrors << "Error:: error encountered while parsing the algebra string:\n [" << algebraString << "]\n";
                //errReturn = static_cast<enReturnErrorAssignment> (errReturn | eassignFailed);
                std::string errStr = "Error:: error encountered while parsing the algebra string";
                sendErrorMsg(errStr);
                isSuccess = false;
            }
        }
    } //isSuccess
    //COUT_FILE_LINE_MSG("Global Algebra String[" << algebraString << "]")

    return (isSuccess);
}

void AssignmentTreeBranchBoundBase::runCalculateAssignment(const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites)
{
    std::unique_ptr<c_Node_Base> nodeAssignment(new c_Node_Base);
    calculateAssignment(std::move(nodeAssignment), assigmentPrerequisites);
}

void AssignmentTreeBranchBoundBase::calculateAssignment(std::unique_ptr<c_Node_Base> nodeAssignment,
                                                        const std::shared_ptr<AssigmentPrerequisites>& assigmentPrerequisites)
{
    bool isError(false);

    /////////////////////////////////////////////////////////
    //construct the inputs for the assignment algorithm
    /////////////////////////////////////////////////////////

    // re-initialize static storage/parameters
    nodeAssignment->m_staticAssignmentParameters.reset(new c_StaticAssignmentParameters);
    nodeAssignment->m_staticAssignmentParameters->m_CostFunction = m_CostFunction;
    nodeAssignment->m_staticAssignmentParameters->m_numberNodesMaximum = m_numberNodesMaximum;
#ifdef AFRL_INTERNAL_ENABLED
    nodeAssignment->m_assignmentType = assigmentPrerequisites->m_assignmentType;
#endif
    nodeAssignment->m_isFinalAssignmentCalculated = false;

    // ALGEBRA:: Initialization
    isError = !isInitializeAlgebra(assigmentPrerequisites);

    if (!isError)
    {
        for (auto itOptions = assigmentPrerequisites->m_taskIdVsTaskPlanOptions.begin(); itOptions != assigmentPrerequisites->m_taskIdVsTaskPlanOptions.end(); itOptions++)
        {
            for (auto itOption = itOptions->second->getOptions().begin(); itOption != itOptions->second->getOptions().end(); itOption++)
            {
                int64_t taskOptionId = c_TaskAssignmentState::getTaskAndOptionId((*itOption)->getTaskID(), (*itOption)->getOptionID());
                if (nodeAssignment->m_staticAssignmentParameters->m_taskOptionIdVsInformation.find(taskOptionId) == nodeAssignment->m_staticAssignmentParameters->m_taskOptionIdVsInformation.end())
                {
                    nodeAssignment->m_staticAssignmentParameters->m_taskOptionIdVsInformation[taskOptionId] = std::unique_ptr<c_TaskInformationStatic>(new c_TaskInformationStatic());
                }
                for (auto itObjVehicle = (*itOption)->getEligibleEntities().begin(); itObjVehicle != (*itOption)->getEligibleEntities().end(); itObjVehicle++)
                {
                    nodeAssignment->m_staticAssignmentParameters->m_taskOptionIdVsInformation[taskOptionId]->m_VehicleIdVsTaskTravelTime[*itObjVehicle] = (*itOption)->getCost();
                }
            }
        }

        for (auto itTaskOptionCost = assigmentPrerequisites->m_assignmentCostMatrix->getCostMatrix().begin();
                itTaskOptionCost != assigmentPrerequisites->m_assignmentCostMatrix->getCostMatrix().end();
                itTaskOptionCost++)
        {
            auto vehicleId = (*itTaskOptionCost)->getVehicleID();
            auto fromId = c_TaskAssignmentState::getTaskAndOptionId((*itTaskOptionCost)->getIntialTaskID(), (*itTaskOptionCost)->getIntialTaskOption());
            fromId = (fromId == 0) ? (vehicleId) : (fromId);
            auto toId = c_TaskAssignmentState::getTaskAndOptionId((*itTaskOptionCost)->getDestinationTaskID(), (*itTaskOptionCost)->getDestinationTaskOption());
            auto travelCost = (*itTaskOptionCost)->getTimeToGo();

            // instantiate new vehicle assignment classes if necessary
            if (nodeAssignment->m_vehicleIdVsAssignmentState.find(vehicleId) == nodeAssignment->m_vehicleIdVsAssignmentState.end())
            {
                nodeAssignment->m_vehicleIdVsAssignmentState[vehicleId] = std::unique_ptr<c_VehicleAssignmentState>(new c_VehicleAssignmentState(vehicleId));
            }
            if (nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation.find(vehicleId) == nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation.end())
            {
                nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation[vehicleId] = std::unique_ptr<c_VehicleInformationStatic>(new c_VehicleInformationStatic(vehicleId));
            }
            if (nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation[vehicleId]->m_FromIdVsToIdVsTravelTime.find(fromId) == nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation[vehicleId]->m_FromIdVsToIdVsTravelTime.end())
            {
                nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation[vehicleId]->m_FromIdVsToIdVsTravelTime[fromId] = std::unique_ptr<std::unordered_map<int64_t, int64_t >> (new std::unordered_map<int64_t, int64_t>);
            }
            nodeAssignment->m_staticAssignmentParameters->m_vehicleIdVsInformation[vehicleId]->m_FromIdVsToIdVsTravelTime[fromId]->operator[](toId) = travelCost;
        }

        //TODO:: need to calculate "m_maximumVehicleCost" for the c_VehicleCostsStatic's map


        /////////////////////////////////////////////////////////
        /////////  RUN THE ASSIGNMENT ALGORITHM
        /////////////////////////////////////////////////////////
        /////////////////////////////////////////////////////////////////////////////////////////////////////////
        // use errRunAllocation to run the allocation algorithm. 
        //  Note: (1)load Objectives and vehicles (2) run allocation algorithm (3)  the function GetWaypoints_m or GetWaypoints_LatLong_rad to return the results
        /////////////////////////////////////////////////////////////////////////////////////////////////////////
        nodeAssignment->m_staticAssignmentParameters->m_assignmentStartTime_ms = uxas::common::utilities::c_TimeUtilities::getTimeNow_ms();
        nodeAssignment->ExpandNode();
        nodeAssignment->printStatus("INFO::FINAL:  ");

        if (nodeAssignment->m_staticAssignmentParameters->m_numberCompleteAssignments <= 0)
        {
            auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
            serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Error);
            auto keyValuePair = new afrl::cmasi::KeyValuePair;
            keyValuePair->setKey(std::string("No UniqueAutomationResponse"));
            keyValuePair->setValue(std::string("Assignment not found: ") + nodeAssignment->m_staticAssignmentParameters->m_reasonsForNoAssignment.str());
            serviceStatus->getInfo().push_back(keyValuePair);
            keyValuePair = nullptr;
            sendSharedLmcpObjectBroadcastMessage(serviceStatus);
            std::cout << "RoutesNotFound:: " << std::endl << nodeAssignment->m_staticAssignmentParameters->m_reasonsForNoAssignment.str() << std::endl << std::endl;
        }
        else
        {
            auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
            serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
            auto keyValuePair = new afrl::cmasi::KeyValuePair;
            keyValuePair->setKey(std::string("AssignmentComplete"));
            serviceStatus->getInfo().push_back(keyValuePair);
            keyValuePair = nullptr;
            sendSharedLmcpObjectBroadcastMessage(serviceStatus);
        }


        /////////////////////////////////////////////////////////
        /////////  Return the results
        /////////////////////////////////////////////////////////
        if (!nodeAssignment->m_staticAssignmentParameters->m_candidateVehicleIdVsAssignmentState.empty())
        {
            auto taskAssignmentSummary = std::make_shared<uxas::messages::task::TaskAssignmentSummary>();

            taskAssignmentSummary->setOperatingRegion(assigmentPrerequisites->m_uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion());
            taskAssignmentSummary->setCorrespondingAutomationRequestID(assigmentPrerequisites->m_uniqueAutomationRequest->getRequestID());

            for (auto itVehicleAssignments = nodeAssignment->m_staticAssignmentParameters->m_candidateVehicleIdVsAssignmentState.begin();
                    itVehicleAssignments != nodeAssignment->m_staticAssignmentParameters->m_candidateVehicleIdVsAssignmentState.end();
                    itVehicleAssignments++)
            {
                for (auto itTaskAssignment = itVehicleAssignments->second->m_taskAssignments.begin();
                        itTaskAssignment != itVehicleAssignments->second->m_taskAssignments.end();
                        itTaskAssignment++)
                {
                    taskAssignmentSummary->getTaskList().push_back((*itTaskAssignment)->clone());
                }
            }
            auto newMessage = std::static_pointer_cast<avtas::lmcp::Object>(taskAssignmentSummary);
            sendSharedLmcpObjectBroadcastMessage(newMessage);
            UXAS_LOG_INFORM("ASSIGNMENT COMPLETE!");
        }
        else
        {
            std::string errMsg = "ASSIGNMENT FAILED!";
            UXAS_LOG_INFORM(errMsg);
            sendErrorMsg(errMsg);
        }    

    } //if(!isError)
    nodeAssignment.reset();
} //void AssignmentTreeBranchBoundBase::CalculateAssignment()

///////////////////////////////////////////////////////////////////////////////////////////////////

c_VehicleInformationStatic::c_VehicleInformationStatic(const int64_t & vehicleId)
: m_vehicleId(vehicleId) { };

int64_t c_VehicleInformationStatic::getTravelTime_ms(const int64_t& fromId, const int64_t & toId)
{
    int64_t returnTravelTime_ms(-1); // LengthOfTime_ms not found
    auto itToCost = m_FromIdVsToIdVsTravelTime.find(fromId);
    if (itToCost != m_FromIdVsToIdVsTravelTime.end())
    {
        auto itTravelTime = itToCost->second->find(toId);
        if (itTravelTime != itToCost->second->end())
        {
            returnTravelTime_ms = itTravelTime->second;
        }
    }
    return (returnTravelTime_ms);
};

c_TaskInformationStatic::c_TaskInformationStatic() { }

int64_t c_TaskInformationStatic::getTravelTime_ms(const int64_t & VehicleId)
{
    int64_t returnCost_ms(-1); // cost not found
    auto itCost = m_VehicleIdVsTaskTravelTime.find(VehicleId);
    if (itCost != m_VehicleIdVsTaskTravelTime.end())
    {
        returnCost_ms = itCost->second;
    }
    return (returnCost_ms);
};

c_VehicleAssignmentState::c_VehicleAssignmentState(const int64_t & vehicleId)
: m_vehicleId(vehicleId) { };

std::unique_ptr<c_VehicleAssignmentState> c_VehicleAssignmentState::clone()
{
    return (std::unique_ptr<c_VehicleAssignmentState>(new c_VehicleAssignmentState(*this)));
}

c_VehicleAssignmentState::c_VehicleAssignmentState(const c_VehicleAssignmentState & rhs)
{
    m_vehicleId = rhs.m_vehicleId;
    m_isAcceptingNewAssignments = rhs.m_isAcceptingNewAssignments;
    m_travelTimeTotal_ms = rhs.m_travelTimeTotal_ms;
    for (auto itAssignment = rhs.m_taskAssignments.begin(); itAssignment != rhs.m_taskAssignments.end(); itAssignment++)
    {
        m_taskAssignments.push_back(std::unique_ptr<uxas::messages::task::TaskAssignment>((*itAssignment)->clone()));
    }
}

c_TaskAssignmentState::c_TaskAssignmentState(const int64_t & taskOptionId)
: m_taskOptionId(taskOptionId) { };

std::unique_ptr<c_TaskAssignmentState> c_TaskAssignmentState::clone()
{
    return (std::unique_ptr<c_TaskAssignmentState>(new c_TaskAssignmentState(*this)));
}

c_TaskAssignmentState::c_TaskAssignmentState(const c_TaskAssignmentState & rhs)
{
    m_taskOptionId = rhs.m_taskOptionId;
    m_taskOptionId = rhs.m_taskOptionId;
}


std::unique_ptr<c_StaticAssignmentParameters> c_Node_Base::m_staticAssignmentParameters(new c_StaticAssignmentParameters);

c_Node_Base::c_Node_Base() //this is used for the root node
{
    m_staticAssignmentParameters->m_numberNodesVisited++;
    //CERR_FILE_LINE_MSG("m_staticAssignmentParameters->m_numberNodesAdded[" << m_staticAssignmentParameters->m_numberNodesAdded << "]")
}

c_Node_Base::~c_Node_Base()
{
    m_staticAssignmentParameters->m_numberNodesRemoved++;
}

std::unique_ptr<c_Node_Base> c_Node_Base::clone()
{
    return (std::unique_ptr<c_Node_Base>(new c_Node_Base(*this)));
}

//copy constructor

c_Node_Base::c_Node_Base(const c_Node_Base & rhs) //copy constructor
: m_travelTimeTotal_ms(rhs.m_travelTimeTotal_ms),
m_isPruneable(rhs.m_isPruneable),
m_isLeafNode(rhs.m_isLeafNode)
{
    m_staticAssignmentParameters->m_numberNodesVisited++;
    for (auto itVehicleAssignmentState = rhs.m_vehicleIdVsAssignmentState.begin();
            itVehicleAssignmentState != rhs.m_vehicleIdVsAssignmentState.end();
            itVehicleAssignmentState++)
    {
        m_vehicleIdVsAssignmentState[itVehicleAssignmentState->first] = itVehicleAssignmentState->second->clone();
    }
    for (auto itTaskAssignmentState = rhs.m_taskIdVsAssignmentState.begin();
            itTaskAssignmentState != rhs.m_taskIdVsAssignmentState.end();
            itTaskAssignmentState++)
    {
        m_taskIdVsAssignmentState[itTaskAssignmentState->first] = itTaskAssignmentState->second->clone();
    }
    m_viObjectiveIDs_Assigned = rhs.m_viObjectiveIDs_Assigned;
    // do not copy children !!!!!!!!
};

void c_Node_Base::printStatus(const std::string& Message)
{
    double timeSinceStart_s = static_cast<double> (uxas::common::utilities::c_TimeUtilities::getTimeNow_ms() -
            m_staticAssignmentParameters->m_assignmentStartTime_ms) / 1000.0;
    UXAS_LOG_INFORM(Message
                  , "timeSinceStart_s[" , timeSinceStart_s
                  , "] m_vehicleID[" , m_vehicleID
                  , "] cost[" , m_staticAssignmentParameters->m_minimumAssignmentCostCandidate
                  , "] numberNodesVisited[" , m_staticAssignmentParameters->m_numberNodesVisited
                  , "] numberNodesRemoved[" , m_staticAssignmentParameters->m_numberNodesRemoved
                  , "] Number Current Nodes[" , (m_staticAssignmentParameters->m_numberNodesVisited - m_staticAssignmentParameters->m_numberNodesRemoved)
                  , "] numberNodesAdded[" , m_staticAssignmentParameters->m_numberNodesAdded
                  , "] numberNodesPruned[" , m_staticAssignmentParameters->m_numberNodesPruned
                  , "]" );
    UXAS_LOG_INFORM_ASSIGNMENT("timeSinceStart_s[", timeSinceStart_s,
                                  "] cost[", m_staticAssignmentParameters->m_minimumAssignmentCostCandidate,
                                  "] numberNodesVisited[", m_staticAssignmentParameters->m_numberNodesVisited, "]");
}

void c_Node_Base::ExpandNode()
{
    //////////////////////////////////////////////////////////////////////////////////
    // check assignment viability and find lower bound on costs of child nodes
    //////////////////////////////////////////////////////////////////////////////////
    bool bTaskAvailable = false; //if there are no tasks to do then this is the final assignment node

    // investigate child nodes
    std::vector<int64_t> vectorOfNextObjectiveIDs;
    m_staticAssignmentParameters->algebra.searchNext(m_viObjectiveIDs_Assigned, vectorOfNextObjectiveIDs);

    for (auto itObjectiveID = vectorOfNextObjectiveIDs.begin(); itObjectiveID != vectorOfNextObjectiveIDs.end(); itObjectiveID++) // ALGEBRA:: New for loop
    {
        bTaskAvailable = true;

        //TODO:: find the prerequsite task
        int64_t prerequisiteTaskOptionId(-1);
        //searchPred (const v_action_t &executedAtomicObjectives, int AtomicObjectiveIn)

        for (auto itVehicleAssignmentState = m_vehicleIdVsAssignmentState.begin(); itVehicleAssignmentState != m_vehicleIdVsAssignmentState.end(); itVehicleAssignmentState++)
        {
            NodeAssignment(itVehicleAssignmentState->second, *itObjectiveID, prerequisiteTaskOptionId);
            if (!itVehicleAssignmentState->second->m_isAcceptingNewAssignments)
            {
                UXAS_LOG_INFORM("Vehicle ID[" + std::to_string(itVehicleAssignmentState->first) + "] is finished!");
            }
        }
    } //for(V_INT_IT_t itObjectiveID = vectorOfNextObjectiveIDs.begin(); itObjectiveID != vectorOfNextObjectiveIDs.end(); itObjectiveID++)

    if (!m_staticAssignmentParameters->m_isStopCondition)
    {
        //if there are valid assignments and there are child nodes, then expand them 
        //if (bTaskAvailable && bVehicleAvailable)
        if (!m_costVsChildren.empty())
        {
            //////////////////////////////////////////////////////////////////////////////////
            //expand the children
            //////////////////////////////////////////////////////////////////////////////////
#ifdef STEVETEST
            std::cout << std::endl << "<>AssignmentTreeBB:m_costVsChildren [" << m_costVsChildren.size() << "] # Previous Assignments[" << m_viObjectiveIDs_Assigned.size() << "]";
#endif  //#ifdef STEVETEST
#ifdef STEVETEST
            for (auto& itChild : m_costVsChildren)
            {
                std::cout << " (" << itChild.second->m_vehicleID << ", " << itChild.second->m_taskOptionID << ", " << itChild.first << ")";
            }
            std::cout << "]" << std::endl;
            std::cout.flush();
#endif  //#ifdef STEVETEST

            for (auto itChild = m_costVsChildren.begin(); itChild != m_costVsChildren.end(); itChild++)
            {
                // other children may have found lower costs or a stop condition
                if ((itChild->second->m_nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate) && !m_staticAssignmentParameters->m_isStopCondition)
                {
#ifdef STEVETEST
                    std::cout << "  #Prev[" << m_viObjectiveIDs_Assigned.size() << "](" << itChild->second->m_vehicleID << ", "
                            << itChild->second->m_taskOptionID << ", " << itChild->first << ", " << itChild->second->m_nodeCost << ")";
#endif  //#ifdef STEVETEST
                    itChild->second->ExpandNode();
                }
                else
                {
                    itChild->second->m_isPruneable = true;
                }
            } //for(L_CHILD_IT_t itChild=lnodeitGe ......
            PruneChildren();
        }
        else //if(((bTaskAvailable)&&(bVehicleAvailable))
        {
            // have all of the tasks been accounted for?
            if (!bTaskAvailable)
            {
                // check to see if this leaf node is better than the candidate optimal
                if (m_nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate)
                {
                    ////////////////  NEW LEAF NODE  ///////////////////////////
                    // this is the new minimum (feasible) leaf node
                    m_isLeafNode = true;
                    m_staticAssignmentParameters->m_numberCompleteAssignments++;
                    m_staticAssignmentParameters->m_minimumAssignmentCostCandidate = m_nodeCost;
                    m_staticAssignmentParameters->m_candidateVehicleIdVsAssignmentState.clear();
                    for (auto itVehicleAssignment = m_vehicleIdVsAssignmentState.begin(); itVehicleAssignment != m_vehicleIdVsAssignmentState.end(); itVehicleAssignment++)
                    {
                        m_staticAssignmentParameters->m_candidateVehicleIdVsAssignmentState[itVehicleAssignment->first] = itVehicleAssignment->second->clone();
                    }
                    printStatus("INFO::NEW LEAF: ");
                }
                else //if (m_nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate)
                {
                    //COUT_INFO_MSG("(!bTaskAvailable)")
                    // this is a node that is not optimal and needs to be pruned
                    m_isLeafNode = true;
                    m_isPruneable = true;
                } //if (m_nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate)
            }
            else //if(!bTaskAvailable)
            {
                //COUT_INFO_MSG("(bTaskAvailable && !bVehicleAvailable)")
                // not all of the tasks were assigned!!!!!
                //TODO:: let them know why this set of assignments didn't work???
                // this is a node that is not optimal and needs to be pruned
                m_isLeafNode = true;
                m_isPruneable = true;
            } //if(!bTaskAvailable)
        } //if(((bTaskAvailable)&&(bVehicleAvailable)))
    }

    if (m_staticAssignmentParameters->m_isStopCondition)
    {
        // got a stop condition, time to get out
        if (!m_isFinalAssignmentCalculated)
        {
            //COUT_INFO_MSG("calculateFinalAssignment()!")
            calculateFinalAssignment();
            m_isFinalAssignmentCalculated = true;
        }
        // dump the children
        m_costVsChildren.clear();

    } //if(m_staticAssignmentParameters->m_isStopCondition)
} //void CNode::ExpandNode(

void c_Node_Base::PruneChildren()
{
    bool isPruneParent(true); //if any of the nodes below this are not pruned then don't allow this one to be pruned

    if (!m_costVsChildren.empty())
    {
        for (auto itChild = m_costVsChildren.begin(); itChild != m_costVsChildren.end(); itChild++)
        {
            itChild->second->PruneChildren();
        }
        while (1)
        {
            auto itChild = m_costVsChildren.begin();
            for (; itChild != m_costVsChildren.end(); itChild++)
            {
                if (itChild->second->m_isPruneable)
                {
                    m_costVsChildren.erase(itChild);
                    itChild = m_costVsChildren.begin();
                    m_staticAssignmentParameters->m_numberNodesPruned++;
                    break;
                }
                else
                {
                    isPruneParent = false;
                }

            }
            if (itChild == m_costVsChildren.end())
            {
                break;
            }
        } //while(1)
    }
    else if ((m_nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate) && m_isLeafNode)
    {
        isPruneParent = false;
    }
    m_isPruneable = isPruneParent;
}

void c_Node_Base::NodeAssignment(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId, const int64_t & prerequisiteTaskOptionId)
{
    if (((m_staticAssignmentParameters->m_numberNodesVisited % 100000) == 0) && (m_staticAssignmentParameters->m_numberNodesVisited > 0))
    {
        printStatus("INFO::UPDATE: ");
    }

    if ((m_staticAssignmentParameters->m_numberNodesMaximum >= 0) &&
            (m_staticAssignmentParameters->m_numberNodesVisited >= m_staticAssignmentParameters->m_numberNodesMaximum) &&
            (m_staticAssignmentParameters->m_numberCompleteAssignments > 0))
    {
        m_staticAssignmentParameters->m_isStopCondition = true;
    }

    bool isError(false);

    int64_t vehicleId = vehicleAssignmentState->m_vehicleId;
    // find the prerequisite cost, if there is one
    int64_t prerequisiteTime_ms(0);
    if (prerequisiteTaskOptionId > 0)
    {
        auto itTaskAssignmentState = m_taskIdVsAssignmentState.find(prerequisiteTaskOptionId);
        if (itTaskAssignmentState != m_taskIdVsAssignmentState.end())
        {
            prerequisiteTime_ms = itTaskAssignmentState->second->m_taskCompletionTime_ms;
        }
        else
        {
	UXAS_LOG_ERROR("ASSIGNMENT_ERROR:: required prerequisite TaskOptionId[", prerequisiteTaskOptionId, "] not found");
            m_staticAssignmentParameters->m_reasonsForNoAssignment << "ASSIGNMENT_ERROR:: required prerequisite TaskOptionId[" << prerequisiteTaskOptionId << "] not found!" << std::endl;
            isError = true;
        }
    }

    auto itVehicleInformation = m_staticAssignmentParameters->m_vehicleIdVsInformation.find(vehicleId);
    auto itTaskOptionInformation = m_staticAssignmentParameters->m_taskOptionIdVsInformation.find(taskOptionId);

    /* NOTE:: local travel time variables
     * taskTime_ms - the time required to perform the task
     * travelTime_ms - the travel time between the end of the last task (vehicle 
     *      starting location) to the start of the the current task.
     * travelTimeTotalToBegin_ms - the total travel time from the vehicle's starting position
     *      to the beginning of the current task, including all previous task times.
     * travelTimeTotalToEnd_ms - the total travel time from the vehicle's starting position
     *      to the end of the current task, including all task times.
     * */
    if (!isError &&
            (itVehicleInformation != m_staticAssignmentParameters->m_vehicleIdVsInformation.end()) &&
            (itTaskOptionInformation != m_staticAssignmentParameters->m_taskOptionIdVsInformation.end()) &&
            (vehicleAssignmentState->m_isAcceptingNewAssignments))
    {
        int64_t taskTime_ms = itTaskOptionInformation->second->getTravelTime_ms(vehicleId);
        int64_t startingLocationId = vehicleId;
        if (!vehicleAssignmentState->m_taskAssignments.empty())
        {
            auto lastTaskId = vehicleAssignmentState->m_taskAssignments.back()->getTaskID();
            auto lastOptionId = vehicleAssignmentState->m_taskAssignments.back()->getOptionID();
            startingLocationId = c_TaskAssignmentState::getTaskAndOptionId(lastTaskId, lastOptionId);
        }
        // increment from last task to this one
        int64_t travelTime_ms = itVehicleInformation->second->getTravelTime_ms(startingLocationId, taskOptionId);
        if (travelTime_ms >= 0)
        {
            // travel from starting location to beginning of this task
            int64_t travelTimeTotalToBegin_ms = travelTime_ms + vehicleAssignmentState->m_travelTimeTotal_ms;

            // make sure the new task doesn't get stated before the prerequisite cost
            if ((prerequisiteTime_ms > 0) && (travelTimeTotalToBegin_ms < prerequisiteTime_ms))
            {
                travelTime_ms += prerequisiteTime_ms;
            }

            // travel from starting location to end of this task
            int64_t travelTimeTotalToEnd_ms = taskTime_ms + travelTime_ms + vehicleAssignmentState->m_travelTimeTotal_ms;

            // check vehicle's max travel time parameter
            int64_t maxVehicleTravelTime_ms = itVehicleInformation->second->m_maxVehicleTravelTime_ms;

            if ((maxVehicleTravelTime_ms < 0) || (travelTimeTotalToEnd_ms < maxVehicleTravelTime_ms))
            {
                // create new child for cost calculation
                auto newChild = std::unique_ptr<c_Node_Base>(clone());
                // calculate assignment cost
                int64_t nodeCost(INT64_MAX);
                int64_t evaluationOrderCost(INT64_MAX);
                newChild->calculateAssignmentCostBase(vehicleAssignmentState, taskOptionId,
                                                      taskTime_ms, travelTime_ms,
                                                      nodeCost, evaluationOrderCost);
                if (nodeCost < m_staticAssignmentParameters->m_minimumAssignmentCostCandidate)
                {
                    // add new child
                    newChild->m_nodeCost = nodeCost;
                    //COUT_INFO_MSG("nodeCost[" << nodeCost << "]")
                    newChild->m_travelTimeTotal_ms = travelTimeTotalToEnd_ms;
                    newChild->m_vehicleID = vehicleId;
                    newChild->m_taskOptionID = taskOptionId;
                    //tell the algebra function that we have accounted for this objective
                    newChild->m_viObjectiveIDs_Assigned.push_back(taskOptionId);

                    //////// update the task //////////
                    if (newChild->m_taskIdVsAssignmentState.find(taskOptionId) == newChild->m_taskIdVsAssignmentState.end())
                    {
                        newChild->m_taskIdVsAssignmentState[taskOptionId] = std::unique_ptr<c_TaskAssignmentState>(new c_TaskAssignmentState(taskOptionId));
                    }
                    newChild->m_taskIdVsAssignmentState[taskOptionId]->m_taskCompletionTime_ms = travelTimeTotalToEnd_ms;
                    //////// update the vehicle //////////
                    newChild->m_vehicleIdVsAssignmentState[vehicleAssignmentState->m_vehicleId]->m_travelTimeTotal_ms = travelTimeTotalToEnd_ms;
                    // add the assignment
                    auto taskAssignment = std::unique_ptr<uxas::messages::task::TaskAssignment>(new uxas::messages::task::TaskAssignment());
                    taskAssignment->setTaskID(c_TaskAssignmentState::getTaskID(taskOptionId));
                    taskAssignment->setOptionID(c_TaskAssignmentState::getOptionID(taskOptionId));
                    taskAssignment->setAssignedVehicle(vehicleId);
                    taskAssignment->setTimeThreshold(prerequisiteTime_ms);
                    taskAssignment->setTimeTaskCompleted(travelTimeTotalToEnd_ms);
                    newChild->m_vehicleIdVsAssignmentState[vehicleAssignmentState->m_vehicleId]->m_taskAssignments.push_back(std::move(taskAssignment));
                    m_costVsChildren.insert(std::pair<int64_t, std::unique_ptr<c_Node_Base> >(evaluationOrderCost, std::move(newChild)));
                    m_staticAssignmentParameters->m_numberNodesAdded++;
                }
                else
                {
                    newChild.reset();
                }
            }
            else
            {
                m_staticAssignmentParameters->m_reasonsForNoAssignment << "ASSIGNMENT_WARNING:: Vehicle[" << vehicleId << "] exceeded travel time[" << maxVehicleTravelTime_ms << "]!" << std::endl;
            }
        }
        else //if (travelTime_ms > 0)
        {
            //UXAS_LOG_WARN("ASSIGNMENT_WARNING:: No TravelTime_ms[", startingLocationId, ",", taskOptionId, "] found.");
            m_staticAssignmentParameters->m_reasonsForNoAssignment << "ASSIGNMENT_WARNING:: No TravelTime_ms[" << startingLocationId << "," << taskOptionId << "] found.!" << std::endl;
        } //if (travelTime_ms > 0)
    }
    else //if ( !isError && (itVehicleAssignmentState != m_vehicleIdVsAssignmentState.end()) &&  ... 
    {
        if (itVehicleInformation == m_staticAssignmentParameters->m_vehicleIdVsInformation.end())
        {
            m_staticAssignmentParameters->m_reasonsForNoAssignment << "ASSIGNMENT_ERROR:: could not find information for VehilceId[" << vehicleId << "]!" << std::endl;
        }
        if (itTaskOptionInformation == m_staticAssignmentParameters->m_taskOptionIdVsInformation.end())
        {
            m_staticAssignmentParameters->m_reasonsForNoAssignment << "ASSIGNMENT_ERROR:: could not find information for TaskOptionId[" << taskOptionId << "]!" << std::endl;
        }
    }
}

void c_Node_Base::calculateAssignmentCostBase(std::unique_ptr<c_VehicleAssignmentState>& vehicleAssignmentState, const int64_t& taskOptionId,
                                              const int64_t& taskTime_ms, const int64_t& travelTime_ms,
                                              int64_t& nodeCost, int64_t& evaluationOrderCost)
{
    nodeCost = MAX_COST_MS;
    evaluationOrderCost = MAX_COST_MS;

#ifdef AFRL_INTERNAL_ENABLED
    switch (m_assignmentType)
    {
        default:
//COUT_FILE_LINE_MSG("")
            calculateAssignmentCost(vehicleAssignmentState, taskOptionId,
                                    taskTime_ms, travelTime_ms,
                                    nodeCost, evaluationOrderCost);
            break;
        case uxas::project::pisr::AssignmentType::MinMaxTime:
//COUT_FILE_LINE_MSG("")

            nodeCost = taskTime_ms + travelTime_ms + vehicleAssignmentState->m_travelTimeTotal_ms;
            for (auto itVehicle = m_vehicleIdVsAssignmentState.begin(); itVehicle != m_vehicleIdVsAssignmentState.end(); itVehicle++)
            {
                int64_t travelTimeTotalLocal_ms = nodeCost;
                if (itVehicle->first != vehicleAssignmentState->m_vehicleId)
                {
                    travelTimeTotalLocal_ms = itVehicle->second->m_travelTimeTotal_ms;
                }
                if (travelTimeTotalLocal_ms > nodeCost)
                {
                    nodeCost = travelTimeTotalLocal_ms;
                }
            }
            evaluationOrderCost = nodeCost;
            break;
        case uxas::project::pisr::AssignmentType::MinCumlativeTime:
//COUT_FILE_LINE_MSG("")
            nodeCost = taskTime_ms + travelTime_ms + vehicleAssignmentState->m_travelTimeTotal_ms;
            for (auto itVehicle = m_vehicleIdVsAssignmentState.begin(); itVehicle != m_vehicleIdVsAssignmentState.end(); itVehicle++)
            {
                if (itVehicle->first != vehicleAssignmentState->m_vehicleId)
                {
                    nodeCost += itVehicle->second->m_travelTimeTotal_ms;
                }
            }
            evaluationOrderCost = nodeCost;
            break;
    }
#else
    // MINMAX
    nodeCost = taskTime_ms + travelTime_ms + vehicleAssignmentState->m_travelTimeTotal_ms;
    for (auto itVehicle = m_vehicleIdVsAssignmentState.begin(); itVehicle != m_vehicleIdVsAssignmentState.end(); itVehicle++)
    {
        int64_t travelTimeTotalLocal_ms = nodeCost;
        if (itVehicle->first != vehicleAssignmentState->m_vehicleId)
        {
            travelTimeTotalLocal_ms = itVehicle->second->m_travelTimeTotal_ms;
        }
        if (travelTimeTotalLocal_ms > nodeCost)
        {
            nodeCost = travelTimeTotalLocal_ms;
        }
    }
    evaluationOrderCost = nodeCost;
#endif
}

}; //namespace service
}; //namespace uxas
