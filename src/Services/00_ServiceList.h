// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   ServiceList.h
 * Author: steve
 *
 * Created on March 29, 2017, 4:47 PM
 */

/*! \brief This file is used to register services. First the service header is
 * "included" and the top of the service manager, and then the service is registered
 * in ServiceManager::getInstance(), through the creation of a "dummy" instance. 
 * To add new services: 
 * 1) add a #include statement, for the service, in the SERVICE HEADER FILES SECTION. 
 * 2) add a line to create a "dummy" instance in the SERVICE REGISTRATION SECTION. 
 * 3) add a #include statement, for each task, in the INCLUDE TASK MESSAGES SECTION. 
 * 4) add a subscription, for each task, in the SUBSCRIBE TO TASKS SECTION. 
*/


//////////////////////////////////////////////////////////////////////////////////////
//define INCLUDE_SERVICE_HEADERS to include header files at top of service manager ///
//////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////
//define REGISTER_SERVICE_CODE to register the services in the     service manager ///
//////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////
//define INCLUDE_TASK_MESSAGES to to include headers for all, current task messages///
//////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////
//define SUBSCRIBE_TO_TASKS to subscribe to all tasks                              ///
//////////////////////////////////////////////////////////////////////////////////////

#include "config.h"

#ifdef AFRL_INTERNAL_ENABLED
#include "AFRLInternalServices.h"
#endif

//////////////////////////////////////////////////////
/// BEGIN -- SERVICE HEADER FILES SECTION          ///
/// include service header files in this section   ///
//////////////////////////////////////////////////////

#if defined INCLUDE_SERVICE_HEADERS
#undef INCLUDE_SERVICE_HEADERS

#ifndef UXAS_SERVICE_LIST_CODE_HEADERS  // only allow one-time definition
#define UXAS_SERVICE_LIST_CODE_HEADERS

// examples
#include "01_HelloWorld.h"

// data
#include "MessageLoggerDataService.h"
#include "AutomationDiagramDataService.h"
#ifdef AFRL_INTERNAL_ENABLED
#include "VicsLoggerDataService.h"
#endif

// task
#include "AssignmentCoordinatorTaskService.h"
#include "AngledAreaSearchTaskService.h"
#include "BlockadeTaskService.h"
#include "CmasiAreaSearchTaskService.h"
#include "CmasiLineSearchTaskService.h"
#include "CmasiPointSearchTaskService.h"
#include "CommRelayTaskService.h"
#include "CordonTaskService.h"
#include "EscortTaskService.h"
#include "ImpactLineSearchTaskService.h"
#include "ImpactPointSearchTaskService.h"
#include "MultiVehicleWatchTaskService.h"
#include "OverwatchTaskService.h"
#include "PatternSearchTaskService.h"
#include "TaskManagerService.h"
#include "TaskTrackerService.h"

// test
#include "SendMessagesService.h"
#include "SendTestMessagesService.h"
#include "MessageLoggerForTestService.h"
#include "SerialAutomationRequestTestService.h"
#include "TcpBridge.h"
#include "Test_SimulationTime.h"

// general services
#include "AssignmentTreeBranchBoundService.h"
#include "AutomationRequestValidatorService.h"
#include "BatchSummaryService.h"
#include "OperatingRegionStateService.h"
#include "OsmPlannerService.h"
#include "PlanBuilderService.h"
#include "RouteAggregatorService.h"
#include "RoutePlannerService.h"
#include "SensorManagerService.h"
#include "WaypointPlanManagerService.h"
#include "RoutePlannerVisibilityService.h"

#endif  //UXAS_SERVICE_LIST_CODE_HEADERS
#endif  //INCLUDE_SERVICE_HEADERS

//////////////////////////////////////////////////////
/// END -- SERVICE HEADER FILES SECTION            ///
//////////////////////////////////////////////////////




//////////////////////////////////////////////////////////
/// BEGIN -- SERVICE REGISTRATION SECTION              ///
/// create dummy instances of services in this section ///
//////////////////////////////////////////////////////////

#if defined REGISTER_SERVICE_CODE   // define this to register the services
#undef REGISTER_SERVICE_CODE

// examples
{auto svc = uxas::stduxas::make_unique<uxas::service::HelloWorld>();}

// adapter
{auto svc = uxas::stduxas::make_unique<uxas::service::adapter::TcpBridge>();}   //TEST ONLY

// data
{auto svc = uxas::stduxas::make_unique<uxas::service::data::MessageLoggerDataService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::data::AutomationDiagramDataService>();}

// task
{auto svc = uxas::stduxas::make_unique<uxas::service::task::AssignmentCoordinatorTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::AngledAreaSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::BlockadeTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::CmasiAreaSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::CmasiLineSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::CmasiPointSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::CommRelayTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::CordonTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::EscortTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::ImpactLineSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::ImpactPointSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::MultiVehicleWatchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::OverwatchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::PatternSearchTaskService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::TaskManagerService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::task::TaskTrackerService>();}

// test
{auto svc = uxas::stduxas::make_unique<uxas::service::test::SendMessagesService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::test::SendTestMessagesService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::test::SerialAutomationRequestTestService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::test::Test_SimulationTime>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::test::MessageLoggerForTestService>();}

// general services
{auto svc = uxas::stduxas::make_unique<uxas::service::AssignmentTreeBranchBoundService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::AutomationRequestValidatorService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::BatchSummaryService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::OperatingRegionStateService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::OsmPlannerService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::PlanBuilderService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::RouteAggregatorService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::RoutePlannerService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::SensorManagerService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::WaypointPlanManagerService>();}
{auto svc = uxas::stduxas::make_unique<uxas::service::RoutePlannerVisibilityService>();}

#endif  //REGISTER_SERVICE_CODE
//////////////////////////////////////////////////////////
/// END -- SERVICE REGISTRATION SECTION                ///
//////////////////////////////////////////////////////////
