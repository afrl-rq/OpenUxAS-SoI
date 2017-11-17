// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   PlanBuilderService.cpp
 * Author: steve
 * 
 * Created on September 2, 2015, 6:17 PM
 */


#include "PlanBuilderService.h"

#include "UnitConversions.h"
#include "Constants/Convert.h"

#include "uxas/messages/task/UniqueAutomationResponse.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/vehicles/GroundVehicleState.h"
#include "afrl/vehicles/SurfaceVehicleState.h"

#include "avtas/lmcp/ByteBuffer.h"
#include "avtas/lmcp/Factory.h"

#include "pugixml.hpp"

#include <sstream>
#include <iostream>     // std::cout, cerr, etc

#define STRING_XML_ASSIGNMENT_START_POINT_LEAD_M "AssignmentStartPointLead_m"

// Rust prototypes
extern "C" {
void* plan_builder_new();
void plan_builder_delete(void* raw_pb);
void plan_builder_configure(void* raw_pb, double assignment_start_point_lead_m);
void plan_builder_process_received_lmcp_message(uxas::service::PlanBuilderService *pbs, void* raw_pb, uint8_t *msg_buf, uint32_t msg_len);
}

namespace uxas
{
namespace service
{

PlanBuilderService::ServiceBase::CreationRegistrar<PlanBuilderService>
PlanBuilderService::s_registrar(PlanBuilderService::s_registryServiceTypeNames());

PlanBuilderService::PlanBuilderService()
: ServiceBase(PlanBuilderService::s_typeName(), PlanBuilderService::s_directoryName()) {
  m_PlanBuilder = plan_builder_new();
}

PlanBuilderService::~PlanBuilderService() {
  plan_builder_delete(m_PlanBuilder);
}

bool
PlanBuilderService::configure(const pugi::xml_node& ndComponent)
{
  double assignmentStartPointLead_m = 50.0;
  if (!ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).empty()) {
    assignmentStartPointLead_m = ndComponent.attribute(STRING_XML_ASSIGNMENT_START_POINT_LEAD_M).as_double();
  }

  addSubscriptionAddress(uxas::messages::task::UniqueAutomationRequest::Subscription);
  addSubscriptionAddress(uxas::messages::task::TaskAssignmentSummary::Subscription);
  addSubscriptionAddress(uxas::messages::task::TaskImplementationResponse::Subscription);
  addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
  addSubscriptionAddress(afrl::vehicles::GroundVehicleState::Subscription);
  addSubscriptionAddress(afrl::vehicles::SurfaceVehicleState::Subscription);

  plan_builder_configure(m_PlanBuilder, assignmentStartPointLead_m);

  return true;
}

bool
PlanBuilderService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
  avtas::lmcp::ByteBuffer * lmcpByteBuffer = avtas::lmcp::Factory::packMessage(receivedLmcpMessage->m_object.get(), true);
  plan_builder_process_received_lmcp_message(this, m_PlanBuilder, lmcpByteBuffer->array(), lmcpByteBuffer->capacity());
  delete lmcpByteBuffer;

  return (false); // always false implies never terminating service from here
};

}; //namespace service
}; //namespace uxas

extern "C" {
// TODO: rewrite all the unit conversions in Rust. This is gross.
void convert_latlong_deg_to_northeast_m_raw(const double *lat_deg, const double *long_deg, double *north_m, double *east_m) {
  uxas::common::utilities::CUnitConversions unitConversions;
  unitConversions.ConvertLatLong_degToNorthEast_m(*lat_deg, *long_deg, *north_m, *east_m);
}
void convert_northeast_m_to_latlong_deg_raw(const double *north_m, const double *east_m, double *lat_deg, double *long_deg) {
  uxas::common::utilities::CUnitConversions unitConversions;
  unitConversions.ConvertNorthEast_mToLatLong_deg(*north_m, *east_m, *lat_deg, *long_deg);
}
}
