// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   TemporalService.cpp
 * Author: derek
 * 
 * Created on Aug 24, 2015, 9:31 AM
 */

#include <iostream>
#include <cmath>
#include "TemporalService.h"

#include "TimeUtilities.h"
#include "UxAS_Log.h"
#include "UxAS_TimerManager.h"

#include "uxas/messages/task/TaskInitialized.h"
#include "uxas/messages/task/TaskAutomationRequest.h"
#include "uxas/messages/task/TaskAutomationResponse.h"
#include "uxas/messages/task/UniqueAutomationResponse.h"

#include "uxas/temporal/TemporalAutomationRequest.h"
#include "uxas/temporal/TemporalUniqueAutomationResponse.h"

#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/impact/ImpactAutomationRequest.h"
#include "afrl/impact/ImpactAutomationResponse.h"
#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"
#include "UnitConversions.h"

#include "afrl/cmasi/ServiceStatus.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/impact/GroundVehicleConfiguration.h"
#include "afrl/impact/SurfaceVehicleConfiguration.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/impact/GroundVehicleState.h"
#include "afrl/impact/SurfaceVehicleState.h"
#include "afrl/cmasi/RemoveTasks.h"
#include "afrl/cmasi/KeepInZone.h"
#include "afrl/cmasi/KeepOutZone.h"
#include "afrl/cmasi/LoiterAction.h"

#include "afrl/cmasi/Task.h"
#include "afrl/cmasi/TaskDescendants.h"    


#include "afrl/impact/PointOfInterest.h"
#include "afrl/impact/LineOfInterest.h"
#include "afrl/impact/AreaOfInterest.h"


#include <typeinfo>
#include "pugixml.hpp"

#define STRING_XML_MAX_RESPONSE_TIME_MS "MaxResponseTime_ms"

#define COUT_INFO_MSG(MESSAGE) std::cout << "<>TemporalService::" << MESSAGE << std::endl;std::cout.flush();

namespace uxas
{
	namespace service
	{
		TemporalService::ServiceBase::CreationRegistrar<TemporalService>
		TemporalService::s_registrar(TemporalService::s_registryServiceTypeNames());

		TemporalService::TemporalService()
		: ServiceBase(TemporalService::s_typeName(), TemporalService::s_directoryName())
		{
		};

		TemporalService::~TemporalService()
		{
			uint64_t delayTime_ms{1000};
			if (m_responseTimerId && !uxas::common::TimerManager::getInstance().destroyTimer(m_responseTimerId, delayTime_ms))
			{
				UXAS_LOG_WARN("TemporalService::~TemporalService failed to destroy response timer "
					"(m_responseTimerId) with timer ID ", m_responseTimerId, " within ", delayTime_ms, " millisecond timeout");
			}
		};

		bool
		TemporalService::initialize()
		{

	// create timer
			m_responseTimerId = uxas::common::TimerManager::getInstance().createTimer(
				std::bind(&TemporalService::OnResponseTimeout, this), "TemporalService::OnResponseTimeout()");
			return true;
		}

		bool
		TemporalService::configure(const pugi::xml_node & ndComponent)
		{
			if (!ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).empty())
			{
				m_maxResponseTime_ms = ndComponent.attribute(STRING_XML_MAX_RESPONSE_TIME_MS).as_uint();
			}


			addSubscriptionAddress(uxas::temporal::TemporalAutomationRequest::Subscription);
			addSubscriptionAddress(uxas::temporal::TemporalUniqueAutomationResponse::Subscription);
			// addSubscriptionAddress(afrl::cmasi::AutomationRequest::Subscription);
			addSubscriptionAddress(afrl::impact::ImpactAutomationRequest::Subscription);
			addSubscriptionAddress(uxas::messages::task::UniqueAutomationResponse::Subscription);
			addSubscriptionAddress(uxas::messages::task::TaskAutomationRequest::Subscription);

	//ENTITY CONFIGURATIONS
			addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
			addSubscriptionAddress(afrl::impact::GroundVehicleConfiguration::Subscription);
			addSubscriptionAddress(afrl::impact::SurfaceVehicleConfiguration::Subscription);
	// ENTITY STATES
			addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
			addSubscriptionAddress(afrl::impact::GroundVehicleState::Subscription);
			addSubscriptionAddress(afrl::impact::SurfaceVehicleState::Subscription);
	// TASKS
			addSubscriptionAddress(afrl::cmasi::RemoveTasks::Subscription);
			addSubscriptionAddress(uxas::messages::task::TaskInitialized::Subscription);
	// KEEP-IN/OUT/OPERATING
			addSubscriptionAddress(afrl::cmasi::OperatingRegion::Subscription);
			addSubscriptionAddress(afrl::cmasi::KeepInZone::Subscription);
			addSubscriptionAddress(afrl::cmasi::KeepOutZone::Subscription);

			addSubscriptionAddress(afrl::impact::AreaOfInterest::Subscription);
			addSubscriptionAddress(afrl::impact::LineOfInterest::Subscription);
			addSubscriptionAddress(afrl::impact::PointOfInterest::Subscription);

	// Subscribe to Task and all derivatives of Task
			addSubscriptionAddress(afrl::cmasi::Task::Subscription);
			std::vector< std::string > childtasks = afrl::cmasi::TaskDescendants();
			for(auto child : childtasks)
				addSubscriptionAddress(child);

			return true;
		}

		bool
		TemporalService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
		{
			bool isMessageHandled{false};
			if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object.get()))
			{
				auto airVehicleState = std::static_pointer_cast<afrl::cmasi::AirVehicleState>(receivedLmcpMessage->m_object);
				m_availableStateEntityIds.insert(airVehicleState->getID());
				m_vehicleStates[airVehicleState->getID()] = airVehicleState;
				isMessageHandled = true;
			}
			else if (afrl::impact::isGroundVehicleState(receivedLmcpMessage->m_object.get()))
			{
				auto groundVehicleState = std::static_pointer_cast<afrl::impact::GroundVehicleState>(receivedLmcpMessage->m_object);
				m_availableStateEntityIds.insert(groundVehicleState->getID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isSurfaceVehicleState(receivedLmcpMessage->m_object.get()))
			{
				auto surfaceVehicleState = std::static_pointer_cast<afrl::impact::SurfaceVehicleState>(receivedLmcpMessage->m_object);
				m_availableStateEntityIds.insert(surfaceVehicleState->getID());
				isMessageHandled = true;
			}
			else if (uxas::messages::task::isTaskInitialized(receivedLmcpMessage->m_object.get()))
			{
				auto taskInitialized = std::static_pointer_cast<uxas::messages::task::TaskInitialized>(receivedLmcpMessage->m_object);
				m_availableStartedTaskIds.insert(taskInitialized->getTaskID());
				isMessageHandled = true;
			}
			else if (afrl::cmasi::isAirVehicleConfiguration(receivedLmcpMessage->m_object.get()))
			{
				auto airVehicleConfiguration = std::static_pointer_cast<afrl::cmasi::AirVehicleConfiguration>(receivedLmcpMessage->m_object);
				m_availableConfigurationEntityIds.insert(airVehicleConfiguration->getID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isGroundVehicleConfiguration(receivedLmcpMessage->m_object.get()))
			{
				auto groundVehicleConfiguration = std::static_pointer_cast<afrl::impact::GroundVehicleConfiguration>(receivedLmcpMessage->m_object);
				m_availableConfigurationEntityIds.insert(groundVehicleConfiguration->getID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isSurfaceVehicleConfiguration(receivedLmcpMessage->m_object.get()))
			{
				auto surfaceVehicleConfiguration = std::static_pointer_cast<afrl::impact::SurfaceVehicleConfiguration>(receivedLmcpMessage->m_object);
				m_availableConfigurationEntityIds.insert(surfaceVehicleConfiguration->getID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isAreaOfInterest(receivedLmcpMessage->m_object.get()))
			{
				auto areaOfInterest = std::static_pointer_cast<afrl::impact::AreaOfInterest>(receivedLmcpMessage->m_object);
				m_availableAreaOfInterestIds.insert(areaOfInterest->getAreaID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isLineOfInterest(receivedLmcpMessage->m_object.get()))
			{
				auto lineOfInterest = std::static_pointer_cast<afrl::impact::LineOfInterest>(receivedLmcpMessage->m_object);
				m_availableLineOfInterestIds.insert(lineOfInterest->getLineID());
				isMessageHandled = true;
			}
			else if (afrl::impact::isPointOfInterest(receivedLmcpMessage->m_object.get()))
			{
				auto pointOfInterest = std::static_pointer_cast<afrl::impact::PointOfInterest>(receivedLmcpMessage->m_object);
				m_availablePointOfInterestIds.insert(pointOfInterest->getPointID());
				isMessageHandled = true;
			}
			else if (afrl::cmasi::isKeepInZone(receivedLmcpMessage->m_object.get()))
			{
				auto keepInZone = std::static_pointer_cast<afrl::cmasi::KeepInZone>(receivedLmcpMessage->m_object);
				m_availableKeepInZoneIds.insert(keepInZone->getZoneID());
				isMessageHandled = true;
			}
			else if (afrl::cmasi::isKeepOutZone(receivedLmcpMessage->m_object.get()))
			{
				auto keepOutZone = std::static_pointer_cast<afrl::cmasi::KeepOutZone>(receivedLmcpMessage->m_object);
				m_availableKeepOutZoneIds.insert(keepOutZone->getZoneID());
				isMessageHandled = true;
			}
			else if (afrl::cmasi::isOperatingRegion(receivedLmcpMessage->m_object.get()))
			{
				auto operatingRegion = std::static_pointer_cast<afrl::cmasi::OperatingRegion>(receivedLmcpMessage->m_object);
				m_availableOperatingRegions[operatingRegion->getID()] = operatingRegion;
				isMessageHandled = true;
			}
			else if (afrl::cmasi::isRemoveTasks(receivedLmcpMessage->m_object.get()))
			{
				auto removeTasks = std::static_pointer_cast<afrl::cmasi::RemoveTasks>(receivedLmcpMessage->m_object);
				for (auto& taskId : removeTasks->getTaskList())
				{
					m_availableTasks.erase(taskId);
					m_availableStartedTaskIds.erase(taskId);
				}
				isMessageHandled = true;
			}
			else if (uxas::temporal::isTemporalAutomationRequest(receivedLmcpMessage->m_object))
			{
				m_waitingForResponse.reset();

                //INITIALIZE WITH TemporalAutomationRequest
				COUT_INFO_MSG("AUTOMATION_BARDH INIT")
				auto mainAutomationRequest = std::static_pointer_cast<uxas::temporal::TemporalAutomationRequest>(receivedLmcpMessage->m_object);       
				remPAStr = mainAutomationRequest->getTaskRelationships();

                //get data from xml file and store it into variables so that it may be used for next partitions of the formula
				mem_OperatingRegion = mainAutomationRequest->getOperatingRegion();
				mem_RedoAllTasks = mainAutomationRequest->getRedoAllTasks();
				mem_EntityList = mainAutomationRequest->getEntityList();
				mem_TaskList = mainAutomationRequest->getTaskList();

				SendTemporalRequest();

			}
			else if (uxas::temporal::isTemporalUniqueAutomationResponse(receivedLmcpMessage->m_object))
			{
				m_waitingForResponse.reset();
				COUT_INFO_MSG("RESPONSE RECEIVED1")
				unsigned index = 0;
				std::vector<double> maxTimePerMission;

				double maxVal = 0;
				int maxVehicleID = 0;

				//GET TIMING FROM PREVIOUS MISSIONS AND ADD TO FIRST WAYPOINT OF CURRENT
				for (auto v: mem_MissionCommandList)
				{
					COUT_INFO_MSG("ERR RESPONSE RECEIVED2")
					auto found = m_vehicleStates.find(v->getVehicleID());
					if ( found != m_vehicleStates.end() )
					{
						auto currLoc = new afrl::cmasi::Location3D;
						auto nextLoc = new afrl::cmasi::Location3D;

						currLoc = found->second->getLocation();

						double m_currNorth_m;
						double m_currEast_m;

						double m_nextNorth_m;
						double m_nextEast_m;

						maxTimePerMission.push_back(0);

						uxas::common::utilities::CUnitConversions flatEarth;
						flatEarth.ConvertLatLong_degToNorthEast_m(currLoc->getLatitude(), currLoc->getLongitude(), m_currNorth_m, m_currEast_m);
						COUT_INFO_MSG("ERR RESPONSE RECEIVED3")
						for (auto w : v->getWaypointList())
						{
							nextLoc->setLatitude(w->getLatitude());
							nextLoc->setLongitude(w->getLongitude());
							nextLoc->setAltitude(w->getAltitude());

							flatEarth.ConvertLatLong_degToNorthEast_m(nextLoc->getLatitude(), nextLoc->getLongitude(), m_nextNorth_m, m_nextEast_m);

							double distancex = pow((m_nextNorth_m - m_currNorth_m),2);
							double distancey = pow((m_nextEast_m - m_currEast_m),2);
							double calcDistance = sqrt(distancex + distancey);


							maxTimePerMission[index] = maxTimePerMission[index] + calcDistance/(w->getSpeed());

							m_currNorth_m = m_nextNorth_m;
							m_currEast_m = m_nextEast_m;
						}
						COUT_INFO_MSG("ERR RESPONSE RECEIVED4")
						m_timeAdjustment[found->first] = maxTimePerMission[index];  

								//INFO FOR LOITERING
						if ( maxTimePerMission[index] > maxVal )
						{
							maxVal = maxTimePerMission[index];
							maxVehicleID = v->getVehicleID();
						}

						index++;
					}
				}
				COUT_INFO_MSG("ERR RESPONSE RECEIVED5")
				for (auto v: mem_MissionCommandList)
				{
					auto found = m_vehicleStates.find(v->getVehicleID());
					if ( found != m_vehicleStates.end() )
					{
									// afrl::cmasi::LoiterAction * pLoiterAction(new afrl::cmasi::LoiterAction());
									// pLoiterAction->setDuration(maxVal - m_timeAdjustment[found->first]);
									// v->getWaypointList().back()->getVehicleActionList().push_back(pLoiterAction);

						// opposite = hypotenuse * sin(30) = loiterTime/6 * sin(30)
						// adjecent = hypotenuse * cos(30) = loiterTime/6 * cos(30)

						double loiterTime = maxVal - m_timeAdjustment[found->first];

						double posX;
						double posY;

						double lat;
						double lon;

						double newPosX;
						double newPosY;

						std::vector<double> anglesHex = {0,60,120,180,240,300};
						auto prevWp = v->getWaypointList()[v->getWaypointList().size() - 1] ;
						
						uxas::common::utilities::CUnitConversions flatEarth;
						flatEarth.ConvertLatLong_degToNorthEast_m(prevWp->getLatitude(), prevWp->getLongitude(), posX, posY);
						double angleShift = atan2(posX,posY) * 180/M_PI;

						
						if (loiterTime != 0)
						{
							for (int i = 0; i < 6; ++i)
							{
								auto nextWp = v->getWaypointList().back()->clone();

								flatEarth.ConvertLatLong_degToNorthEast_m(nextWp->getLatitude(), nextWp->getLongitude(), posX, posY);
								newPosX = posX + (22 * (loiterTime * 1/6) * cos( angleShift + ( anglesHex[i] * M_PI/180 ) ) ); 
								newPosY = posY + (22 * (loiterTime * 1/6) * sin( angleShift + ( anglesHex[i] * M_PI/180 ) ) );



								flatEarth.ConvertNorthEast_mToLatLong_deg(newPosX, newPosY, lat, lon);

								std::cout << "LOITER: " << loiterTime << " posX:  " << posX << " newposX:  " << newPosX << " posY:  " << posY << " newposY:  " << newPosY << "\n";

								nextWp->setLongitude( lon );
								nextWp->setLatitude( lat );
								nextWp->setNumber( v->getWaypointList().back()->getNumber() + 1 );

								v->getWaypointList().back()->setNextWaypoint( v->getWaypointList().back()->getNumber() + 1 );
								v->getWaypointList().push_back(nextWp);
							}
						}

						

					}
					
				}

				//IF AUTOMATIONRESPONSETEMPORAL - STORE MISSIONS FOR VEHICLES
				//FOR FUTURE MISSIONS WHERE VEHICLES ARE THE SAME AND IN THE STORED MISSIONS, APPEND EXISTING INSTEAD OF CREATING NEW MISSION
				COUT_INFO_MSG("AR TEMPORAL INIT")				
				auto uniqueResp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);
				auto missionCommandList = uniqueResp->getOriginalResponse()->getMissionCommandList(); 
				auto vehActionCommandList = uniqueResp->getOriginalResponse()->getVehicleCommandList(); 
				//loop thorugh each and clone

				bool bool_temp_checkifexists = false;
				
				// CHECK IF MISSIONS FROM THE MOST RECENT REQUEST HAVE A VEHICLE THAT ALREADY EXISTS IN MEM_MISSIONCOMMANDLIST
				// IF SO, APPEND EXISTING MISSION RATHER THAN CREATE A NEW MISSION
				for (auto v : missionCommandList)
				{
					bool foundMission = 0;

					for (auto u : mem_MissionCommandList)
					{
						if (v->getVehicleID() == u->getVehicleID())
							foundMission = 1;
					}

					if (foundMission == 0)
					{
						COUT_INFO_MSG("<<<<MISSION ADDED>>>>")
						mem_MissionCommandList.push_back(v->clone());
					}
					else
					{
						COUT_INFO_MSG("<<<<MISSION FOR VEHICLE EXISTS - APPENDING EXISTING MISSION >>>>")

						for (auto u : mem_MissionCommandList)
						{
									//std::cout << v->getVehicleID() << "xVEHICLEx" << u->getVehicleID() << "\n";
							if ( u->getVehicleID() == v->getVehicleID() )
							{   
								bool_temp_checkifexists = true;

								COUT_INFO_MSG("PUSHING WAYPOINTS...")

								std::cout << "LAST APPENDED:" << v->getWaypointList().front()->getLatitude() << "<><><>" << v->getWaypointList().front()->getLongitude() << "\n";

								u->getWaypointList().back()->setNextWaypoint(v->getWaypointList().front()->getNumber());

								for (auto w : v->getWaypointList())
								{

												//std::cout << "FINAL: " << v->getWaypointList().back()->getLatitude() << "<><><>" << v->getWaypointList().back()->getLongitude() << "\n";

									std::cout << "ADDING: " << w->getLatitude() << "<><><>" << w->getLongitude() << "\n";
												//w->setNumber(index);
									double lastwp = u->getWaypointList().back()->getNumber();
									u->getWaypointList().back()->setNextWaypoint(lastwp+1);
									
									u->getWaypointList().push_back(w->clone());
									u->getWaypointList().back()->setNumber(lastwp+1);

								}
								u->getWaypointList().back()->setNextWaypoint(0);
							} 
							else
							{
								COUT_INFO_MSG("NOT PUSHING WAYPOINTS...")
							} 

						}
					}
						


							// }


					//POSSIBLE ERROR - USE MAP INSTEAD OF VECTOR


					//CALCULATE THE TIME FOR EACH MISSION
					//lookup from m_vehicleStates and store from airvehiclestate from amase 



						// //FOR THE CASE WHERE MISSION COMMAND IS FOR ANOTHER VEHICLE
						// if (!bool_temp_checkifexists)
						// {
						//     for (auto v : missionCommandList)           
						//     {
						//         mem_MissionCommandList.push_back(v->clone());
						//     }

						//     bool_temp_checkifexists = false;
						// }

						
					

					endingLocationsEntityIDMissionList.push_back(v->getVehicleID());
					endingLocationsLatPerMissionList.push_back(v->getWaypointList().back()->getLatitude());
					endingLocationsLonPerMissionList.push_back(v->getWaypointList().back()->getLongitude());
					endingLocationsAltPerMissionList.push_back(v->getWaypointList().back()->getAltitude());


					COUT_INFO_MSG("ID LAT LON ALT:")
					COUT_INFO_MSG(endingLocationsEntityIDMissionList.back());
					COUT_INFO_MSG(endingLocationsLatPerMissionList.back())
					COUT_INFO_MSG(endingLocationsLonPerMissionList.back())
					COUT_INFO_MSG(endingLocationsAltPerMissionList.back())


					
					
				}

				COUT_INFO_MSG("WAYPOINTS--------------------------------")


				//PRINT OUT WAYPOINTS
				for (auto v : missionCommandList)
				{
					std::cout << "VehicleWP: " << v->getVehicleID() << " AND " << "CommandID: " << v->getCommandID() << "\n";
					unsigned index = 1;
					for (auto u : v->getWaypointList())
					{

						std::cout << index << ":::" << u->getNumber() << "<><>" << u->getLatitude() << "<><><>" << u->getLongitude() << "\n";
						index++;
					}
				}

				if (mem_LastIteration == true)
				{
					//Handle Last Iteration
					COUT_INFO_MSG("FINAL RESPONSE")


					auto tempResp = std::static_pointer_cast<uxas::messages::task::UniqueAutomationResponse>(receivedLmcpMessage->m_object);
						//auto testingStuff = tempResp->clone();

						// for (auto v : mem_MissionCommandList)
						//     std::cout << typeid(v).name() << '\n';

					tempResp->getOriginalResponse()->getMissionCommandList().clear();
					tempResp->getOriginalResponse()->getMissionCommandList().insert(tempResp->getOriginalResponse()->getMissionCommandList().end(),mem_MissionCommandList.begin(),mem_MissionCommandList.end());

						// std::cout << "--" << '\n';

						// for (auto v : tempResp->getOriginalResponse()->getMissionCommandList())
						//     std::cout << typeid(v).name() << '\n';

						// std::cout << "--" << '\n';

						// for (auto v : tempResp->getOriginalResponse()->getMissionCommandList())
						//     std::cout << typeid(v).name() << '\n';

						// std::cout << "--" << '\n';

					for (auto v : tempResp->getOriginalResponse()->getMissionCommandList())
					{
						COUT_INFO_MSG("ChangeOfMission!")
						std::cout << "VehicleWP: " << v->getVehicleID() << "\n";
						unsigned index = 1;
						for (auto w : v->getWaypointList())
						{
							std::cout << index << ":::" << w->getNumber() << "<><>" << w->getLatitude() << "<><><>" << w->getLongitude() << "<><><>" << w->getNextWaypoint()  << "\n";

							index++;
						}
					}

					auto finalAutomationResponse = std::shared_ptr<afrl::cmasi::AutomationResponse>(tempResp->getOriginalResponse()->clone());
					COUT_INFO_MSG("FINAL RESPONSE SENT")



					sendSharedLmcpObjectBroadcastMessage(finalAutomationResponse);
					m_waitingRequests.clear();

				}
				else
				{
					COUT_INFO_MSG("SENDING TEMPORAL REQUEST")
					SendTemporalRequest();
				}

				isMessageHandled = true;
			}
			


			if (!isMessageHandled)
			{
				auto baseTask = std::dynamic_pointer_cast<afrl::cmasi::Task>(receivedLmcpMessage->m_object);
				if (baseTask)
				{
					m_availableTasks[baseTask->getTaskID()] = baseTask;
				}
				isMessageHandled = true;
			}
			checkToSendNextRequest();
			return false;
		}

		void TemporalService::calculateTiming()
		{

		}

		void TemporalService::SendTemporalRequest()
		{
			size_t position = remPAStr.find('S');
			std::string partPAStr;
			auto qAutomationRequest = std::shared_ptr<uxas::temporal::TemporalAutomationRequest> (new uxas::temporal::TemporalAutomationRequest);

			COUT_INFO_MSG("SENDING")
            //BREAK UP PA STRING AND STORE THE NEXT PARTITION IN MEMORY
			if (position != std::string::npos)
			{
                // iterate
				partPAStr = remPAStr.substr(0, position); 
				remPAStr = remPAStr.substr(position+1);
				COUT_INFO_MSG("PARTITION:");
				COUT_INFO_MSG(partPAStr.c_str());      
			}
			else
			{
                //case for last partition
				COUT_INFO_MSG("LAST PARTITION:");
				COUT_INFO_MSG(remPAStr.c_str());
				partPAStr = remPAStr;
				mem_LastIteration = true;
			}
			
            //SET UP REQUEST
			qAutomationRequest->getEntityList().insert(qAutomationRequest->getEntityList().end(),mem_EntityList.begin(), mem_EntityList.end());
			qAutomationRequest->getTaskList().insert(qAutomationRequest->getTaskList().end(),mem_TaskList.begin(), mem_TaskList.end());
			qAutomationRequest->setOperatingRegion(mem_OperatingRegion);
			qAutomationRequest->setRedoAllTasks(mem_RedoAllTasks);
			qAutomationRequest->setTaskRelationships(partPAStr);
			qAutomationRequest->setTemporal(true);

            //FILL U
			auto qUniqueAutomationRequest = std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> (new uxas::messages::task::UniqueAutomationRequest);
			qUniqueAutomationRequest->setRequestID(getUniqueEntitySendMessageId());
			qUniqueAutomationRequest->setOriginalRequest((afrl::cmasi::AutomationRequest*) qAutomationRequest->clone());

			//IN CASE OF MULTIPLE PARTITIONS - START PLANNING FROM THE END OF LAST POSITION
			if (!endingLocationsEntityIDMissionList.empty())
			{
				COUT_INFO_MSG("INTXXXINT")

				auto qPlanningStates = qUniqueAutomationRequest->getPlanningStates();

				for (auto v : mem_MissionCommandList)
				{   
					unsigned index = 0;
					for ( auto u : endingLocationsEntityIDMissionList)
					{
						if ( v->getVehicleID() == u )
						{
							COUT_INFO_MSG("v equals u")
							auto newPlanningState = new uxas::messages::task::PlanningState;
							newPlanningState->setEntityID(u);

							auto loc3D = new afrl::cmasi::Location3D;
							loc3D->setLatitude(endingLocationsLatPerMissionList[index]);
							loc3D->setLongitude(endingLocationsLonPerMissionList[index]);
							loc3D->setAltitude(endingLocationsAltPerMissionList[index]);

							std::cout << "LAT: " << endingLocationsLatPerMissionList[index] << " LON: " << endingLocationsLonPerMissionList[index] << '\n';

									// tempResp->getOriginalResponse()->getMissionCommandList().clear();
									// tempResp->getOriginalResponse()->getMissionCommandList().insert(tempResp->getOriginalResponse()->getMissionCommandList().end(),mem_MissionCommandList.begin(),mem_MissionCommandList.end());
							newPlanningState->setPlanningPosition(loc3D);
							qPlanningStates.push_back(newPlanningState);
						}
						index++;
					}
				}
				for (auto v : qPlanningStates)
					qUniqueAutomationRequest->getPlanningStates().push_back(v->clone());

			}

			m_waitingRequests.push_back(qUniqueAutomationRequest);
		}

		void TemporalService::OnResponseTimeout()
		{
			if(!m_waitingForResponse)
			{
				m_isAllClear = true;        
			}
			else
			{
				m_waitingForResponse.reset();
				checkToSendNextRequest();
			}
		}

		void TemporalService::checkToSendNextRequest()
		{
			if(!m_waitingForResponse && !m_waitingRequests.empty())
			{
				auto uniqueAutomationRequest = m_waitingRequests.front();
				m_waitingRequests.pop_front();
				if (isCheckAutomationRequestRequirements(uniqueAutomationRequest))
				{
					m_isAllClear = false;
					m_waitingForResponse = uniqueAutomationRequest;
					sendSharedLmcpObjectBroadcastMessage(uniqueAutomationRequest);
					
					auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
					serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
					auto keyValuePair = new afrl::cmasi::KeyValuePair;
					std::string message = "UniqueAutomationRequest[" + std::to_string(uniqueAutomationRequest->getRequestID()) + "] - sent";
					keyValuePair->setKey(message);
					serviceStatus->getInfo().push_back(keyValuePair);
					keyValuePair = nullptr;
					sendSharedLmcpObjectBroadcastMessage(serviceStatus);
			// reset the timer
				}
			else //if (isCheckAutomationRequestRequirements(uniqueAutomationRequest))
			{
				if (m_waitingRequests.empty())
				{
					m_waitingRequests.push_back(uniqueAutomationRequest);
				}
				else
				{
					// automation request ID not sent
					std::stringstream reasonForFailure;
					reasonForFailure << "- automation request ID[" << uniqueAutomationRequest->getRequestID() << "] was not ready in time and was not sent." << std::endl;
					UXAS_LOG_WARN(reasonForFailure.str());
					COUT_INFO_MSG(reasonForFailure.str());
					auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
					serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
					auto keyValuePair = new afrl::cmasi::KeyValuePair;
					keyValuePair->setKey(std::string("RequestValidator"));
					keyValuePair->setValue(reasonForFailure.str());
					serviceStatus->getInfo().push_back(keyValuePair);
					keyValuePair = nullptr;
					sendSharedLmcpObjectBroadcastMessage(serviceStatus);
				}
			}
		}
	}

	bool TemporalService::isCheckAutomationRequestRequirements(const std::shared_ptr<uxas::messages::task::UniqueAutomationRequest>& uniqueAutomationRequest)
	{
		bool isReady{true};
		std::stringstream reasonForFailure;
		reasonForFailure << "Automation Request ID[" << uniqueAutomationRequest->getRequestID() << "] Not Ready ::" << std::endl;

		if (!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
		{
		// check for required entity configurations, if none are required, make sure there is at least one
			if (!m_availableConfigurationEntityIds.empty())
			{
				if (!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
				{
					for (auto& id : uniqueAutomationRequest->getOriginalRequest()->getEntityList())
					{
					//COUT_INFO_MSG("id[" << id << "]")
						if (m_availableConfigurationEntityIds.find(id) == m_availableConfigurationEntityIds.end())
						{
							reasonForFailure << "- EntityConfiguration for Entity Id[" << id << "] not available." << std::endl;
							isReady = false;
						}
					}
				}
			}
			else
			{
				reasonForFailure << "- No EntityConfigurations available." << std::endl;
				isReady = false;
			}

		// check for required entity states, if none are required, make sure there is at least one with matching configuration
			if (!m_availableStateEntityIds.empty())
			{
				for (auto& id : uniqueAutomationRequest->getOriginalRequest()->getEntityList())
				{
					bool isReadyLocal{false};
					if (m_availableStateEntityIds.find(id) != m_availableStateEntityIds.end())
					{
						isReadyLocal = true;
					}
					if(!isReadyLocal)
					{
						for(auto& planningState: uniqueAutomationRequest->getPlanningStates())
						{
							if(planningState->getEntityID() == id)
							{
								isReadyLocal = true;
								break;
							}
						}
					}
					if(!isReadyLocal)
					{
						isReady = false;
						reasonForFailure << "- EntityState for Entity Id[" << id << "] not available." << std::endl;
					}
				}
			}
			else
			{
				reasonForFailure << "- No EntityStates available." << std::endl;
				isReady = false;
			}
		}
	else //if(!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())
	{
		if (!m_availableConfigurationEntityIds.empty() && !m_availableStateEntityIds.empty())
		{
			bool isFoundAMatch{false};
			for (auto& id1 : m_availableConfigurationEntityIds)
			{
				for (auto& id2 : m_availableConfigurationEntityIds)
				{
					if (id1 == id2)
					{
						isFoundAMatch = true;
						break;
					}
				}
				if (isFoundAMatch)
				{
					break;
				}
			}
			if (!isFoundAMatch)
			{
				reasonForFailure << "- No EntityStates that match EntityConfigurations are available." << std::endl;
				isReady = false;
			}
		}
		else
		{
			if (m_availableConfigurationEntityIds.empty())
			{
				reasonForFailure << "- No EntityConfigurations available." << std::endl;
			}
			else
			{
				reasonForFailure << "- No EntityStates available." << std::endl;
			}
			isReady = false;
		}

	} //if(!uniqueAutomationRequest->getOriginalRequest()->getEntityList().empty())

	// check for required operating region and keepin/keepout zones
	if (uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion() != 0)
	{
		auto itOperatingRegion = m_availableOperatingRegions.find(uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion());
		if (itOperatingRegion != m_availableOperatingRegions.end())
		{
			for (auto & keepInArea : itOperatingRegion->second->getKeepInAreas())
			{
				if (m_availableKeepInZoneIds.find(keepInArea) == m_availableKeepInZoneIds.end())
				{
					reasonForFailure << "- KeepInArea Id[" << keepInArea << "] not available." << std::endl;
					isReady = false;
				}
			}
			for (auto & keepOutArea : itOperatingRegion->second->getKeepOutAreas())
			{
				if (m_availableKeepOutZoneIds.find(keepOutArea) == m_availableKeepOutZoneIds.end())
				{
					reasonForFailure << "- KeepOutArea Id[" << keepOutArea << "] not available." << std::endl;
					isReady = false;
				}
			}
		}
		else
		{
			reasonForFailure << "- OperatingRegion Id[" << uniqueAutomationRequest->getOriginalRequest()->getOperatingRegion() << "] not available." << std::endl;
			isReady = false;
		}
	}

	// check for required tasks and task requirements
	for (auto& taskId : uniqueAutomationRequest->getOriginalRequest()->getTaskList())
	{
		auto itTask = m_availableTasks.find(taskId);
		if (itTask != m_availableTasks.end())
		{
			auto itStartedTaskId = m_availableStartedTaskIds.find(taskId);
			if (itStartedTaskId != m_availableStartedTaskIds.end())
			{
				// check for specific task requirements
				if (itTask->second->getFullLmcpTypeName() == afrl::impact::AngledAreaSearchTask::Subscription)
				{
					auto angledAreaSearchTask = std::static_pointer_cast<afrl::impact::AngledAreaSearchTask>(itTask->second);
					if (angledAreaSearchTask->getSearchAreaID() != 0)
					{
						if (m_availableAreaOfInterestIds.find(angledAreaSearchTask->getSearchAreaID()) == m_availableAreaOfInterestIds.end())
						{
							reasonForFailure << "- AreaOfInterest Id[" << angledAreaSearchTask->getSearchAreaID() << "] not available." << std::endl;
							isReady = false;
						}
					}
				}
				else if (itTask->second->getFullLmcpTypeName() == afrl::impact::ImpactLineSearchTask::Subscription)
				{
					auto impactLineSearchTask = std::static_pointer_cast<afrl::impact::ImpactLineSearchTask>(itTask->second);
					if (impactLineSearchTask->getLineID() != 0)
					{
						if (m_availableLineOfInterestIds.find(impactLineSearchTask->getLineID()) == m_availableLineOfInterestIds.end())
						{
							reasonForFailure << "- LineOfInterest Id[" << impactLineSearchTask->getLineID() << "] not available." << std::endl;
							isReady = false;
						}
					}
				}
				else if (itTask->second->getFullLmcpTypeName() == afrl::impact::ImpactPointSearchTask::Subscription)
				{
					auto impactPointSearchTask = std::static_pointer_cast<afrl::impact::ImpactPointSearchTask>(itTask->second);
					if (impactPointSearchTask->getSearchLocationID() != 0)
					{
						if (m_availablePointOfInterestIds.find(impactPointSearchTask->getSearchLocationID()) == m_availablePointOfInterestIds.end())
						{
							reasonForFailure << "- LineOfInterest Id[" << impactPointSearchTask->getSearchLocationID() << "] not available." << std::endl;
							isReady = false;
						}
					}
				}
			}
			else
			{
				reasonForFailure << "- Task with the Id[" << taskId << "] not yet started." << std::endl;
				isReady = false;
			}
		}
		else
		{
			reasonForFailure << "- Task with the Id[" << taskId << "] not available." << std::endl;
			isReady = false;
		}
	}

	if (!isReady)
	{
		UXAS_LOG_WARN(reasonForFailure.str());
		COUT_INFO_MSG(reasonForFailure.str());
		auto serviceStatus = std::make_shared<afrl::cmasi::ServiceStatus>();
		serviceStatus->setStatusType(afrl::cmasi::ServiceStatusType::Information);
		auto keyValuePair = new afrl::cmasi::KeyValuePair;
		keyValuePair->setKey(std::string("RequestValidator"));
		keyValuePair->setValue(reasonForFailure.str());
		serviceStatus->getInfo().push_back(keyValuePair);
		keyValuePair = nullptr;
		sendSharedLmcpObjectBroadcastMessage(serviceStatus);
	}

	return (isReady);
}



}; //namespace service
}; //namespace uxas
