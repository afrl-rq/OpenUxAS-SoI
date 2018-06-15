// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_SensorManager.cpp
 * Author: steve
 * 
 * Created on January 26, 2016, 6:17 PM
 */


#include "SensorManagerService.h"

#include "afrl/cmasi/EntityConfiguration.h"
#include "afrl/cmasi/EntityConfigurationDescendants.h"
#include "afrl/cmasi/GimbalConfiguration.h"
#include "afrl/cmasi/CameraConfiguration.h"
#include "afrl/cmasi/RemoveTasks.h"
#include "uxas/messages/task/SensorFootprintResponse.h"
#include "uxas/messages/task/SensorFootprint.h"

#include "pugixml.hpp"
#include "Constants/Convert.h"

#include <sstream>      //std::stringstream
#include <iostream>     // std::cout, cerr, etc
#include <fstream>     // std::ifstream
#include <cstdint>
#include <memory>      //int64_t


#define STRING_COMPONENT_NAME "SensorManager"

#define STRING_XML_COMPONENT_TYPE STRING_COMPONENT_NAME

#define STRING_XML_COMPONENT "Component"
#define STRING_XML_TYPE "Type"

#define COUT_FILE_LINE_MSG(MESSAGE) std::cout << "SRM-SRM-SRM-SRM:: SensorManager:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();
#define CERR_FILE_LINE_MSG(MESSAGE) std::cerr << "SRM-SRM-SRM-SRM:: SensorManager:" << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();

#define MIMIMUM_ASSIGNED_ALTITUDE_M (10.0)    
#define GIMBAL_STEP_SIZE_RAD (5.0*n_Const::c_Convert::dDegreesToRadians())
#define HORIZANTAL_FOV_STEP_SIZE_DEG (5.0)

namespace uxas
{
namespace service
{
SensorManagerService::ServiceBase::CreationRegistrar<SensorManagerService>
SensorManagerService::s_registrar(SensorManagerService::s_registryServiceTypeNames());

SensorManagerService::SensorManagerService()
: ServiceBase(SensorManagerService::s_typeName(), SensorManagerService::s_directoryName())
{
};

SensorManagerService::~SensorManagerService()
{
};

bool
SensorManagerService::configure(const pugi::xml_node& ndComponent)

{
    bool isSuccess(true);
    std::string strBasePath = m_workDirectoryPath;
    uint32_t ui32EntityID = m_entityId;
    uint32_t ui32LmcpMessageSize_max = 100000;
    std::stringstream sstrErrors;

    std::string strComponentType = ndComponent.attribute(STRING_XML_TYPE).value();
    //assert(strComponentType==STRING_XML_COMPONENT_TYPE)
    addSubscriptionAddress(afrl::cmasi::RemoveTasks::Subscription);
    
    //ENTITY CONFIGURATIONS
    addSubscriptionAddress(afrl::cmasi::EntityConfiguration::Subscription);
    std::vector< std::string > childconfigs = afrl::cmasi::EntityConfigurationDescendants();
    for(auto child : childconfigs)
        addSubscriptionAddress(child);

    addSubscriptionAddress(uxas::messages::task::SensorFootprintRequests::Subscription);

    return (isSuccess);
}

bool
SensorManagerService::initialize()
{
    bool isSuccess{true};


    return (isSuccess);
}

bool
SensorManagerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
//example: if (afrl::cmasi::isServiceStatus(receivedLmcpMessage->m_object.get()))
{
    bool isMessageProcessed(false);
    auto entityConfiguration = std::dynamic_pointer_cast<afrl::cmasi::EntityConfiguration>(receivedLmcpMessage->m_object);
    if (entityConfiguration)
    {
        m_idVsEntityConfiguration.insert(std::make_pair(entityConfiguration->getID(), entityConfiguration));
        isMessageProcessed = true;
    }
    if (!isMessageProcessed)
    {
        auto sensorFootprintRequests = std::dynamic_pointer_cast<uxas::messages::task::SensorFootprintRequests>(receivedLmcpMessage->m_object);
        if (sensorFootprintRequests)
        {
            ProcessSensorFootprintRequests(sensorFootprintRequests);
            isMessageProcessed = true;
        }

    }
    if (!isMessageProcessed)
    {
        //CERR_FILE_LINE_MSG("WARNING::SensorManagerService::ProcessMessage: MessageType [" << receivedLmcpMessage->m_object->getFullLmcpTypeName() << "] not processed.")
    }
    return (false); // always false implies never terminating service from here
};

void SensorManagerService::ProcessSensorFootprintRequests(const std::shared_ptr<uxas::messages::task::SensorFootprintRequests>& sensorFootprintRequests)
{
    auto sensorFootprintResponse = std::make_shared<uxas::messages::task::SensorFootprintResponse>();
    sensorFootprintResponse->setResponseID(sensorFootprintRequests->getRequestID());
    for (auto& request : sensorFootprintRequests->getFootprints())
    {
        if (m_idVsEntityConfiguration.find(request->getVehicleID()) != m_idVsEntityConfiguration.end())
        {
            auto entityConfiguration = m_idVsEntityConfiguration.find(request->getVehicleID())->second;

            std::vector<afrl::cmasi::WavelengthBand::WavelengthBand> eligibleWavelengths;
            if (request->getEligibleWavelengths().empty())
            {
                // Default Value = AllAny
                eligibleWavelengths.push_back(afrl::cmasi::WavelengthBand::AllAny);
            }
            else
            {
                eligibleWavelengths = request->getEligibleWavelengths();
            }

            std::vector<float> groundSampleDistances;
            if (request->getGroundSampleDistances().empty())
            {
                // If list is empty, then footprint calculation uses the max ground sample distance for the specified altitude 
                groundSampleDistances.push_back(0.0);
            }
            else
            {
                groundSampleDistances = request->getGroundSampleDistances();
            }

            std::vector<float> aglAltitudes;
            if (request->getAglAltitudes().empty())
            {
                // if 'AglAltitudes' list is empty, sensor planner should use nominal altitude from entity configurations
                aglAltitudes.push_back(0.0);
            }
            else
            {
                aglAltitudes = request->getAglAltitudes();
            }

            std::vector<float> elevationAngles;
            if (request->getElevationAngles().empty())
            {
                // If list is empty, then uses an optimal elevation angle for achieving max GSD 
                elevationAngles.push_back(0.0);
            }
            else
            {
                elevationAngles = request->getElevationAngles();
            }

            for (auto& eligibleWavelength : eligibleWavelengths)
            {
                for (auto& groundSampleDistance : groundSampleDistances)
                {
                    for (auto& aglAltitude : aglAltitudes)
                    {
                        for (auto& elevationAngle : elevationAngles)
                        {
                            auto sensorFootprint = new uxas::messages::task::SensorFootprint();
                            FindSensorFootPrint(entityConfiguration, eligibleWavelength, groundSampleDistance, aglAltitude, elevationAngle, sensorFootprint);
                            // set IDs after sensorfootprint is found to facilitate retrieving stored footprints
                            sensorFootprint->setFootprintResponseID(request->getFootprintRequestID());
                            sensorFootprint->setVehicleID(entityConfiguration->getID());
                            sensorFootprintResponse->getFootprints().push_back(sensorFootprint);
                            sensorFootprint = nullptr; //gave up ownership
                        }
                    }
                }
            }
        } //if(m_idVsEntityConfiguration.find(request->getVehicleID()) != m_idVsEntityConfiguration.end())
    } //for (auto& request : sensorFootprintRequests->getFootprints())
    auto response = std::static_pointer_cast<avtas::lmcp::Object>(sensorFootprintResponse);
    sendSharedLmcpObjectBroadcastMessage(response);
};

void SensorManagerService::FindSensorFootPrint(const std::shared_ptr<afrl::cmasi::EntityConfiguration>& entityConfiguration,
        const afrl::cmasi::WavelengthBand::WavelengthBand& wavelength, const float& groundSampleDistance,
        const float& aglAltitude, const float& elevationAngle, uxas::messages::task::SensorFootprint* sensorFootprint)
{

    double altitudeAgl_m = aglAltitude;
    if (altitudeAgl_m < 0.001) //zero
    {
        altitudeAgl_m = entityConfiguration->getNominalAltitude();
    }
    double desiredGsd_m = groundSampleDistance;
    if (desiredGsd_m < 0.001) //zero
    {
        desiredGsd_m = 1000.0; // any GSD is good
    }
    sensorFootprint->setAchievedGSD(0.0); // no GSD found


    if (altitudeAgl_m >= MIMIMUM_ASSIGNED_ALTITUDE_M) //sanity check
    {
        bool firstGsdInitialized = false;
        for (auto& payloadConfiguration : entityConfiguration->getPayloadConfigurationList())
        {
            //find the camera configurations
            if (payloadConfiguration->getLmcpType() == afrl::cmasi::CMASIEnum::GIMBALCONFIGURATION)
            {
                auto gimbalConfiguration = static_cast<afrl::cmasi::GimbalConfiguration*> (payloadConfiguration);
                int64_t gimbalId = gimbalConfiguration->getPayloadID();
                //find gimbal elevation angle range
                //ASSUME:: min/max angles are between -180/180
                double gimbalElevationMin_rad = gimbalConfiguration->getMinElevation() * n_Const::c_Convert::dDegreesToRadians();
                gimbalElevationMin_rad = (gimbalElevationMin_rad<-n_Const::c_Convert::dPi()) ? (-(n_Const::c_Convert::dPi() - (1.0 * n_Const::c_Convert::dDegreesToRadians()))) : (gimbalElevationMin_rad); // can't calculate a useful footprint if not pointing down
                double gimbalElevationMax_rad = gimbalConfiguration->getMaxElevation() * n_Const::c_Convert::dDegreesToRadians();
                gimbalElevationMax_rad = (gimbalElevationMax_rad > 0.0) ? (-1.0 * n_Const::c_Convert::dDegreesToRadians()) : (gimbalElevationMax_rad); // can't calculate a useful footprint if not pointing down
                gimbalElevationMax_rad = (gimbalElevationMax_rad < gimbalElevationMin_rad) ? (gimbalElevationMin_rad) : (gimbalElevationMax_rad); //if wrong, choose min

                if (!gimbalConfiguration->getIsElevationClamped())
                {
                    // gimbal elevation is free to rotate 360deg, we need to point at the ground
                    gimbalElevationMax_rad = -1.0 * n_Const::c_Convert::dDegreesToRadians();
                    gimbalElevationMin_rad = -(n_Const::c_Convert::dPi() - (1.0 * n_Const::c_Convert::dDegreesToRadians()));
                }
                if (elevationAngle < 0.001)
                {
                    // elevation angle specified
                    gimbalElevationMin_rad = (elevationAngle <= gimbalElevationMin_rad) ? (gimbalElevationMin_rad) : (elevationAngle);
                    gimbalElevationMax_rad = gimbalElevationMin_rad;
                }
                if (gimbalElevationMin_rad < 0.0)
                {
                    for (double gimbalElevation_rad = gimbalElevationMin_rad;
                            gimbalElevation_rad <= gimbalElevationMax_rad;
                            gimbalElevation_rad += GIMBAL_STEP_SIZE_RAD)
                    {
                        double dDenominator = sin(-gimbalElevation_rad);
                        double dSlantRangeMin_m = (n_Const::c_Convert::bCompareDouble(dDenominator, 0.0, n_Const::c_Convert::enEqual)) ? (altitudeAgl_m) : (altitudeAgl_m / dDenominator);
                        // now find any cameras that are installed on this gimbal
                        for (auto& sensorID : gimbalConfiguration->getContainedPayloadList())
                        {
                            for (auto& payloadConfiguration2 : entityConfiguration->getPayloadConfigurationList())
                            {
                                if ((payloadConfiguration2->getLmcpType() == afrl::cmasi::CMASIEnum::CAMERACONFIGURATION) && (payloadConfiguration2->getPayloadID() == sensorID))
                                {
                                    //this is one of our cameras
                                    auto cameraConfiguration = static_cast<afrl::cmasi::CameraConfiguration*> (payloadConfiguration2);
                                    if ((cameraConfiguration->getSupportedWavelengthBand() == wavelength) ||
                                            (afrl::cmasi::WavelengthBand::AllAny == wavelength))
                                    {
                                        double dAspectRatio = (cameraConfiguration->getVideoStreamVerticalResolution() == 0) ? (1.0) :
                                                (static_cast<double> (cameraConfiguration->getVideoStreamHorizontalResolution()) / static_cast<double> (cameraConfiguration->getVideoStreamVerticalResolution()));
                                        double videoStreamResolutionMin = (cameraConfiguration->getVideoStreamHorizontalResolution() < cameraConfiguration->getVideoStreamVerticalResolution()) ?
                                                (cameraConfiguration->getVideoStreamHorizontalResolution()) :
                                                (cameraConfiguration->getVideoStreamVerticalResolution());

                                        std::vector<float> horizontalFieldOfViewList;
                                        if (cameraConfiguration->getFieldOfViewMode() == afrl::cmasi::FOVOperationMode::Discrete)
                                        {
                                            horizontalFieldOfViewList = cameraConfiguration->getDiscreteHorizontalFieldOfViewList();
                                        }
                                        else if (cameraConfiguration->getFieldOfViewMode() == afrl::cmasi::FOVOperationMode::Continuous)
                                        {
                                            for (double horizantalFov_deg = cameraConfiguration->getMinHorizontalFieldOfView();
                                                horizantalFov_deg <= cameraConfiguration->getMaxHorizontalFieldOfView();
                                                horizantalFov_deg += HORIZANTAL_FOV_STEP_SIZE_DEG)
                                            {
                                                horizontalFieldOfViewList.push_back(horizantalFov_deg);
                                            }
                                        }
                                        else
                                        {
                                            CERR_FILE_LINE_MSG("ERROR::FindSensorFootPrint:: unknown FieldOfViewMode[" << cameraConfiguration->getFieldOfViewMode() << "]")
                                        } //if(gimbalConfiguration->getFieldOfViewMode() == afrl::cmasi::FOVOperationMode::Discrete)
                                        for (auto& horizantalFov_deg : horizontalFieldOfViewList)
                                        {
                                            // calculate GSD
                                            double horizantalFov_rad = horizantalFov_deg * n_Const::c_Convert::dDegreesToRadians();
                                            double alpha_rad = (videoStreamResolutionMin <= 0.0) ? (n_Const::c_Convert::dPiO2() /*ERROR:: make it worst case*/) : (horizantalFov_rad / videoStreamResolutionMin);
                                            double gsd_m = dSlantRangeMin_m * sin(alpha_rad);
                                            double gsdDeltaDesired_m = abs(desiredGsd_m - gsd_m);
                                            // if the new GSD is closer to the desired than the last one
                                            if (!firstGsdInitialized || abs(desiredGsd_m - sensorFootprint->getAchievedGSD()) > gsdDeltaDesired_m)
                                            {
                                                firstGsdInitialized = true;

                                                sensorFootprint->setCameraID(sensorID);
                                                sensorFootprint->setGimbalID(gimbalId);
                                                sensorFootprint->setHorizontalFOV(horizantalFov_deg);
                                                sensorFootprint->setAglAltitude(altitudeAgl_m);
                                                sensorFootprint->setGimbalElevation(gimbalElevation_rad * n_Const::c_Convert::dRadiansToDegrees());
                                                sensorFootprint->setAspectRatio(dAspectRatio);
                                                sensorFootprint->setAchievedGSD(gsd_m);
                                                sensorFootprint->setCameraWavelength(cameraConfiguration->getSupportedWavelengthBand());

                                                CalculateSensorFootprint(horizantalFov_rad, dAspectRatio, gimbalElevation_rad, altitudeAgl_m, sensorFootprint);
                                            }
                                        }

                                    } //if(cameraConfiguration->getSupportedWavelengthBand() == wavelength)
                                }
                            } //for(auto itPayloadCamera=ptr_vGetPayloadConfigurationList()->begin();itPayloadCamera!=ptr_vGetPayloadConfigurationList()->end();itPayloadCamera++)
                        } //for(auto itSensorID=gimbalConfiguration->getContainedPayloadList().begi ...
                    } //for(double dGimbalElevation_rad=dGimbalElevationMin_rad; ...
                }
                else //if(dGimbalElevation_rad < 0.0)
                {
                    CERR_FILE_LINE_MSG("ProcessSensorFootprintRequests:WARNING:: Unable to point gimbal Id[" << gimbalId << "] towards ground. Minimum gimbal elevation angle(deg)[" << gimbalElevationMin_rad * n_Const::c_Convert::dRadiansToDegrees() << "]")
                } //if(dGimbalElevation_rad < 0.0)
            } //if(payloadGimbal->getLmcpType() == afrl::cmasi::CMASIEnum::GIMBALCONFIGURATION)
        } //for(auto itPayload=ptr_vGetPayloadConfigurationList()->begin();itPayload!=ptr_vGetPayloadConfigurationList()->end();itPayload++)
    } //if(dAssignedAltitude_m >= MIMIMUM_ASSIGNED_ALTITUDE_M)
} //void SensorManagerService::FindSensorFootPrint(const std::shared_ptr<afrl::cmasi::EntityConfiguration>& entityConfiguration, ...

void SensorManagerService::CalculateSensorFootprint(const double& horizantalFov_rad, const double& dAspectRatio, const double& dGimbalAngle_rad, const double altitudeAgl_m, uxas::messages::task::SensorFootprint* sensorFootprint)
{
    double verticalFov_rad = horizantalFov_rad / dAspectRatio;
    double gimbalAngleMax_rad = dGimbalAngle_rad + (verticalFov_rad / 2.0);
    gimbalAngleMax_rad = (gimbalAngleMax_rad > 0.0) ? (0.0) : ((gimbalAngleMax_rad<-n_Const::c_Convert::dPi()) ? (-n_Const::c_Convert::dPi()) : (gimbalAngleMax_rad));
    double dGimbalAngleMin_rad = dGimbalAngle_rad - (verticalFov_rad / 2.0);
    dGimbalAngleMin_rad = (dGimbalAngleMin_rad > 0.0) ? (0.0) : ((dGimbalAngleMin_rad<-n_Const::c_Convert::dPi()) ? (-n_Const::c_Convert::dPi()) : (dGimbalAngleMin_rad));

    double denominator = sin(-dGimbalAngle_rad);
    double slantRangeToCenter_m = (n_Const::c_Convert::bCompareDouble(denominator, 0.0, n_Const::c_Convert::enEqual)) ? (0.0) : (altitudeAgl_m / denominator);
    denominator = tan(-dGimbalAngle_rad);
    double horizantalToCenter_m = (n_Const::c_Convert::bCompareDouble(denominator, 0.0, n_Const::c_Convert::enEqual)) ? (0.0) : (altitudeAgl_m / denominator);
    denominator = tan(-gimbalAngleMax_rad);
    double horizantalToLeadingEdge_m = (n_Const::c_Convert::bCompareDouble(denominator, 0.0, n_Const::c_Convert::enEqual)) ? (0.0) : (altitudeAgl_m / denominator);
    denominator = tan(-dGimbalAngleMin_rad);
    double horizantalToTrailingEdge_m = (n_Const::c_Convert::bCompareDouble(denominator, 0.0, n_Const::c_Convert::enEqual)) ? (0.0) : (altitudeAgl_m / denominator);

    double widthCenter_m = 2.0 * slantRangeToCenter_m * tan(0.5 * horizantalFov_rad);


    sensorFootprint->setHorizontalToLeadingEdge(horizantalToLeadingEdge_m);
    sensorFootprint->setHorizontalToTrailingEdge(horizantalToTrailingEdge_m);
    sensorFootprint->setHorizontalToCenter(horizantalToCenter_m);
    sensorFootprint->setWidthCenter(widthCenter_m);
    sensorFootprint->setSlantRangeToCenter(slantRangeToCenter_m);
}


}; //namespace service
}; //namespace uxas
