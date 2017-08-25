#include "STaliroTrajectoryPopulator.h"
#include "avtas/lmcp/Factory.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/CameraState.h"
#include <cmath>

#define LMCP_NAME_INDEX 0
#define FILTERING_FIELD_NAME_INDEX 1
#define FILTERING_FIELD_VALUE_INDEX 2
#define FIELD_NAME_INDEX 3

namespace testgeneration
{
    namespace staliro
    {
        c_TrajectoryPopulator::c_TrajectoryPopulator()
        {
            uxas::common::utilities::CUnitConversions* flatEarth = new uxas::common::utilities::CUnitConversions();
        }
        
        void c_TrajectoryPopulator::setCameraPixelCount(int64_t vehicleId, 
                int32_t horizontalPixelCount, 
                int32_t longitudinalPixelCount)
        {
            double_t pixelCount = 1.0;
            double_t tempPixelCount = (double) (std::sqrt(std::pow((double_t) horizontalPixelCount, 2.0) 
                    + std::pow((double_t) longitudinalPixelCount, 2.0)));
            if (tempPixelCount > 1.0)
            {
                pixelCount = tempPixelCount;
            }
            cameraDiagonalPixelCount[vehicleId] = pixelCount;
        }
        
        double_t c_TrajectoryPopulator::computeGroundSampleDistance(int vehicleId, 
                double (&cameraFootprintCoordinates)[4][2])
        {
            double_t gsd = 0.0;
            uxas::common::utilities::CUnitConversions cUnitConversions;
            
            double_t dist_diag_1 = cUnitConversions.dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(
                    cameraFootprintCoordinates[0][0],
                    cameraFootprintCoordinates[0][1],
                    cameraFootprintCoordinates[2][0],
                    cameraFootprintCoordinates[2][1]);

            double_t dist_diag_2 = cUnitConversions.dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(
                    cameraFootprintCoordinates[1][0],
                    cameraFootprintCoordinates[1][1],
                    cameraFootprintCoordinates[3][0],
                    cameraFootprintCoordinates[3][1]);
            
            double_t pixelCount = 1.0;
            if (cameraDiagonalPixelCount.find(vehicleId) != cameraDiagonalPixelCount.end())
            {
                pixelCount = cameraDiagonalPixelCount[vehicleId];
            }
            double_t gsd_1 = dist_diag_1 / pixelCount;
            double_t gsd_2 = dist_diag_2 / pixelCount;
            gsd = (gsd_1 < gsd_2) ? gsd_2:gsd_1;
            return gsd;
        }
        
        void c_TrajectoryPopulator::populateTrajectory(
            void* receivedLmcpMessage, 
                std::map<int64_t, std::vector<double_t>>* trajectory,
                std::map<int32_t, std::vector<std::string>>* trajectoryMapping)
        {
            for (auto mappingIter = (*trajectoryMapping).begin(); 
                    mappingIter != (*trajectoryMapping).end(); 
                    mappingIter++)
            {
                if (((avtas::lmcp::Object *) receivedLmcpMessage)->getLmcpTypeName() == mappingIter->second.at(LMCP_NAME_INDEX))
                {
                    // Would be perfect to make the following automatically reconfigurable instead of the hard coded behavior for different type of messages.
                    if (mappingIter->second.at(LMCP_NAME_INDEX) == "AirVehicleState")
                    {
                        afrl::cmasi::AirVehicleState* airVehicleState = (afrl::cmasi::AirVehicleState*) receivedLmcpMessage;
                        if (mappingIter->second.at(FILTERING_FIELD_NAME_INDEX) == "ID")
                        {
                            if (airVehicleState->getID() == std::stoi(mappingIter->second.at(FILTERING_FIELD_VALUE_INDEX)))
                            {
                                int64_t curTime = airVehicleState->getTime();
                                if ( (*trajectory).find(curTime) == (*trajectory).end() )
                                {
                                    for (uint32_t i = 0; i < trajectoryMapping->size(); i++)
                                    {
                                        (*trajectory)[curTime].push_back(0.0);
                                    }
                                }
                                
                                // This list has to be extended manually to support more variety of data in the trajectory.
                                if (mappingIter->second.at(FIELD_NAME_INDEX) == "Location.Location3D.Latitude")
                                {
                                    (*trajectory)[curTime][mappingIter->first] = airVehicleState->getLocation()->getLatitude();
                                }
                                else if (mappingIter->second.at(FIELD_NAME_INDEX) == "Location.Location3D.Longitude")
                                {
                                    (*trajectory)[curTime][mappingIter->first] = airVehicleState->getLocation()->getLongitude();
                                }
                                else if (mappingIter->second.at(FIELD_NAME_INDEX) == "Location.Location3D.Altitude")
                                {
                                    (*trajectory)[curTime][mappingIter->first] = airVehicleState->getLocation()->getAltitude();
                                }
                                else if (mappingIter->second.at(FIELD_NAME_INDEX) == "Airspeed")
                                {
                                    (*trajectory)[curTime][mappingIter->first] = airVehicleState->getAirspeed();
                                }
                                else if (mappingIter->second.at(FIELD_NAME_INDEX) == "VerticalSpeed")
                                {
                                    (*trajectory)[curTime][mappingIter->first] = airVehicleState->getVerticalSpeed();
                                }
                                else if (mappingIter->second.at(FIELD_NAME_INDEX) == "gsd")
                                {
                                    std::vector< afrl::cmasi::PayloadState* > payloadStateList = airVehicleState->getPayloadStateList();

                                    double_t cameraFootprintCoords[4][2] = {{0,0}, {0,0}, {0,0}, {0,0}};
                                    for (std::vector< afrl::cmasi::PayloadState* >::iterator plIter = payloadStateList.begin(); 
                                            plIter < payloadStateList.end(); 
                                            plIter++)
                                    {
                                        if ((*plIter)->getLmcpTypeName() == "CameraState")
                                        {
                                            std::vector<afrl::cmasi::Location3D*> footprintVector = static_cast<afrl::cmasi::CameraState*>(*plIter)->getFootprint();
                                            int curInd = 0;
                                            for (auto fpIter = footprintVector.begin(); fpIter < footprintVector.end(); fpIter++)
                                            {
                                                if (curInd < 4)
                                                {
                                                    cameraFootprintCoords[curInd][0] = (*fpIter)->getLatitude();
                                                    cameraFootprintCoords[curInd][1] = (*fpIter)->getLongitude();
                                                    curInd++;
                                                }
                                            }
                                        }
                                    }
                                    double_t gsd = computeGroundSampleDistance(airVehicleState->getID(), cameraFootprintCoords);
                                    
                                    (*trajectory)[curTime][mappingIter->first] = gsd;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
