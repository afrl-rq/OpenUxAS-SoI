#include "STaliroTrajectoryPopulator.h"
#include "avtas/lmcp/Factory.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/CameraState.h"
#include <cmath>

namespace testgeneration
{
    namespace staliro
    {
        c_TrajectoryPopulator::c_TrajectoryPopulator()
        {
            uxas::common::utilities::CUnitConversions* flatEarth = new uxas::common::utilities::CUnitConversions();
            // Optionally a more generalizable configuration can be read here.
            // For the scope of this project, we will hard code which fields of 
            // which messages will be added to the trajectory.
        }
        
        void c_TrajectoryPopulator::setCameraPixelCount(int64_t vehicleId, 
                int32_t horizontalPixelCount, 
                int32_t longitudinalPixelCount)
        {
            double_t pixelCount = std::sqrt(std::pow((double_t) horizontalPixelCount, 2.0) 
                    + std::pow((double_t) longitudinalPixelCount, 2.0));
            if (pixelCount < 1.0)
            {
                pixelCount = 1.0;
            }
            cameraDiagonalPixelCount[vehicleId] = pixelCount;
        }
        
        double_t c_TrajectoryPopulator::computeGroundSampleDistance(int64_t vehicleId, 
                double_t (&cameraFootprintCoordinates)[4][2])
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
            void* receivedLmcpMessage, std::map<int64_t, std::vector<double_t>>* trajectory)
        {
            afrl::cmasi::AirVehicleState* airVehicleState = (afrl::cmasi::AirVehicleState*) receivedLmcpMessage;
            int64_t curTime = airVehicleState->getTime();
            
            std::map<int64_t, std::vector<double_t>>::iterator curIter = (*trajectory).find(curTime);
            
            if (curIter == (*trajectory).end())
            {
                if (!trajectory->empty() && (trajectory->rbegin()->first < curTime))
                {
                    (*trajectory)[curTime] = (*trajectory).rbegin()->second;
                }
                else
                {
                    for (int i = 0; i < 8; i++)
                    {
                        (*trajectory)[curTime].push_back(0.0);
                    }
                }
            }
            
            double_t curLatitude = airVehicleState->getLocation()->getLatitude();
            double_t curLongitude = airVehicleState->getLocation()->getLongitude();
            double_t curAltitude = airVehicleState->getLocation()->getAltitude();
            std::vector< afrl::cmasi::PayloadState* > payloadStateList = 
                    airVehicleState->getPayloadStateList();

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
            double_t gsd = computeGroundSampleDistance(airVehicleState->getID(), 
                    cameraFootprintCoords);
            
            uint32_t indexStart = 0;

            if (airVehicleState->getID() == 400)
            {
                indexStart = 0;
            }
            else if (airVehicleState->getID() == 500)
            {
                indexStart = 4;
            }
            (*trajectory)[curTime][indexStart] = curLatitude;
            (*trajectory)[curTime][indexStart+1] = curLongitude;
            (*trajectory)[curTime][indexStart+2] = curAltitude;
            (*trajectory)[curTime][indexStart+3] = gsd;
        }
    }
}
