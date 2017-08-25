/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   STaliroTrajectoryPopulator.h
 * Author: etuncali
 *
 * Created on June 19, 2017, 10:21 AM
 */

#ifndef STALIROTRAJECTORYPOPULATOR_H
#define STALIROTRAJECTORYPOPULATOR_H

#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <map>
#include "UnitConversions.h"
#include "UxAS_Log.h"

namespace testgeneration
{
    namespace staliro
    {
        class c_TrajectoryPopulator
        {
        public:
            c_TrajectoryPopulator();
            virtual ~c_TrajectoryPopulator(){};
            
            void populateTrajectory(void* receivedLmcpMessage, 
                    std::map<int64_t, std::vector<double_t>>* trajectory,
                    std::map<int32_t, std::vector<std::string>>* trajectoryMapping);
            void setCameraPixelCount(int64_t vehicleId, 
                    int32_t horizontalPixelCount, 
                    int32_t longitudinalPixelCount);
            std::map<int64_t, uint32_t> vehicleTrajectoryStartIndex;
        protected:
            std::map<int64_t, double_t> cameraDiagonalPixelCount;
            uxas::common::utilities::CUnitConversions* flatEarth;
            double_t computeGroundSampleDistance(int vehicleId, 
                    double (&cameraFootprintCoordinates)[4][2]);
            uint32_t nextAvailableStartIndex;
            uint32_t sizeOfVehicleTrajectory;
        };
    }
}

#endif /* STALIROTRAJECTORYPOPULATOR_H */

