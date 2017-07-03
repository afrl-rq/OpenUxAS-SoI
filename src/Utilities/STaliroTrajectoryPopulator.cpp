#include "STaliroTrajectoryPopulator.h"
#include "avtas/lmcp/Factory.h"
#include "afrl/cmasi/AirVehicleState.h"
namespace testgeneration
{
    namespace staliro
    {
        testgeneration::staliro::c_TrajectoryPopulator::c_TrajectoryPopulator()
        {
            // Optionally a more generalizable configuration can be read here.
            // For the scope of this project, we will hard code which fields of 
            // which messages will be added to the trajectory.
        }
        

        void testgeneration::staliro::c_TrajectoryPopulator::populateTrajectory(
            void* receivedLmcpMessage, std::map<int64_t, std::vector<double>>* trajectory)
        {
            afrl::cmasi::AirVehicleState* airVehicleState = (afrl::cmasi::AirVehicleState*) receivedLmcpMessage;
            int64_t curTime = airVehicleState->getTime();
            
            std::map<int64_t, std::vector<double>>::iterator curIter = (*trajectory).find(curTime);
            
            if (curIter == (*trajectory).end())
            {
                if (!trajectory->empty() && (trajectory->rbegin()->first < curTime))
                {
                    (*trajectory)[curTime] = (*trajectory).rbegin()->second;
                }
                else
                {
                    for (int i = 0; i < 4; i++)
                    {
                        (*trajectory)[curTime].push_back(0.0);
                    }
                }
            }
            
            double curLatitude = airVehicleState->getLocation()->getLatitude();
            double curLongitude = airVehicleState->getLocation()->getLongitude();
            uint32_t indexStart = 0;

            if (airVehicleState->getID() == 400)
            {
                indexStart = 0;
            }
            else if (airVehicleState->getID() == 500)
            {
                indexStart = 2;
            }
            (*trajectory)[curTime][indexStart] = curLatitude;
            (*trajectory)[curTime][indexStart+1] = curLongitude;
        }
    }
}
