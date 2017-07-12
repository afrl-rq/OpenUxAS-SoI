#include "AutonomyMonitors/MonitorUtils.h"
#include <memory>
#include <iostream>

namespace uxas{
  namespace service {
    namespace monitoring {
      std::vector<afrl::cmasi::Location3D*> getCameraFootprintFromEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr ){
        // First search over the payloads
        std::vector<afrl::cmasi::PayloadState*> payloads = ptr -> getPayloadStateList();
        for (afrl::cmasi::PayloadState * pay: payloads){
          // Dynamic cast the payload to a camera state
          afrl::cmasi::CameraState * cState = dynamic_cast<afrl::cmasi::CameraState*>(pay);
          if (cState){
            /*-- I will assume that this is not a big vector,
            so copying it is not a huge performance hit --*/
            return cState -> getFootprint();
          }
        }
        // Otherwise, the vehicle does not have a camera
        std::vector<afrl::cmasi::Location3D*> dummy;
        return dummy; // Return a empty vector and hope for the best.
      }
    }
  }
}
