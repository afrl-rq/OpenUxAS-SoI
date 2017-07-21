#include "AutonomyMonitors/VehicleStateMessage.h"
#include "AutonomyMonitors/MonitorUtils.h"

namespace uxas{
  namespace service{
    namespace monitoring {
      
      bool VehicleStateMessage::checkCameraAngleInWedge(std::vector<afrl::cmasi::Wedge*> const & all_wedges) const{
	// First extract the camera angles
	std::vector<afrl::cmasi::PayloadState*> payloads = msg -> getPayloadStateList();
	for (auto pay: payloads){
	  auto cState = dynamic_cast<afrl::cmasi::CameraState*> (pay);
	  if (cState){
	    if ( checkCameraAngleInWedge_Util(all_wedges, cState))
	      return true;
	  }
	}
	/* -- No camera pointing inside a wedge --*/
	return false;
      }
    }
  }
}
