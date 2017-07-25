#include "AutonomyMonitors/VehicleStateMessage.h"
#include "AutonomyMonitors/MonitorUtils.h"

namespace uxas{
  namespace service{
    namespace monitoring {

      VehicleStateMessage::VehicleStateMessage(std::shared_ptr<afrl::cmasi::EntityState> what):
	  vehicleID(what -> getID()),
	  timeStamp(what -> getTime()),
	  cameraFootprintPolygon(),
	  camera_azimuth(0.0),
	  camera_elevation(0.0),
	  msg(what)
	{
	  afrl::cmasi::Location3D * loc = what -> getLocation();
	  where = std::make_shared<afrl::cmasi::Location3D>(*( what -> getLocation()));
	  getCameraFootprintFromEntityState(what, cameraFootprintPolygon, camera_azimuth, camera_elevation);
	};

      VehicleStateMessage::~VehicleStateMessage(){};
      
      bool VehicleStateMessage::checkCameraAngleInWedge(std::vector<afrl::cmasi::Wedge*> const & all_wedges) const{
	// First extract the camera angles	
	return checkCameraAngleInWedge_Util(all_wedges, camera_azimuth, camera_elevation);
      }
    }
  }
}
