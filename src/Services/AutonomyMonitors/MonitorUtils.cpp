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


      bool checkCameraAngleInWedge_Util(std::vector<afrl::cmasi::Wedge*> const & all_wedges, afrl::cmasi::CameraState const * cState) {
	for (auto wedge: all_wedges){
	  /* - Check azimuth -*/
	  double camera_azimuth = cState -> getAzimuth();
	  double camera_elevation = cState -> getElevation();
	  double wedge_center_azimuth = wedge -> getAzimuthCenterline();
	  double wedge_azimuth_extent = wedge -> getAzimuthExtent();
	  if (camera_azimuth <= wedge_center_azimuth + wedge_azimuth_extent ||
	      camera_azimuth >= wedge_center_azimuth - wedge_azimuth_extent){
	    double wedge_center_vertical = wedge -> getVerticalCenterline();
	    double wedge_vertical_extent = wedge -> getVerticalExtent();
	    if (camera_elevation <= wedge_center_vertical + wedge_vertical_extent ||
		camera_elevation >= wedge_center_vertical - wedge_vertical_extent ){
	      return true;
	    }
	  } 
	}
	return false;
      }
      
    }
  }
}
