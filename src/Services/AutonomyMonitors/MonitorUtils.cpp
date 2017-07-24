#include "AutonomyMonitors/MonitorUtils.h"
#include <memory>
#include <iostream>

namespace uxas{
  namespace service {
    namespace monitoring {
      
      void  getCameraFootprintFromEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr,
					      std::vector< std::shared_ptr<afrl::cmasi::Location3D> > & footPrint,
					      double & camera_azimuth,
					      double & camera_elevation ){
        // First search over the payloads
        std::vector<afrl::cmasi::PayloadState*> payloads = ptr -> getPayloadStateList();
        for (afrl::cmasi::PayloadState * pay: payloads){
          // Dynamic cast the payload to a camera state
          afrl::cmasi::CameraState * cState = dynamic_cast<afrl::cmasi::CameraState*>(pay);
          if (cState){
            /*-- I will assume that this is not a big vector,
            so copying it is not a huge performance hit --*/
	    std::vector<afrl::cmasi::Location3D*> & camFootPrint = cState -> getFootprint();
	    for (auto loc: camFootPrint){
	      std::shared_ptr<afrl::cmasi::Location3D> new_loc = std::make_shared<afrl::cmasi::Location3D>(*loc);
	      footPrint.push_back(new_loc);
	    }
	    camera_azimuth = cState -> getAzimuth();
	    camera_elevation = cState -> getElevation();
	    return;
          }
        }


	camera_azimuth = 0.0;
	camera_elevation = 0.0;
	return;
      }


      bool checkCameraAngleInWedge_Util(std::vector<afrl::cmasi::Wedge*> const & all_wedges, double camera_azimuth, double camera_elevation) {
	for (auto wedge: all_wedges){
	  /* - Check azimuth -*/

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

      std::pair<double, double> get_east_north_coordinates(uxas::common::utilities::CUnitConversions & flatEarth,
							   afrl::cmasi::Location3D const * loc){
	double currentNorth_m, currentEast_m;
	double lat = loc -> getLatitude();
	double lon = loc -> getLongitude();
	
	flatEarth.ConvertLatLong_degToNorthEast_m(lat, lon, currentNorth_m, currentEast_m);
	return std::pair<double, double>(currentEast_m, currentNorth_m);
	
      }
      
    }
  }
}
