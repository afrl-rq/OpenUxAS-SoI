/*--
  MonitorUtils: A bunch of simple utilities that support the
  monitor tasks including extraction of various fields from the
  messages.
  */

#ifndef D__MONITOR__UTILS__H__
#define D__MONITOR__UTILS__H__

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/CameraState.h"
#include "afrl/cmasi/Wedge.h"
#include "UnitConversions.h"

#include <memory>      //int64_t
#include <vector>


namespace uxas {
    namespace service {
      namespace monitoring {
	
	void getCameraFootprintFromEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr,
					       std::vector< std::shared_ptr<afrl::cmasi::Location3D> > &  v,
					       double & camera_azimuth,
					       double & camera_elevation  );
	  bool checkCameraAngleInWedge_Util(std::vector<afrl::cmasi::Wedge*> const & all_wedges, double camera_azimuth, double camera_elevation);
	  std::pair<double, double> get_east_north_coordinates(uxas::common::utilities::CUnitConversions & flatEarth,
							       afrl::cmasi::Location3D const * loc);
      }
    }
}



#endif
