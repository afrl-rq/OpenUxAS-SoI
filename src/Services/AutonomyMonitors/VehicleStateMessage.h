#ifndef D__VEHICLE_STATE_MESSAGE__H__
#define D__VEHICLE_STATE_MESSAGE__H__

#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/EntityState.h"
#include "AutonomyMonitors/MonitorUtils.h"
namespace uxas{
  namespace service{
    namespace monitoring {
      class VehicleStateMessage {
      public:
	VehicleStateMessage(std::shared_ptr<afrl::cmasi::EntityState> what);
	~VehicleStateMessage();

	int64_t getVehicleID() const { return vehicleID;}
	int64_t getTimeStamp() const { return timeStamp; }
	double getLatitude() const { return where -> getLatitude(); }
	double getLongitude() const { return where -> getLongitude(); }
	double getAltitude() const { return (double) where -> getAltitude(); }
	std::vector< std::shared_ptr< afrl::cmasi::Location3D> > const & getCameraFootprint() const { return cameraFootprintPolygon; }

	/*-- Check if for a given vehicle state, the camera angle lies within the wedges required by a search task --*/
	bool checkCameraAngleInWedge(std::vector<afrl::cmasi::Wedge*> const & all_wedges) const;

	double getCameraAzimuth() const { return camera_azimuth; }
	double getCameraElevation() const { return camera_elevation; }

      protected:
	int64_t vehicleID;
	int64_t timeStamp;
	std::shared_ptr<afrl::cmasi::Location3D> where;
	std::vector<std::shared_ptr< afrl::cmasi::Location3D> > cameraFootprintPolygon;
	std::shared_ptr<afrl::cmasi::EntityState> msg;
	double camera_azimuth;
	double camera_elevation;

	
      };

    };
  };
};

#endif
