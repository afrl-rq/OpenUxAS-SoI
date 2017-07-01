#include "FileSystemUtilities.h"
#include "VehicleStateListenerService.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/AirVehicleState.h"
#include "afrl/cmasi/AirVehicleConfiguration.h"
#include <iostream>
#include <sstream>
#include <fstream>
#include <cstdint>
#include <memory>
#include <iomanip>

#define STRING_COMPONENT_NAME "VehicleStateListenerService"
#define SAVE_PATH "/tmp/"

namespace uxas{
  namespace service {
    namespace test{
    // This apparently registers the service
    VehicleStateListenerService::ServiceBase::CreationRegistrar<VehicleStateListenerService>
    VehicleStateListenerService::s_registrar(VehicleStateListenerService::s_registryServiceTypeNames());

    // Constructor.
    VehicleStateListenerService::VehicleStateListenerService()
      :ServiceBase(VehicleStateListenerService::s_typeName(), VehicleStateListenerService::s_directoryName())
    {};

    //Destructor
    VehicleStateListenerService::~VehicleStateListenerService()
    {};

    //Configuration
    bool VehicleStateListenerService::configure(const pugi::xml_node & ndComponent){
      std::cout << "VehicleStateListenerService: Configured." << std::endl;
      // Add the subscription to messages
      addSubscriptionAddress(afrl::cmasi::AirVehicleConfiguration::Subscription);
      addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
      return true;  // Always a success, for now!
    }

    bool VehicleStateListenerService::initialize()
    {
      return true;
    }

    bool VehicleStateListenerService::start(){
      std::cout << "VehicleStateListenerService: STARTED." << std::endl;
      return true;
    }

    bool VehicleStateListenerService::terminate(){
      std::cout << "VehicleStateListenerService: TERMINATED." << std::endl;
      /* -- Dump the data into a CSV file, how? --*/
      std::string fileStem;
      std::string basePath(SAVE_PATH);
      std::stringstream baseName;
      baseName << "ID_"<< m_entityId << "_";
      bool isAddExtension=false;
      bool isSuccess = uxas::common::utilities::c_FileSystemUtilities::bFindUniqueFileName(baseName.str(), basePath, fileStem, isAddExtension);

      
      for (auto it = _m.begin(); it != _m.end(); ++it){
	EntityStateInfo const & eInfo = it -> second;
	std::string fileName = fileStem + "Vehicle_"+std::to_string(eInfo.getVehicleID())+".csv";
	std::ofstream fHandle(fileName);
	eInfo.dumpToFile(fHandle);
	fHandle.close();
	std::cout << "VehicleStateListenerService: Dumped Information to file " << fileName << std::endl;
      }
      
      return true;
    }

    bool VehicleStateListenerService::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage){
      // Is it an entity configuration message
      if (afrl::cmasi::isAirVehicleConfiguration(receivedLmcpMessage->m_object)){
	// Cast it as an entity state configuration message
	auto msg = std::static_pointer_cast<afrl::cmasi::AirVehicleConfiguration> (receivedLmcpMessage->m_object);
	// Record the entity ID since we will have to track air vehicle states for this entity
	int64_t vehicle_id = msg-> getID();
	this -> registerVehicleID(vehicle_id);
      }

      if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage -> m_object)){
	auto msg = std::static_pointer_cast<afrl::cmasi::AirVehicleState> (receivedLmcpMessage -> m_object);
	int64_t vehicle_id = msg -> getID();
	afrl::cmasi::Location3D* loc = msg -> getLocation();
	float energy = msg -> getEnergyAvailable();
	int64_t timestamp = msg -> getTime();
	this -> registerVehicleState(timestamp, vehicle_id, loc, energy);
      }
      return false;
    };


    void VehicleStateListenerService::registerVehicleID(int64_t vID){
      /* Check if the vehicle ID is already present. If yes, then warn. */
      auto it = _m.find(vID);
      if (it == _m.end()){
	/*- Create a new Entity State Information Object -*/
	EntityStateInfo eInfo(vID);
	_m.insert(std::pair<int64_t, EntityStateInfo>(vID, eInfo));
      } else {
	/*- Issue a warning about this situation. -*/
	UXAS_LOG_WARN(s_typeName(), "::VehicleStateListenerService::registerVehicleID(int64_t) - received multiple registrations for vehicle id ", vID);
      }
      return;
    };

    void VehicleStateListenerService::registerVehicleState(int64_t timeStamp, int64_t vehicleID, afrl::cmasi::Location3D* loc, float energyLeft){
      /* Check that the vehicle ID is present */
      auto it = _m.find(vehicleID);
      if (it == _m.end()){
	UXAS_LOG_WARN(s_typeName(), "::VehicleStateListenerService::registerVehicleState(..) - Unknown vehicle ID in air vehicle state message: " , vehicleID);
	this -> registerVehicleID(vehicleID);
      } else {
	EntityStateInfo & eInfo = it -> second;
	eInfo.addState(timeStamp,loc,energyLeft);
      }
      return;
    };

    void VehicleStateListenerService::EntityStateInfo::addState(int64_t tStamp, afrl::cmasi::Location3D* loc, float energy){
      v_times.push_back(tStamp);
      v_energies.push_back(energy);
      v_lats.push_back(loc -> getLatitude());
      v_longs.push_back(loc -> getLongitude());
      if (loc -> getAltitudeType() == afrl::cmasi::AltitudeType::MSL){
	v_alts.push_back(loc -> getAltitude());
      } else {
	double alt = loc -> getAltitude();
	UXAS_LOG_WARN(s_typeName(), "::VehicleStateListenerService::EntityStateInfo.addstate(..) - ASL altitude measurement obtained " , alt, "at time ", tStamp );
	v_alts.push_back(alt);
      }
    };

      void VehicleStateListenerService::EntityStateInfo::dumpToFile(std::ostream & where) const{
	int n = v_times.size();
	where << "TIME, LAT, LONG, ALT, ENERGY" << std::endl;
	for (int i=0; i < n; ++i){
	  where << v_times[i] << ","
		<< std::setprecision(12) << v_lats[i] << ","
		<< std::setprecision(12) << v_longs[i] << ","
		<< std::setprecision(3) << v_alts[i] << ","
		<< std::setprecision(3) << v_energies[i] << std::endl;
	}
	return;
      };
      
      
    };
  }; // namespace service
}; // namespace uxas
