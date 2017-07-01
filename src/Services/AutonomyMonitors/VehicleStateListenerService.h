#ifndef D__VEHICLE_STATE_LISTENER_H__
#define D__VEHICLE_STATE_LISTENER_H__

/* 
   VehicleStateListenerService

   This service will continuously listen to the vehicle state sent 
   by the vehicles and store them. Upon termination, it prints
   the information on latitude/longitude/altitude to a new CSV file
   under the /tmp directory.

   Ideally, this file should have been placed under OpenUxAS/src/Services
   
   But to aid collaborative development, it is placed here in a fresh repository.

   Author: Sriram Sankaranarayanan
   Email: srirams AT colorado.edu

*/

#include "ServiceBase.h"
#include "afrl/cmasi/Location3D.h"
#include <ostream>
#include <map>
namespace uxas {
  namespace service {
    namespace test {
    
    
      /*! \class VehicleStateListenerService \brief This service listens
       * to the vehicle state sent by the vehicles and extracts their
       * positions over time.
       *
       * Configuration String: 
       *   None
       * 
       * Subscribed Messages:
       * 
       * 
       * Sent Messages: 
       *
       *
       */

      // All services in UxAS inherit from the public class ServiceBase
      class VehicleStateListenerService : public ServiceBase {
      public:
	/* Mimicked this code snippet below from 01_HelloWorld.cpp under src/Services/ */
	static const std::string &
	s_typeName()
	{
	  static std::string s_string("VehicleStateListenerService"); // The name of this service
	  return (s_string);
	};

	static const std::vector<std::string>
	s_registryServiceTypeNames()
	{
	  std::vector<std::string> rSTN = {s_typeName()};
	  return (rSTN);
	};

	static const std::string&
	s_directoryName(){
	  static std::string s_string("VehicleStateListenerService");
	  return (s_string);
	};
      
	static ServiceBase*
	create(){
	  return new VehicleStateListenerService;
	};

	/*-- end mimicing from HelloWorld Service --*/
	
	VehicleStateListenerService(); // Constructor

	virtual ~VehicleStateListenerService(); // Destructor

      private:

	// Also mimicking from HelloWorld Service
	static
	  ServiceBase::CreationRegistrar<VehicleStateListenerService> s_registrar; 


	/** Copy constructor not permitted in UxAS services */
	VehicleStateListenerService(VehicleStateListenerService const &) = delete;
      
	/** Copy assignment not permitted in UxAS services*/
	void operator= (VehicleStateListenerService const & ) = delete;

	/* Call back method: configure is called to configure the service 
	   We can pass in parameters through the XML */
	bool
	configure(const pugi::xml_node& serviceXmlNode) override;

	/* Call back method: initialize */
	bool initialize() override;

	/* call back method: start */
	bool start() override;
	
	/* call back method: terminate */
	bool terminate() override;

	/* call back method: processReceivedLmcpMessage */
	bool processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedMsg) override;

      private:
	/* Register a new vehicle ID */
	void registerVehicleID(int64_t vID);
	
	/* Register a vehicle state with given timeStamp, vehicle ID, location and energy */
	void registerVehicleState(int64_t timeStamp, int64_t vehicleID, afrl::cmasi::Location3D* loc, float energy);

      private:


	/*! \class EntityStateInfo
	 *  \brief Stores a list of latitude, longitude, altitude values for each vehicle
	 */
	class EntityStateInfo {
	private:
	  int64_t vID;
	  std::vector<double> v_lats;
	  std::vector<double> v_longs;
	  std::vector<double> v_alts;
	  std::vector<int64_t> v_times;
	  std::vector<double> v_energies;
	
	public:
	
	  
	EntityStateInfo(int64_t whoAmI):vID(whoAmI){} ;
	  
	EntityStateInfo(EntityStateInfo const & what)
	  :vID(what.vID),
	    v_lats(what.v_lats),
	    v_longs(what.v_longs),
	    v_alts(what.v_alts),
	    v_times(what.v_times),
	    v_energies(what.v_energies)
	      {}; 
	  
	  void addState(int64_t timeStamp, afrl::cmasi::Location3D* loc, float energyRemaining);

	  int64_t getVehicleID() const { return vID; };
	  
	  void dumpToFile(std::ostream& fHandle) const;
	};
	
	std::map<int64_t, EntityStateInfo> _m;
	
      }; // Class VehicleStateListenerService
    }; // namespace test
  }; // namespace Service
}; // namespace uxas

#endif 
