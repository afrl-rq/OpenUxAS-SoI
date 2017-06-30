#ifndef D__VEHICLE_STATE_LISTENER_H__
#define D__VEHICLE_STATE_LISTENER_H__

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
      class VehicleStateListenerService : public ServiceBase {
      public:
	static const std::string &
	s_typeName()
	{
	  static std::string s_string("VehicleStateListenerService");
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

	VehicleStateListenerService();

	virtual ~VehicleStateListenerService();

      private:

	static
	  ServiceBase::CreationRegistrar<VehicleStateListenerService> s_registrar;


	/** brief copy constructor not permitted */
	VehicleStateListenerService(VehicleStateListenerService const &) = delete;
      
	/** brief copy assignment not permitted */
	void operator= (VehicleStateListenerService const & ) = delete;

	bool
	configure(const pugi::xml_node& serviceXmlNode) override;

	bool initialize() override;
	bool start() override;

	bool terminate() override;

	bool processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedMsg) override;

	void registerVehicleID(int64_t vID);

	void registerVehicleState(int64_t timeStamp, int64_t vehicleID, afrl::cmasi::Location3D* loc, float energy);

      private:


	/*! \class EntityStateInfo
	 *  \brief Stores a list of latitude, longitude, altitude values for each entity.
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
