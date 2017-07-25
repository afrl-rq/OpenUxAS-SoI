/*
* AutonomyMonitorServiceMain.h
*
*  Created on: Jul 2, 2017
*      Author: Sriram Sankaranarayanan
*/

#ifndef SRC_SERVICES_AUTONOMYMONITORS_AUTONOMYMONITORSERVICEMAIN_H_
#define SRC_SERVICES_AUTONOMYMONITORS_AUTONOMYMONITORSERVICEMAIN_H_

#include "ServiceBase.h"

namespace uxas {
  namespace service {
    namespace monitoring {

      class MonitorDB;
      
      /** \class AutonomyMonitorServiceMain
      *  \brief Provides the main class for the Autonomy monitoring service.
      *  This class will register for the appropriate messages and build the monitoring problem.
      *  It's eventual goal is to judge mission succes/failure, provide robustness estimate and
      *  finally provide diagnosis of failure cases
      */
      
      class AutonomyMonitorServiceMain : public uxas::service::ServiceBase {
      public:
        /* Mimicked this code snippet below from 01_HelloWorld.cpp under src/Services/ */
        static const std::string &
        s_typeName()
        {
          static std::string s_string("AutonomyMonitorServiceMain"); // The name of this service
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
          static std::string s_string("AutonomyMonitorServiceMain");
          return (s_string);
        };

        static ServiceBase*
        create(){
          return new AutonomyMonitorServiceMain;
        };

        /*-- end mimicing from HelloWorld Service --*/

        AutonomyMonitorServiceMain();
        virtual ~AutonomyMonitorServiceMain();

	
	void broadcastMessage(const std::shared_ptr<avtas::lmcp::Object> & msgToBroadcast) ;
	

      private:
        
	MonitorDB * monitorDB;


      private:

        // Also mimicking from HelloWorld Service
        static ServiceBase::CreationRegistrar<AutonomyMonitorServiceMain> s_registrar;


        /** Copy constructor not permitted in UxAS services */
        AutonomyMonitorServiceMain(AutonomyMonitorServiceMain const &) = delete;

        /** Copy assignment not permitted in UxAS services*/
        void operator= (AutonomyMonitorServiceMain const & ) = delete;

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

	
      };

    } /* namespace monitoring */
  } /* namespace service */
} /* namespace uxas */

#endif /* SRC_SERVICES_AUTONOMYMONITORS_AUTONOMYMONITORSERVICEMAIN_H_ */
