--  see OpenUxAS\src\Communications\LmcpObjectNetworkClientBase.h

with DOM.Core;
with AVTAS.LMCP.Object;  use AVTAS.LMCP.Object;
with UxAS.Comms.Data.LMCP_Messages;                 use UxAS.Comms.Data.LMCP_Messages;
with UxAS.Comms.LMCP_Object_Message_Sender_Pipes;   use UxAS.Comms.LMCP_Object_Message_Sender_Pipes;
with UxAS.Comms.LMCP_Object_Message_Receiver_Pipes; use UxAS.Comms.LMCP_Object_Message_Receiver_Pipes;
with UxAS.Comms.Data.Addressed.Attributed;          use UxAS.Comms.Data.Addressed.Attributed;

package UxAS.Comms.LMCP_Net_Client
is
   pragma Elaborate_Body;

   type LMCP_Object_Network_Client_Base is abstract tagged limited private;

   type LMCP_Object_Network_Client_Base_Reference is access all LMCP_Object_Network_Client_Base;

   type Any_LMCP_Object_Network_Client_Base is access all LMCP_Object_Network_Client_Base'Class;

   procedure Construct_Client (This : in out LMCP_Object_Network_Client_Base);
   --  the ctor, must be manually called in the SPARK version since no Controlled types allowed

   type Receive_Processing_Type is (LMCP, Serialized_LMCP);
   --  LMCP objects are de-serialized
   --  Serialized_LMCP objects are not de-serialized

   --      s_entityIdPrefix() { static std::string s_string("eid"); return (s_string); };
   function Entity_Id_Prefix return String;

   --  s_serviceIdPrefix string (leading characters for indicating that a service ID follows)
   --  @return
   --
   --      static std::string&
   --      s_serviceIdPrefix() { static std::string s_string(".sid"); return (s_string); };
   function Service_Id_Prefix return String;

   --  s_serviceIdAllSuffix string (trailing characters that are appended to entity cast address
   --  to form cast-to-all services of a specific entity)
   --  @return
   --
   --      static std::string&
   --      s_serviceIdAllSuffix() { static std::string s_string(".sidall"); return (s_string); };
   function Service_Id_All_Suffix return String;

   --   Multi-cast entity-based subscription address string
   --
   --  @param entityId UxAS entity ID.
   --  @return address string to used to send a message to all services hosted by
   --  a particular UxAS entity.
   --
   --      static std::string
   --      getEntityCastAddress(const uint32_t entityId)
   function Entity_Cast_Address (Entity_Id : UInt32) return String;

   --   Multi-cast subscription address string that addresses a message
   --  to all services of a specific entity.
   --
   --  @param entityId UxAS entity ID.
   --  @return address string to used to send a message to all services hosted by
   --  a particular UxAS entity.
   --
   --      static std::string
   --      getEntityServicesCastAllAddress(const uint32_t entityId)
   function Get_Entity_Services_Cast_All_Address (Entity_Id : UInt32) return String;

   --   Uni-cast service-based subscription address string
   --
   --  @param entityId UxAS entity ID.
   --  @param networkClientId UxAS bridge or service ID.
   --  @return address string to used to send a message to a specific service
   --  hosted by a particular UxAS entity.
   --
   function Network_Client_Unicast_Address (Entity_Id : Uint32;  Network_Client_Id : Int64)
     return String;

   --   Multi-cast entity-based subscription address string
   --
   --  @param entityId UxAS entity ID.
   --  @return address string to used to send a message to all services hosted by
   --  a particular UxAS entity.
   --
   --      static std::string
   --      getEntityCastAddress(const std::string entityId)
   function Entity_Cast_Address (Entity_Id : String) return String;

   --   Uni-cast service-based subscription address string
   --
   --  @param entityId UxAS entity ID.
   --  @param networkClientId UxAS bridge or service ID.
   --  @return address string to used to send a message to a specific service
   --  hosted by a particular UxAS entity.
   --
   --      static std::string
   --      getNetworkClientUnicastAddress(const uint32_t entityId, const std::string networkClientId)
   function Get_Network_Client_Unicast_Address
     (Entity_Id         : UInt32;
      Network_Client_Id : String)
     return String;

   --   Uni-cast service-based subscription address string
   --
   --  @param entityId UxAS entity ID.
   --  @param networkClientId UxAS bridge or service ID.
   --  @return address string to used to send a message to a specific service
   --  hosted by a particular UxAS entity.
   --
   --      static std::string
   --      getNetworkClientUnicastAddress(const std::string& entityId, const std::string& networkClientId)
   function Get_Network_Client_Unicast_Address
     (Entity_Id         : String;
      Network_Client_Id : String)
     return String;

   --      static std::string
   --      getNetworkClientUnicastAddress(const std::string& entityId, const int64_t& networkClientId)
   function Get_Network_Client_Unicast_Address
     (Entity_Id         : String;
      Network_Client_Id : Int64)
     return String;

   --      static int64_t
   --      getUniqueEntitySendMessageId()
   procedure Get_Unique_Entity_Send_Message_Id (Value : out Int64);

   --  The getUniqueNetworkClientId returns a unique service ID.
   --  It returns the ID from a call to getUniqueNetworkClientId(), which are used as service IDs
   --
   --  @return unique service ID.
   --
   --      static int64_t
   --      getUniqueNetworkClientId()
   procedure Get_Unique_Network_Client_Id (Value : out Int64);

   --  Type name for the LmcpObjectNetworkClientBase class
   --      static const std::string&
   --      s_typeName()
   Type_Name : constant String := "LmcpObjectNetworkClientBase";

   --  protected: but made public for sake of subclasses outside the package hierarchy  -----------
   --
   --  To be overridden by subclasses

   --  The virtual configure method is invoked by the
   --  LmcpObjectNetworkClientBase class after completing its
   --  own configuration.
   --
   --  @param xmlNode XML node containing object configurations.
   --  @return true if configuration succeeds; false if configuration fails.
   --
   --      virtual
   --      bool
   --      configure(const pugi::xml_node& xmlNode) { return (true); };
   procedure Configure
     (This     : in out LMCP_Object_Network_Client_Base;
      XML_Node : DOM.Core.Element;
      Result   : out Boolean)
     is abstract;

   --  The virtual initialize method is invoked by the
   --  LmcpObjectNetworkClientBase class after completing
   --  configurations and before startup.
   --
   --  @return true if initialization succeeds; false if initialization fails.
   --
   --      virtual
   --      bool
   --      initialize() --  { return (true); };
   procedure Initialize
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean);

   --  The virtual start method is invoked by the
   --  LmcpObjectNetworkClientBase class after initialization and
   --  before starting its own thread.
   --
   --  @return true if start succeeds; false if start fails.
   --
   --      virtual
   --      bool
   --      start() { return (true); };
   procedure Start
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean);

   --  The virtual terminate method can be implemented by
   --  inheriting classes to perform inheriting class termination logic
   --  (e.g., thread joining).
   --
   --      virtual
   --      bool
   --      terminate() { return (true); };
   procedure Stop
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean);

   --  The virtual processReceivedLmcpMessage is
   --  repeatedly invoked by the LmcpObjectNetworkClientBase class in an
   --  infinite loop until termination.
   --
   --  @param receivedLmcpObject received LMCP object.
   --  @return true if object is to terminate; false if object is to continue processing.
   --
   --      virtual
   --      bool
   --      processReceivedLmcpMessage
   --         (std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) { return (false); };
   procedure Process_Received_LMCP_Message
     (This             : in out LMCP_Object_Network_Client_Base;
      Received_Message : not null Any_LMCP_Message;
      Should_Terminate : out Boolean)
     is abstract;

   --  The virtual processReceivedSerializedLmcpMessage is
   --  repeatedly invoked by the LmcpObjectNetworkClientBase class in an
   --  infinite loop until termination. The payload of the AddressedAttributedMessage
   --  is a serialized LMCP object.
   --
   --  @param receivedSerializedLmcpObject received AddressedAttributedMessage object with serialized LMCP object payload.
   --  @return true if object is to terminate; false if object is to continue processing.
   --
   --      virtual
   --      bool
   --      processReceivedSerializedLmcpMessage
   --        (std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> receivedSerializedLmcpMessage) { return (false); };
   procedure Process_Received_Serialized_LMCP_Message
     (This             : in out LMCP_Object_Network_Client_Base;
      Received_Message : not null Any_Addressed_Attributed_Message;
      Should_Terminate : out Boolean)
     is abstract;

--  end protected:  -------------------------------------------------

   --  The configureNetworkClient method must be invoked
   --  before calling the initializeAndStart
   --  method.  It performs LmcpObjectNetworkClientBase-specific configuration
   --  and invokes the configure virtual method.
   --
   --  @param subclassTypeName type name of the inheriting class.
   --  @param receiveProcessingType enumeration determining whether or not received LMCP message will be de-serialized.
   --  @param networkXmlNode XML node containing object configurations.
   --  @return true if configuration succeeds; false if configuration fails.
   --
   --      bool
   --      configureNetworkClient
   --          (const std::string& subclassTypeName, ReceiveProcessingType receiveProcessingType, const pugi::xml_node& networkClientXmlNode);
   procedure Configure_Network_Client
     (This                    : in out LMCP_Object_Network_Client_Base;
      Subclass_Type_Name      : String;
      Processing_Kind         : Receive_Processing_Type;
      Network_Client_XML_Node : DOM.Core.Element;
      Result                  : out Boolean);

   --  The initializeAndStart routine must be invoked
   --  after calling the configureNetworkClient method.
   --  It performs the following steps:
   --     * LmcpObjectNetworkClientBase-specific initialization
   --     * inheriting class initialization (calls initialize virtual method)
   --     * inheriting class startup (calls start virtual method)
   --     * LmcpObjectNetworkClientBase-specific startup
   --
   --  @return true if all initialization and startup succeeds; false if initialization or startup fails.
   --
   --      bool
   --      initializeAndStart();
   procedure Initialize_And_Start (This : in out LMCP_Object_Network_Client_Base; Result : out Boolean);

   --      bool
   --      getIsTerminationFinished() { return(m_isBaseClassTerminationFinished && m_isSubclassTerminationFinished); }
   function Is_Termination_Finished (This : LMCP_Object_Network_Client_Base) return Boolean;

   --  The addSubscriptionAddress can be invoked
   --  at any time to add specified message subscription address.
   --
   --  @param address message subscription value
   --  @return true if address is added; false if address is not added.
   --
   --      bool
   --      addSubscriptionAddress(const std::string& address);
   procedure Add_Subscription_Address
     (This    : in out LMCP_Object_Network_Client_Base;
      Address : String;
      Success : out Boolean);

   --  The removeSubscriptionAddress can be invoked at any time to remove the
   --  specified message subscription address.
   --
   --  @param address message subscription address
   --  @return true if address is removed; false if address is not removed.
   --
   --      bool
   --      removeSubscriptionAddress(const std::string& address);
   procedure Remove_Subscription_Address
     (This    : in out LMCP_Object_Network_Client_Base;
      Address : String;
      Success : out Boolean);

   --  The removeAllSubscriptionAddresses can be invoked at any time to remove
   --  message subscription addresses.
   --
   --  @param address message subscription address
   --  @return true if address is removed; false if address is not removed.
   --
   --      bool
   --      removeAllSubscriptionAddresses();
   procedure Remove_All_Subscription_Addresses
     (This    : in out LMCP_Object_Network_Client_Base;
      Success : out Boolean);

   --  The sendLmcpObjectLimitedCastMessage method can be
   --  invoked to send a uni-cast or multi-cast LMCP object message to the LMCP network.
   --
   --  @param castAddress message publish address
   --  @param lmcpObject LMCP object to be uni-casted/multi-casted.
   --
   --      void
   --      sendLmcpObjectLimitedCastMessage(const std::string& castAddress, std::unique_ptr<avtas::lmcp::Object> lmcpObject);
   procedure Send_LMCP_Object_Limited_Cast_Message
     (This        : in out LMCP_Object_Network_Client_Base;
      CastAddress : String;
      Msg         : not null AVTAS.LMCP.Object.Object_Any);

   --  These were public member data in the C++ version so we provide accessors.
   --  TODO: consider using discriminants for some of them.

   --    Unique ID for UxAS entity instance; value read from configuration XML
   --      uint32_t m_entityId;
   function Entity_Id (This : LMCP_Object_Network_Client_Base) return UInt32;

   --    String representation of the unique ID for UxAS entity instance; value read from configuration XML
   --      std::string m_entityIdString;
   function Entity_Id_String (This : LMCP_Object_Network_Client_Base) return String;

   --    Unique ID of the LMCP object communication network actor (e.g., bridge or service).
   --      int64_t m_networkId;
   function Network_Id (This : LMCP_Object_Network_Client_Base) return Int64;

   --    String representation of the unique ID of the LMCP object communication network actor (e.g., bridge or service).
   --      std::string m_networkIdString;
   function Network_Id_String (This : LMCP_Object_Network_Client_Base) return String;

   --    Unicast message address for messaging case of sending message to only this network client instance
   --      std::string m_entityIdNetworkIdUnicastString;
   function Entity_Id_Network_Id_Unicast_String (This : LMCP_Object_Network_Client_Base) return String;

   --    Name of subclass used for logging/messaging.
   --      std::string m_networkClientTypeName;
   function Network_Client_Type_Name (This : LMCP_Object_Network_Client_Base) return String;

private

   --  The static member data in the C++ base class is duplicated in the Ada
   --  process via this implementation of the base class but is not coordinated.
   --  That is, both the Ada process and the C++ UxAS process have this base class
   --  present even though in our demo the C++ version doesn't have the validator
   --  subclass enabled. The base class has static member values that are
   --  incremented and used by the subclasses, such as the unique ID for
   --  automation requests, and the service id numbers. Hence they are duplicated.
   --
   --  We hack this by hardcoding starting values in the Ada version that are far
   --  above what the C++ code will reach, thus ensuring they remain unique across
   --  the two versions.

   --      static int64_t s_uniqueEntitySendMessageId;
   Unique_Entity_Send_Message_Id : Int64 := 10_000; --1;

   --  For the Next_Network_Client_Id we could include all the services in
   --  the demo xml, and thus know how many would be in the C++ side, and then
   --  use that info to determine the ID for the validator, but a really large
   --  number should be OK for a temporary solution.

   --   static ID of network clients, used to create unique IDs.
   --      static uint32_t s_nextNetworkClientId;
   Next_Network_Client_Id : Int64 := 1000; -- 10;

   --   static entity service cast address.
   --      static std::string s_entityServicesCastAllAddress;
   Entity_Services_Cast_All_Address : Dynamic_String (Capacity => Cast_All_Address_Max_Length);

   task type Network_Client_Processor
     (Client : not null access LMCP_Object_Network_Client_Base);

   type Client_Thread_Reference is access Network_Client_Processor;
   --  we use a pointer to the tasks, rather than simply having the task object
   --  be a component of the record type, for the sake of potential SPARKifying

   type LMCP_Object_Network_Client_Base is abstract tagged limited record
      --      bool m_isConfigured{false};
      Is_Configured : Boolean := False;

      --      bool m_isThreadStarted{false};
      Is_Thread_Started : Boolean := False;

      --      ReceiveProcessingType m_receiveProcessingType;
      Processing_Type : Receive_Processing_Type := LMCP;

      --    Unique ID for UxAS entity instance; value read from configuration XML
      --      uint32_t m_entityId;
      Entity_Id : UInt32;

      --    String representation of the unique ID for UxAS entity instance; value read from configuration XML
      --      std::string m_entityIdString;
      Entity_Id_String : Dynamic_String (Capacity => Entity_Id_Max_Length);

      --    Unique ID of the LMCP object communication network actor (e.g., bridge or service).
      --      int64_t m_networkId;
      Network_Id : Int64;

      --   String representation of the unique ID of the LMCP object communication network actor (e.g., bridge or service).
      --      std::string m_networkIdString;
      Network_Id_String : Dynamic_String (Capacity => Network_Id_Max_Length);

      --   Unicast message address for messaging case of sending message to only this network client instance
      --      std::string m_entityIdNetworkIdUnicastString;
      Entity_Id_Network_Id_Unicast_String : Dynamic_String (Capacity => Unicast_Message_Max_Length);

      --   Name of subclass used for logging/messaging.
      --      std::string m_networkClientTypeName;
      Network_Client_Type_Name : Dynamic_String (Capacity => Network_Client_Type_Name_Max_Length);

      --   Pointer to the component's thread.
      --      std::unique_ptr<std::thread> m_networkClientThread;
      Network_Client_Thread : Client_Thread_Reference;

      --      std::set<std::string> m_preStartLmcpSubscriptionAddresses;
      Pre_Start_LMCP_Subscription_Addresses : Subscription_Address_Set;

      --      uxas::communications::LmcpObjectMessageReceiverPipe m_lmcpObjectMessageReceiverPipe;
      Message_Receiver_Pipe : LMCP_Object_Message_Receiver_Pipe;

      --      uxas::communications::LmcpObjectMessageSenderPipe m_lmcpObjectMessageSenderPipe;
      Message_Sender_Pipe : LMCP_Object_Message_Sender_Pipe;

      --   Multi-cast group address that is subscribed to and included in sent messages
      --      std::string m_messageSourceGroup;
      Message_Source_Group : Dynamic_String (Capacity => Msg_Source_Group_Max_Length);

      --   Type of UxAS entity instance; value read from configuration XML
      --      std::string m_entityType;
      Entity_Type : Dynamic_String (Capacity => Entity_Type_Max_Length);

      --      std::atomic<bool> m_isBaseClassKillServiceProcessingPermitted{true};
      Is_Base_Class_Kill_Service_Processing_Permitted : Boolean := True with Atomic;
      --      std::atomic<bool> m_isTerminateNetworkClient{false};
      Is_Terminate_Network_Client : Boolean := False with Atomic;
      --      std::atomic<bool> m_isBaseClassTerminationFinished{false};
      Is_Base_Class_Termination_Finished : Boolean := False with Atomic;
      --      std::atomic<bool> m_isSubclassTerminationFinished{false};
      Is_Subclass_Termination_Finished : Boolean := False with Atomic;

      --      uint32_t m_subclassTerminationAbortDuration_ms{10000};
      Subclass_Termination_Abort_Duration : Duration := 10.0;
      --      uint32_t m_subclassTerminationWarnDuration_ms{3000};
      Subclass_Termination_Warn_Duration : Duration := 3.0;
      --      uint32_t m_subclassTerminationAttemptPeriod_ms{500};
      Subclass_Termination_Attempt_Period : Duration := 0.5;
   end record;

   --  The sendLmcpObjectBroadcastMessage method can be invoked to broadcast a
   --  LMCP object message on the LMCP network.
   --
   --  @param lmcpObject LMCP object to be broadcasted. The message publish
   --  address is derived from the full LMCP object name.
   --
   --      void
   --      sendLmcpObjectBroadcastMessage(std::unique_ptr<avtas::lmcp::Object> lmcpObject);
   procedure Send_LMCP_Object_Broadcast_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null AVTAS.LMCP.Object.Object_Any);

   --  The sendSerializedLmcpObjectMessage method can be invoked to
   --  send a AddressedAttributedMessage to the LMCP network. The
   --  AddressedAttributedMessage payload must be a serialized LMCP object string.
   --
   --  @param serializedLmcpObject LMCP object to be sent (uni-cast/multi-cast/broadcast).
   --
   --      void
   --      sendSerializedLmcpObjectMessage
   --          (std::unique_ptr<uxas::communications::data::AddressedAttributedMessage> serializedLmcpObject);
   procedure Send_Serialized_LMCP_Object_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null Addressed_Attributed_Message_Ref);

   --  The sendSharedLmcpObjectBroadcastMessage method can be invoked to broadcast
   --  a LMCP object message on the LMCP network.
   --
   --       @param lmcpObject LMCP object to be broadcasted. The message publish
   --       address is derived from the full LMCP object name.
   --
   --      void
   --      sendSharedLmcpObjectBroadcastMessage(const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);
   procedure Send_Shared_LMCP_Object_Broadcast_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null AVTAS.LMCP.Object.Object_Any);

   --  The sendSharedLmcpObjectLimitedCastMessage method can be invoked to send a
   --  uni-cast or multi-cast LMCP object message to the LMCP network.
   --
   --       @param castAddress message publish address
   --       @param lmcpObject LMCP object to be uni-casted/multi-casted.
   --
   --      void
   --      sendSharedLmcpObjectLimitedCastMessage(const std::string& castAddress, const std::shared_ptr<avtas::lmcp::Object>& lmcpObject);
   procedure Send_Shared_LMCP_Object_Limited_Cast_Message
     (This         : in out LMCP_Object_Network_Client_Base;
      Cast_Address : String;
      Msg          : not null AVTAS.LMCP.Object.Object_Any);

end UxAS.Comms.LMCP_Net_Client;
