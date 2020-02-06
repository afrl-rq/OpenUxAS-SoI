with String_Utils;            use String_Utils;
with AVTAS.LMCP.ByteBuffers;  use AVTAS.LMCP.ByteBuffers;
with AVTAS.LMCP.Factory;
with UxAS.Common.Configuration_Manager;
with UXAS.Messages.UxNative.KillService;

with Ada.Strings.Fixed;

package body UxAS.Comms.LMCP_Net_Client is

   --  The initializeNetworkClient method is invoked by
   --  the initializeAndStart method to perform
   --  LmcpObjectNetworkClientBase-specific initialization
   --
   --  @return true if initialization succeeds; false if initialization fails.
   --
   --      bool
   --      initializeNetworkClient();
   procedure Initialize_Network_Client
     (This    : in out LMCP_Object_Network_Client_Base;
      Success : out Boolean);

   --  If m_receiveProcessingType == ReceiveProcessingType::LMCP, then
   --  the executeNetworkClient method repeatedly invokes
   --  the processReceivedLmcpMessage in an infinite loop until
   --  termination. Otherwise, the executeNetworkClient method is
   --  not invoked.
   --
   --      void
   --      executeNetworkClient();
   procedure Execute_Network_Client (This : in out LMCP_Object_Network_Client_Base);

   --  If m_receiveProcessingType == ReceiveProcessingType::SERIALIZED_LMCP, then
   --  the executeSerializedNetworkClient method repeatedly invokes
   --  the processReceivedSerializedLmcpMessage in an infinite loop until
   --  termination. Otherwise, the executeSerializedNetworkClient method is
   --  not invoked.
   --
   --      void
   --      executeSerializedNetworkClient();
   procedure Execute_Serialized_Network_Client (This : in out LMCP_Object_Network_Client_Base);

   --  The deserializeMessage method deserializes an LMCP
   --  string into an LMCP object.
   --
   --  @return unique pointer to LMCP object if succeeds; unique pointer with
   --  unassigned native pointer.
   --
   --      std::shared_ptr<avtas::lmcp::Object>
   --      deserializeMessage(const std::string& payload);
   function Deserialzed_Message (Payload : String) return AVTAS.LMCP.Object.Object_Any;

   function Should_Kill_This_Service
     (This : LMCP_Object_Network_Client_Base;
      Msg  : Any_Lmcp_Message)
   return Boolean;

   function Should_Kill_This_Service
     (This : LMCP_Object_Network_Client_Base;
      Msg  : AVTAS.LMCP.Object.Object_Any)
   return Boolean;
   --  a refactored convenience routine

   function Has_KillService_Subscription (Msg : Addressed_Attributed_Message_Ref) return Boolean;
   --  a refactored convenience routine

   ----------------------
   -- Construct_Client --
   ----------------------

   procedure Construct_Client (This : in out LMCP_Object_Network_Client_Base)
   is
   begin
      --  from the default ctor
      This.Network_Id := Next_Network_Client_Id;
      Next_Network_Client_Id := Next_Network_Client_Id + 1;
      Copy (To_String (This.Network_Id), To => This.Network_Id_String);

      --  from static elaboration (see top of OpenUxAS\src\Communications\LmcpObjectNetworkClientBase.cpp)
      Copy (Get_Entity_Services_Cast_All_Address (UxAS.Common.Configuration_Manager.Instance.Get_Entity_Id),
            To => Entity_Services_Cast_All_Address);
   end Construct_Client;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean)
   is
      pragma Unreferenced (This);  -- by design
   begin
      Result := True;
   end Initialize;

   -------------------------------
   -- Initialize_Network_Client --
   -------------------------------

   procedure Initialize_Network_Client
     (This    : in out LMCP_Object_Network_Client_Base;
      Success : out Boolean)
   is
      Unused : Boolean;
   begin
      This.Message_Receiver_Pipe.Initialize_Subscription
        (Entity_Id  => This.Entity_Id,
         Service_Id => UInt32 (This.Network_Id));

      for Address of This.Pre_Start_LMCP_Subscription_Addresses loop
         This.Message_Receiver_Pipe.Add_Lmcp_Object_Subscription_Address (Value (Address), Unused);
      end loop;

      This.Message_Sender_Pipe.Initialize_Push
        (Source_Group => Value (This.Message_Source_Group),
         Entity_Id    => This.Entity_Id,
         Service_Id   => UInt32 (This.Network_Id));

      Success := True;  -- per the C++ code
   end Initialize_Network_Client;

   -------------------------
   -- Deserialzed_Message --
   -------------------------

   function Deserialzed_Message (Payload : String) return AVTAS.LMCP.Object.Object_Any is
      Result : AVTAS.LMCP.Object.Object_Any;
      Buffer : ByteBuffer (Capacity => Payload'Length);
   begin
      --  // allocate memory
      --  avtas::lmcp::ByteBuffer lmcpByteBuffer;
      --  lmcpByteBuffer.allocate(payload.size());
      --  lmcpByteBuffer.rewind();

      --  for (size_t charIndex = 0; charIndex < payload.size(); charIndex++)
      --  {
      --      lmcpByteBuffer.putByte(payload[charIndex]); // TODO REVIEW
      --  }
      --  PDR: note we don't just call Put_String because that would first put
      --  the length, which the C++ code doesn't do
      for C of Payload loop
         Buffer.Put_Byte (Character'Pos (C));
      end loop;
      --  lmcpByteBuffer.rewind();
      Buffer.Rewind;

      --  lmcpObject.reset(avtas::lmcp::Factory::getObject(lmcpByteBuffer));
      AVTAS.LMCP.Factory.GetObject (Buffer, Result);

      return Result;
   end Deserialzed_Message;

   ----------------------
   -- Entity_Id_Prefix --
   ----------------------

   function Entity_Id_Prefix return String is
     ("eid");

   -----------------------
   -- Service_Id_Prefix --
   -----------------------

   function Service_Id_Prefix return String is
      (".sid");

   ---------------------------
   -- Service_Id_All_Suffix --
   ---------------------------

   function Service_Id_All_Suffix return String is
      (".sidall");

   -------------------------
   -- Entity_Cast_Address --
   -------------------------

   function Entity_Cast_Address (Entity_Id : UInt32) return String is
      (Entity_Id_Prefix & To_String (Entity_Id));

   -------------------------
   -- Entity_Cast_Address --
   -------------------------

   function Entity_Cast_Address (Entity_Id : String) return String is
      (Entity_Id_Prefix & Entity_Id);

   --------------------------------------
   -- Entity_Services_Cast_All_Address --
   --------------------------------------

   function Get_Entity_Services_Cast_All_Address (Entity_Id : UInt32) return String is
     (Entity_Cast_Address (Entity_Id) & Service_Id_All_Suffix);

   ------------------------------------
   -- Network_Client_Unicast_Address --
   ------------------------------------

   function Network_Client_Unicast_Address
     (Entity_Id         : UInt32;
      Network_Client_Id : Int64)
   return String
   is
     (Entity_Cast_Address (Entity_Id) & Service_Id_Prefix & To_String (Network_Client_Id));

   ----------------------------------------
   -- Get_Network_Client_Unicast_Address --
   ----------------------------------------

   function Get_Network_Client_Unicast_Address
     (Entity_Id         : UInt32;
      Network_Client_Id : String)
      return String
   is
     (Entity_Cast_Address (Entity_Id) & Service_Id_Prefix & Network_Client_Id);

   ----------------------------------------
   -- Get_Network_Client_Unicast_Address --
   ----------------------------------------

   function Get_Network_Client_Unicast_Address
     (Entity_Id         : String;
      Network_Client_Id : String)
      return String
   is
     (Entity_Cast_Address (Entity_Id) & Service_Id_Prefix & Network_Client_Id);

   ----------------------------------------
   -- Get_Network_Client_Unicast_Address --
   ----------------------------------------

   function Get_Network_Client_Unicast_Address
     (Entity_Id         : String;
      Network_Client_Id : Int64)
     return String
   is
     (Entity_Cast_Address (Entity_Id) & Service_Id_Prefix & To_String (Network_Client_Id));

   ---------------------------------------
   -- Get_Unique_Entity_Send_Message_Id --
   ---------------------------------------

   procedure Get_Unique_Entity_Send_Message_Id (Value : out Int64)is
   begin
      --  return (s_uniqueEntitySendMessageId++);
      Value := Unique_Entity_Send_Message_Id;
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
   end Get_Unique_Entity_Send_Message_Id;

   ----------------------------------
   -- Get_Unique_Network_Client_Id --
   ----------------------------------

   procedure Get_Unique_Network_Client_Id (Value : out Int64) is
   begin
      Next_Network_Client_Id := Next_Network_Client_Id + 1;
      Value := Next_Network_Client_Id;
   end Get_Unique_Network_Client_Id;

   -----------------------------
   -- Is_Termination_Finished --
   -----------------------------

   function Is_Termination_Finished (This : LMCP_Object_Network_Client_Base) return Boolean is
      (This.Is_Base_Class_Termination_Finished and This.Is_Subclass_Termination_Finished);

   ------------------------------
   -- Configure_Network_Client --
   ------------------------------

   procedure Configure_Network_Client
     (This                    : in out LMCP_Object_Network_Client_Base;
      Subclass_Type_Name      : String;
      Processing_Kind         : Receive_Processing_Type;
      Network_Client_XML_Node : DOM.Core.Element;
      Result                  : out Boolean)
   is
      Unused : Boolean;
   begin
      --  m_entityId = uxas::common::ConfigurationManager::getInstance().getEntityId();
      This.Entity_Id := UXAS.Common.Configuration_Manager.Instance.Get_Entity_Id;

      --  m_entityIdString = std::to_string(m_entityId);
      Copy (To_String (This.Entity_Id), To => This.Entity_Id_String);

      --  m_entityType = uxas::common::ConfigurationManager::getInstance().getEntityType();
      Copy (UXAS.Common.Configuration_Manager.Instance.Get_Entity_Type, To => This.Entity_Type);

      --  m_networkClientTypeName = subclassTypeName;
      Copy (Subclass_Type_Name, To => This.Network_Client_Type_Name);

      --  m_receiveProcessingType = receiveProcessingType;
      This.Processing_Type := Processing_Kind;

      --  // subscribe to messages addressed to network client (bridge, service, etc.)
      --  m_entityIdNetworkIdUnicastString = getNetworkClientUnicastAddress(m_entityId, m_networkId);
      Copy (Get_Network_Client_Unicast_Address (This.Entity_Id, To_String (This.Network_Id)),
            To => This.Entity_Id_Network_Id_Unicast_String);

      --  addSubscriptionAddress(m_entityIdNetworkIdUnicastString);
      This.Add_Subscription_Address (Entity_Id_Network_Id_Unicast_String (This), Unused);

      --  s_entityServicesCastAllAddress = getEntityServicesCastAllAddress(m_entityId);
      Copy (Get_Entity_Services_Cast_All_Address (This.Entity_Id),
            To => Entity_Services_Cast_All_Address);

      --  addSubscriptionAddress(s_entityServicesCastAllAddress);
      This.Add_Subscription_Address (Value (Entity_Services_Cast_All_Address), Unused);

      --  // network client can be terminated via received KillService message
      --  addSubscriptionAddress(uxas::messages::uxnative::KillService::Subscription);
      This.Add_Subscription_Address (UXAS.Messages.UxNative.KillService.Subscription, Unused);

      --  m_isConfigured = configure(networkClientXmlNode);
      Configure (LMCP_Object_Network_Client_Base'Class (This),
                 XML_Node => Network_Client_XML_Node,
                 Result   => Result);
   end Configure_Network_Client;

   --------------------------
   -- Initialize_And_Start --
   --------------------------

   procedure Initialize_And_Start (This : in out LMCP_Object_Network_Client_Base; Result : out Boolean) is
   begin
      if not This.Is_Configured then
         Result := False;
         return;
      end if;

      Initialize_Network_Client (This,  Result);
      if not Result then
         return;
      end if;

      Initialize (LMCP_Object_Network_Client_Base'Class (This), Result);  -- dispatch to subclass, which will call this baseclass' version
      if not Result then
         return;
      end if;

      Start (LMCP_Object_Network_Client_Base'Class (This),  Result);  -- dispatch to subclass
      if not Result then
         return;
      end if;

      This.Network_Client_Thread := new Network_Client_Processor (This'Unchecked_Access);
   end Initialize_And_Start;

   ------------------------------
   -- Network_Client_Processor --
   ------------------------------

   task body Network_Client_Processor is
   begin
      --  we'll need to wait for a signal to start unless dynamically allocated

      case Client.Processing_Type is
         when LMCP =>
            Execute_Network_Client (Client.all);  --  loops
         when Serialized_LMCP =>
            Execute_Serialized_Network_Client (Client.all);  --  loops
      end case;
   end Network_Client_Processor;

   ----------------------------
   -- Execute_Network_Client --
   ----------------------------

   procedure Execute_Network_Client (This : in out LMCP_Object_Network_Client_Base) is
      ReceivedLmcpMessage : Any_Lmcp_Message;
   begin
      This.Is_Thread_Started := True;

      while not This.Is_Terminate_Network_Client loop
         This.Message_Receiver_Pipe.Get_Next_Message_Object (ReceivedLmcpMessage);
         if ReceivedLmcpMessage /= null then
            if Should_Kill_This_Service (This, ReceivedLmcpMessage) then
               This.Is_Terminate_Network_Client := True;
            else
               Process_Received_LMCP_Message
                 (LMCP_Object_Network_Client_Base'Class (This),  -- dispatch to subclass version
                  Received_Message => ReceivedLmcpMessage,
                  Should_Terminate => This.Is_Terminate_Network_Client);
            end if;
         end if;
      end loop;

      This.Is_Base_Class_Termination_Finished := True;

      loop
         Stop (LMCP_Object_Network_Client_Base'Class (This), This.Is_Subclass_Termination_Finished);   -- dispatch to subclass version
         exit when This.Is_Subclass_Termination_Finished;
         -- std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
         delay This.Subclass_Termination_Attempt_Period;
         --  subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
         --  if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
         --  {
         --      UXAS_LOG_WARN(m_networkClientTypeName, "::executeNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
         --  }
         --  else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
         --  {
         --      UXAS_LOG_ERROR(m_networkClientTypeName, "::executeNetworkClient aborting termination of subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
         --      break;
         --  }
      end loop;
   end Execute_Network_Client;

   ---------------------------------------
   -- Execute_Serialized_Network_Client --
   ---------------------------------------

   procedure Execute_Serialized_Network_Client (This : in out LMCP_Object_Network_Client_Base) is
      Next_Received_Serialized_Lmcp_Object : Addressed_Attributed_Message_Ref;
   begin
      --  m_isThreadStarted = true;
      This.Is_Thread_Started := True;
      --  while (!m_isTerminateNetworkClient)
      while not This.Is_Terminate_Network_Client loop
         --  get the next serialized LMCP object message (if any) from the LMCP network server
         --  std::unique_ptr<uxas::communications::data::AddressedAttributedMessage>   nextReceivedSerializedLmcpObject = m_lmcpObjectMessageReceiverPipe.getNextSerializedMessage();
         This.Message_Receiver_Pipe.Get_Next_Serialized_Message (Next_Received_Serialized_Lmcp_Object);

         --  if (nextReceivedSerializedLmcpObject)
         if Next_Received_Serialized_Lmcp_Object /= null then
            --  if (m_isBaseClassKillServiceProcessingPermitted
            if This.Is_Base_Class_Kill_Service_Processing_Permitted and then
               Has_KillService_Subscription (Next_Received_Serialized_Lmcp_Object)
            then --  reconstitute LMCP object
               declare
                  --  std::shared_ptr<avtas::lmcp::Object> lmcpObject = deserializeMessage(nextReceivedSerializedLmcpObject->getPayload());
                  Lmcp_Object : AVTAS.LMCP.Object.Object_Any;
               begin
                  Lmcp_Object := Deserialzed_Message (Next_Received_Serialized_Lmcp_Object.Payload);
                  --  check KillService serviceID == my serviceID
                  --  if (uxas::messages::uxnative::isKillService(lmcpObject)
                  --          //&& m_entityIdString.compare(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getEntityID()) == 0//TODO check entityID
                  --          && m_networkIdString.compare(std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getServiceID())) == 0)
                  if Should_Kill_This_Service (This, Lmcp_Object) then
                     --      m_isTerminateNetworkClient = true;
                     This.Is_Terminate_Network_Client := True;
                     --  else if (processReceivedSerializedLmcpMessage(std::move(nextReceivedSerializedLmcpObject)))
                     --  {
                     --      m_isTerminateNetworkClient = true;
                     --  }
                  else
                     Process_Received_Serialized_LMCP_Message
                       (LMCP_Object_Network_Client_Base'Class (This),  -- dispatch to subclass version
                        Received_Message => Any_Addressed_Attributed_Message (Next_Received_Serialized_Lmcp_Object),
                        Should_Terminate           => This.Is_Terminate_Network_Client);
                  end if;
               end;
            end if;
         end if;
      end loop;

      --  m_isBaseClassTerminationFinished = true;
      This.Is_Base_Class_Termination_Finished := True;

      loop
         --  m_isSubclassTerminationFinished = terminate();
         Stop (LMCP_Object_Network_Client_Base'Class (This), This.Is_Subclass_Termination_Finished);   -- dispatch to subclass version
         exit when This.Is_Subclass_Termination_Finished;

         --  std::this_thread::sleep_for(std::chrono::milliseconds(m_subclassTerminationAttemptPeriod_ms));
         delay This.Subclass_Termination_Attempt_Period;
         --  subclassTerminateDuration_ms += m_subclassTerminationAttemptPeriod_ms;
         --  if (subclassTerminateDuration_ms > m_subclassTerminationWarnDuration_ms)
         --  {
         --      UXAS_LOG_WARN(m_networkClientTypeName, "::executeSerializedNetworkClient has not terminated subclass processing after [", subclassTerminateDuration_ms, "] milliseconds on thread [", std::this_thread::get_id(), "]");
         --  }
         --  else if (subclassTerminateDuration_ms > m_subclassTerminationAbortDuration_ms)
         --  {
         --      m_isSubclassTerminationFinished = true;
         --      break;
         --  }
      end loop;
   end Execute_Serialized_Network_Client;

   -----------------------------------
   -- Process_Received_LMCP_Message --
   -----------------------------------

   procedure Process_Received_LMCP_Message
     (This             : in out LMCP_Object_Network_Client_Base;
      Received_Message : not null Any_LMCP_Message;
      Should_Terminate : out Boolean)
   is
      pragma Unreferenced (This, Received_Message);
   begin
      Should_Terminate := False; -- per the C++ version
   end Process_Received_LMCP_Message;

   ----------------------------------------------
   -- Process_Received_Serialized_LMCP_Message --
   ----------------------------------------------

   procedure Process_Received_Serialized_LMCP_Message
     (This             : in out LMCP_Object_Network_Client_Base;
      Received_Message : not null Any_Addressed_Attributed_Message;
      Should_Terminate : out Boolean)
   is
      pragma Unreferenced (This, Received_Message);
   begin
      Should_Terminate := False; -- per the C++ version
   end Process_Received_Serialized_LMCP_Message;

   ------------------------------
   -- Add_Subscription_Address --
   ------------------------------

   procedure Add_Subscription_Address
     (This    : in out LMCP_Object_Network_Client_Base;
      Address : String;
      Success : out Boolean)
   is
      Target : constant Subscription_Address := Instance (Subscription_Address_Max_Length, Content => Address);
      Unused : Boolean;
   begin
      if This.Is_Thread_Started then
         This.Message_Receiver_Pipe.Add_Lmcp_Object_Subscription_Address (Address, Unused);
      else
         --  replace if already present
         Subscription_Addresses.Include (This.Pre_Start_LMCP_Subscription_Addresses, Target);
      end if;

      Success := True;  -- per the C++ implementation
   end Add_Subscription_Address;

   ---------------------------------
   -- Remove_Subscription_Address --
   ---------------------------------

   procedure Remove_Subscription_Address
     (This    : in out LMCP_Object_Network_Client_Base;
      Address : String;
      Success : out Boolean)
   is
      Target : constant Subscription_Address := Instance (Subscription_Address_Max_Length, Content => Address);
      Unused : Boolean;
   begin
      if This.Is_Thread_Started then
         This.Message_Receiver_Pipe.Remove_Lmcp_Object_Subscription_Address (Address, Unused);
      else
         --  remove if present
         Subscription_Addresses.Exclude (This.Pre_Start_LMCP_Subscription_Addresses, Target);
      end if;

      Success := False;  -- per the C++ implementation!!!!
   end Remove_Subscription_Address;

   ---------------------------------------
   -- Remove_All_Subscription_Addresses --
   ---------------------------------------

   procedure Remove_All_Subscription_Addresses
     (This    : in out LMCP_Object_Network_Client_Base;
      Success : out Boolean)
   is
      Unused : Boolean;
   begin
      if This.Is_Thread_Started then
         This.Message_Receiver_Pipe.Remove_All_Lmcp_Object_Subscription_Address (Unused);
      else
         Subscription_Addresses.Clear (This.Pre_Start_LMCP_Subscription_Addresses);
      end if;

      Success := False;  -- per the C++ implementation!!!!
   end Remove_All_Subscription_Addresses;

   -------------------------------------------
   -- Send_LMCP_Object_Limited_Cast_Message --
   -------------------------------------------

   procedure Send_LMCP_Object_Limited_Cast_Message
     (This        : in out LMCP_Object_Network_Client_Base;
      CastAddress : String;
      Msg         : not null AVTAS.LMCP.Object.Object_Any)
   is
   begin
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
      This.Message_Sender_Pipe.Send_LimitedCast_Message (CastAddress, Msg);
   end Send_LMCP_Object_Limited_Cast_Message;

   ----------------------------------------
   -- Send_LMCP_Object_Broadcast_Message --
   ----------------------------------------

   procedure Send_LMCP_Object_Broadcast_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null AVTAS.LMCP.Object.Object_Any)
   is
   begin
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
      This.Message_Sender_Pipe.Send_Broadcast_Message (Msg);
   end Send_LMCP_Object_Broadcast_Message;

   -----------------------------------------
   -- Send_Serialized_LMCP_Object_Message --
   -----------------------------------------

   procedure Send_Serialized_LMCP_Object_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null Addressed_Attributed_Message_Ref)
   is
   begin
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
      This.Message_Sender_Pipe.Send_Serialized_Message (Msg);
   end Send_Serialized_LMCP_Object_Message;

   -----------------------------------------------
   -- Send_Shared_LMCP_Object_Broadcast_Message --
   -----------------------------------------------

   procedure Send_Shared_LMCP_Object_Broadcast_Message
     (This : in out LMCP_Object_Network_Client_Base;
      Msg  : not null AVTAS.LMCP.Object.Object_Any)
   is
   begin
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
      This.Message_Sender_Pipe.Send_Shared_Broadcast_Message (Msg);
   end Send_Shared_LMCP_Object_Broadcast_Message;

   --------------------------------------------------
   -- Send_Shared_LMCP_Object_Limited_Cast_Message --
   --------------------------------------------------

   procedure Send_Shared_LMCP_Object_Limited_Cast_Message
     (This         : in out LMCP_Object_Network_Client_Base;
      Cast_Address : String;
      Msg          : not null AVTAS.LMCP.Object.Object_Any)
   is
   begin
      Unique_Entity_Send_Message_Id := Unique_Entity_Send_Message_Id + 1;
      This.Message_Sender_Pipe.Send_Shared_LimitedCast_Message (Cast_Address, Msg);
   end Send_Shared_LMCP_Object_Limited_Cast_Message;

   ---------------
   -- Entity_Id --
   ---------------

   function Entity_Id (This : LMCP_Object_Network_Client_Base) return UInt32 is
      (This.Entity_Id);

   ----------------------
   -- Entity_Id_String --
   ----------------------

   function Entity_Id_String (This : LMCP_Object_Network_Client_Base) return String is
      (Value (This.Entity_Id_String));

   ----------------
   -- Network_Id --
   ----------------

   function Network_Id (This : LMCP_Object_Network_Client_Base) return Int64 is
      (This.Network_Id);

   -----------------------
   -- Network_Id_String --
   -----------------------

   function Network_Id_String (This : LMCP_Object_Network_Client_Base) return String is
      (Value (This.Network_Id_String));

   -----------------------------------------
   -- Entity_Id_Network_Id_Unicast_String --
   -----------------------------------------

   function Entity_Id_Network_Id_Unicast_String (This : LMCP_Object_Network_Client_Base) return String is
      (Value (This.Entity_Id_Network_Id_Unicast_String));

   ------------------------------
   -- Network_Client_Type_Name --
   ------------------------------

   function Network_Client_Type_Name (This : LMCP_Object_Network_Client_Base) return String is
      (Value (This.Network_Client_Type_Name));

   -----------
   -- Start --
   -----------

   procedure Start
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean)
   is
      pragma Unreferenced (This); -- by design
   begin
      Result := True;
   end Start;

   ----------
   -- Stop --
   ----------

   procedure Stop
     (This   : in out LMCP_Object_Network_Client_Base;
      Result : out Boolean)
   is
      pragma Unreferenced (This); -- by design
   begin
      Result := True;
   end Stop;

   ------------------------------
   -- Should_Kill_This_Service --
   ------------------------------

   function Should_Kill_This_Service
     (This : LMCP_Object_Network_Client_Base;
      Msg  : Any_Lmcp_Message)
    return Boolean
   is
      use UXAS.Messages.UxNative.KillService;

      --  the lmcpgen C++ generated code in class KillService has these static functions:
      --
      --  // Subscription string is namespace separated by '.' followed by type name
      --  const std::string KillService::Subscription = "uxas.messages.uxnative.KillService";
      --  const std::string KillService::TypeName = "KillService";
      --  const std::string KillService::SeriesName = "UXNATIVE";
      --  const int64_t KillService::SeriesId = 6149751333668345413LL;
      --  const uint16_t KillService::SeriesVersion = 9;
      --  const uint32_t KillService::TypeId = 4;
      --
      --  bool isKillService(avtas::lmcp::Object* obj)
      --  {
      --     if(!obj) return false;
      --     if(obj->getSeriesNameAsLong() != 6149751333668345413LL) return false;
      --     if(obj->getSeriesVersion() != 9) return false;
      --     if(obj->getLmcpType() != 4) return false;
      --     return true;
      --  }

   begin
      if not This.Is_Base_Class_Kill_Service_Processing_Permitted then
         return False;
      end if;

      --  && uxas::messages::uxnative::isKillService(receivedLmcpMessage->m_object)
      if Msg.Payload.all not in KillService'Class then
         return False;
      end if;

      --  check KillService serviceID == my serviceID
      --  && m_networkIdString.compare
      --    (std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(receivedLmcpMessage->m_object)->getServiceID()))
      --    == 0)
      return This.Network_Id_String = To_String (KillService (Msg.Payload.all).GetServiceID);
   end Should_Kill_This_Service;

   ------------------------------
   -- Should_Kill_This_Service --
   ------------------------------

   function Should_Kill_This_Service
     (This : LMCP_Object_Network_Client_Base;
      Msg  : AVTAS.LMCP.Object.Object_Any)
   return Boolean
   is
      use UXAS.Messages.UxNative.KillService;
   begin
      if not This.Is_Base_Class_Kill_Service_Processing_Permitted then
         return False;
      end if;

      --  if (uxas::messages::uxnative::isKillService(lmcpObject)
      if Msg.all not in KillService'Class then
         return False;
      end if;

      --  check KillService serviceID == my serviceID
      --  //&& m_entityIdString.compare(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getEntityID()) == 0//TODO check entityID
      --  && m_networkIdString.compare(std::to_string(std::static_pointer_cast<uxas::messages::uxnative::KillService>(lmcpObject)->getServiceID())) == 0)
      return This.Network_Id_String = To_String (KillService (Msg.all).GetServiceID);
   end Should_Kill_This_Service;

   ----------------------------------
   -- Has_KillService_Subscription --
   ----------------------------------

   function Has_KillService_Subscription (Msg : Addressed_Attributed_Message_Ref) return Boolean is
      Descriptor : constant String := Msg.Message_Attributes_Reference.Payload_Descriptor;
      Target     : constant String := UXAS.Messages.UxNative.KillService.Subscription;
      Pos        : Natural;
      use Ada.Strings;
   begin
      --  && nextReceivedSerializedLmcpObject->getMessageAttributesReference()->getDescriptor()
      --          .rfind(uxas::messages::uxnative::KillService::Subscription) != std::string::npos)
      Pos := Ada.Strings.Fixed.Index (Source => Descriptor, Pattern => Target, Going => Backward) ;
      return Pos /= 0;
   end Has_KillService_Subscription;

end UxAS.Comms.LMCP_Net_Client;
