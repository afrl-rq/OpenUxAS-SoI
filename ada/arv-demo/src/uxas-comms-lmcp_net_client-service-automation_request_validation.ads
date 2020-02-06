--  see OpenUxAS\src\Services\AutomationRequestValidatorService.h

with DOM.Core;
with AFRL.CMASI.LmcpTask;
with UxAS.Messages.LmcpTask.UniqueAutomationRequest;
with UxAS.Messages.LmcpTask.UniqueAutomationResponse;

with Ada.Containers.Formal_Hashed_Maps;
with Ada.Containers.Formal_Doubly_Linked_Lists;
with UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary; use UxAS.Messages.LmcpTask.UniqueAutomationRequest.SPARK_Boundary;
with AFRL.CMASI.OperatingRegion.SPARK_Boundary;                     use AFRL.CMASI.OperatingRegion.SPARK_Boundary;
with AFRL.CMASI.LmcpTask.SPARK_Boundary;
with Common_Formal_Containers;                                      use Common_Formal_Containers;

package UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation is

   type Automation_Request_Validator_Service is new Service_Base with private;

   type Automation_Request_Validator_Service_Ref is access all Automation_Request_Validator_Service;

   Type_Name : constant String := "AutomationRequestValidatorService";

   Directory_Name : constant String := "";

   --  static const std::vector<std::string>
   --  s_registryServiceTypeNames()
   function Registry_Service_Type_Names return Service_Type_Names_List;

   --  static ServiceBase*
   --  create()
   function Create return Any_Service;

private

   --  static
   --  ServiceBase::CreationRegistrar<AutomationRequestValidatorService> s_registrar;
   --  see the package body executable part

   use UxAS.Messages.LmcpTask.UniqueAutomationRequest;
   use UxAS.Messages.LmcpTask.UniqueAutomationResponse;

   type Automation_Request_Type is
     (Automation_Request,
      Sandbox_Automation_Request,
      Task_Automation_Request);

   type Request_Details is record
      requestType     : Automation_Request_Type;
      Play_Id         : Int64 := 0;
      Soln_Id         : Int64 := 0;
      Task_Request_Id : Int64 := 0;
   end record;

   package Int64_Operating_Region_Maps is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type     => Int64,
      Element_Type => OperatingRegionAreas,
      Hash         => Int64_Hash);

   Operating_Region_Maps_Max_Capacity : constant := 200; -- arbitrary

   subtype Operating_Region_Maps is Int64_Operating_Region_Maps.Map
     (Operating_Region_Maps_Max_Capacity,
      Int64_Operating_Region_Maps.Default_Modulus (Operating_Region_Maps_Max_Capacity));

   package Int64_Request_Details_Maps is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type     => Int64,
      Element_Type => Request_Details,
      Hash         => Int64_Hash);

   Request_Details_Max_Capacity : constant := 200; -- arbitrary

   subtype Request_Details_Map is Int64_Request_Details_Maps.Map
     (Request_Details_Max_Capacity,
      Int64_Request_Details_Maps.Default_Modulus (Request_Details_Max_Capacity));

   package Int64_CMASI_Task_Maps is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type     => Int64,
      Element_Type => afrl.cmasi.lmcptask.spark_boundary.Task_Kind_And_Id,  --- TODO: maybe not classwide???
      Hash         => Int64_Hash,
      "="          => afrl.cmasi.lmcptask.spark_boundary."=");

   Int64_CMASI_Task_Maps_Max_Capacity : constant := 200; -- arbitrary

   subtype CMASI_Task_Map is Int64_CMASI_Task_Maps.Map
     (Int64_CMASI_Task_Maps_Max_Capacity,
      Int64_CMASI_Task_Maps.Default_Modulus (Int64_CMASI_Task_Maps_Max_Capacity));

   type UniqueAutomationRequest_Holder is record
      Content : My_UniqueAutomationRequest;
   end record;
   --  Holder containing a unique automation request. Its predefined equality
   --  uses the primitive equality of My_UniqueAutomationRequest.

   package UniqueAutomationRequest_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists
     (Element_Type => UniqueAutomationRequest_Holder);

   Max_UniqueAutomationRequest_Deque_Depth : constant := 200; -- arbitrary
   --  the max number of references to UniqueAutomationRequest values in a deque containing that type

   subtype UniqueAutomationRequest_Ref_Deque is UniqueAutomationRequest_Lists.List (Capacity => Max_UniqueAutomationRequest_Deque_Depth);

   type Configuration_Data is record

      --  std::unordered_set<int64_t> m_availableConfigurationEntityIds;
      Available_Configuration_Entity_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availableStateEntityIds;
      Available_State_Entity_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availableKeepInZoneIds;
      Available_KeepIn_Zones_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availableKeepOutZoneIds;
      Available_KeepOut_Zones_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availableAreaOfInterestIds;
      Available_Area_of_Interest_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availableLineOfInterestIds;
      Available_Line_of_Interest_Ids : Int64_Set;

      --  std::unordered_set<int64_t> m_availablePointOfInterestIds;
      Available_Point_of_Interest_Ids : Int64_Set;

      --  std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::OperatingRegion> > m_availableOperatingRegions;
      Available_Operating_Regions : Operating_Region_Maps;

      -- std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::Task> > m_availableTasks;
      Available_Tasks : CMASI_Task_Map;

      --  std::unordered_set<int64_t> m_availableInitializedTasks;
      Available_Initialized_Tasks : Int64_Set;
   end record;

   type Automation_Request_Validator_Service is new Service_Base with record

      --  TODO: implement these timers, maybe using Timing_Events, but maybe using
      --  tasks because their purpose is to call send outgoing messages at the
      --  desired rate
      --
      --      this timer is used to track time for the system to respond to automation requests */
      --      uint64_t m_responseTimerId{0};
      --
      --      this timer is used to track time for the system to wait for task initialization */
      --      uint64_t m_taskInitTimerId{0};

      --      the maximum time to wait for a response (in ms)*/
      --      uint32_t m_maxResponseTime_ms = {5000}; // default: 5000 ms
      Max_Response_Time : UInt32 := 5000; -- milliseconds

      --  std::unordered_map<int64_t, RequestDetails> m_sandboxMap;
      Sandbox : Request_Details_Map;

      Configs : Configuration_Data;

      --  std::deque< std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_pendingRequests;
      Pending_Requests : UniqueAutomationRequest_Ref_Deque;

      --  std::deque< std::shared_ptr<uxas::messages::task::UniqueAutomationRequest> > m_requestsWaitingForTasks;
      Requests_Waiting_For_Tasks : UniqueAutomationRequest_Ref_Deque;

      --  std::shared_ptr<uxas::messages::task::UniqueAutomationResponse> m_errorResponse;
      Error_Response : UniqueAutomationResponse;
      --  Error_Response : UniqueAutomationResponse_Acc;
   end record;

   overriding
   procedure Configure
     (This     : in out Automation_Request_Validator_Service;
      XML_Node : DOM.Core.Element;
      Result   : out Boolean);

   overriding
   procedure Initialize
     (This   : in out Automation_Request_Validator_Service;
      Result : out Boolean);

   overriding
   procedure Process_Received_LMCP_Message
     (This             : in out Automation_Request_Validator_Service;
      Received_Message : not null Any_LMCP_Message;
      Should_Terminate : out Boolean);

   --  void HandleAutomationRequest(std::shared_ptr<avtas::lmcp::Object>& autoRequest);
   procedure Handle_Automation_Request
     (This    : in out Automation_Request_Validator_Service;
      Request : Object_Any);

   --  void HandleAutomationResponse(std::shared_ptr<avtas::lmcp::Object>& autoResponse);
   procedure Handle_Automation_Response
     (This     : in out Automation_Request_Validator_Service;
      Response : Object_Any);

   --  void SendResponse(std::shared_ptr<uxas::messages::task::UniqueAutomationResponse>& resp);
   procedure Send_Response
     (This : in out Automation_Request_Validator_Service;
      Resp : UniqueAutomationResponse_Acc);

--  TODO: TIMER CALLBACKS
--  this function gets called when the response timer expires
--  void OnResponseTimeout();
--  this function gets called when the tasks involved have not reported initialization in time
--  void OnTasksReadyTimeout();

   --  void sendNextRequest();
   procedure Send_Next_Request
     (This : in out Automation_Request_Validator_Service);

   procedure Construct (This : in out Automation_Request_Validator_Service);
   --  the ctor, called by the Create function

   function UInt32_Attribute
     (XML_Node : DOM.Core.Element;
      Name     : String;
      Default  : UInt32)
   return UInt32;
   --  convenience function

end UxAS.Comms.LMCP_Net_Client.Service.Automation_Request_Validation;
