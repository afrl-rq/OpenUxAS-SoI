with DOM.Core;

with Route_Aggregator;                               use Route_Aggregator;
with Route_Aggregator_Communication;                 use Route_Aggregator_Communication;
with Route_Aggregator_Common;                        use Route_Aggregator_Common;

with Ada.Containers.Ordered_Maps;
with Ada.Containers.Ordered_Sets;

with AVTAS.LMCP.Types;
with AFRL.CMASI.EntityState;                         use AFRL.CMASI.EntityState;
with Afrl.Cmasi.EntityConfiguration;                 use Afrl.Cmasi.EntityConfiguration;
with Uxas.Messages.Lmcptask.UniqueAutomationRequest; use Uxas.Messages.Lmcptask.UniqueAutomationRequest;
with UxAS.Messages.Lmcptask.TaskPlanOptions;         use UxAS.Messages.Lmcptask.TaskPlanOptions;

package UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation is

   type Route_Aggregator_Service is new Service_Base with private;

   Type_Name : constant String := "RouteAggregatorService";

   Directory_Name : constant String := "";

   --  static const std::vector<std::string>
   --  s_registryServiceTypeNames()
   function Registry_Service_Type_Names return Service_Type_Names_List;

   --  static ServiceBase*
   --  create()
   function Create return Any_Service;

private

   --  We need a mapping of Int64 vehicle Ids to EntityState baseclass
   --  pointers, but the Route_Aggregator package is in SPARK so cannnot use
   --  pointers. Therefore, in the SPARK code, Config.m_EntityStates is not a
   --  map, but rather just a vector of Int64 values. The SPARK code doesn't
   --  really use m_EntityStates because its primary usage is in functionality
   --  not implemented in SPARK. But it is implemented in Ada, therefore we
   --  need this mapping to EntityState baseclass pointers. So we will add
   --  another component.

   package Id_EntityState_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => Route_Aggregator_Common.Int64,
      Element_Type => EntityState_Any);

   package Id_EntityConfiguration_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => Route_Aggregator_Common.Int64,
      Element_Type => EntityConfiguration_Any);

   package Id_UniqueAutomationRequest_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => Route_Aggregator_Common.Int64,
      Element_Type => UniqueAutomationRequest_Any);

   package Id_TaskPlanOptions_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => AVTAS.LMCP.Types.Int64,
      Element_Type => TaskPlanOptions_Any);

   package Int64_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => AVTAS.LMCP.Types.Int64,
      "<"          => AVTAS.LMCP.Types."<",
      "="          => AVTAS.LMCP.Types."=");

   package Pending_Auto_Requests_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => AVTAS.LMCP.Types.Int64,
      Element_Type => Int64_Sets.Set,
      "<"          => AVTAS.LMCP.Types."<",
      "="          => Int64_Sets."=");

   type AggregatorTaskOptionPair is record
      --  int64_t vehicleId{0};
      vehicleId : AVTAS.LMCP.Types.Int64 := 0;
      --  int64_t taskId{0};
      taskId : AVTAS.LMCP.Types.Int64 := 0;
      --  int64_t taskOption{0};
      taskOption : AVTAS.LMCP.Types.Int64 := 0;
      --  int64_t prevTaskId{0};
      prevTaskId : AVTAS.LMCP.Types.Int64 := 0;
      --  int64_t prevTaskOption{0};
      prevTaskOption : AVTAS.LMCP.Types.Int64 := 0;
   end record;

   type AggregatorTaskOptionPair_Reference is access all AggregatorTaskOptionPair;

   package RouteId_AggregatorPair_Mapping is new Ada.Containers.Ordered_Maps
     (Key_Type     => AVTAS.LMCP.Types.Int64,
      Element_Type => AggregatorTaskOptionPair_Reference);


   type Route_Aggregator_Service is new Service_Base with record
      Entity_Mapping             : Id_EntityState_Mapping.Map;
      Entity_Configurations      : Id_EntityConfiguration_Mapping.Map;
      M_AutoRequestId            : Route_Aggregator_Common.Int64 := 0;
      M_UniqueAutomationRequests : Id_UniqueAutomationRequest_Mapping.Map;
      M_TaskOptions              : Id_TaskPlanOptions_Mapping.Map;

      --  std::unordered_map<int64_t, std::unordered_set<int64_t> > m_pendingAutoReq;
      M_PendingAutoReq           : Pending_Auto_Requests_Mapping.Map;

      --  Mapping from route ID to the corresponding task/option pair:
      --                 route id,      task+option pair
      --  std::unordered_map<int64_t, std::shared_ptr<AggregatorTaskOptionPair> > m_routeTaskPairing;
      M_RouteTaskPairing : RouteId_AggregatorPair_Mapping.Map;

      --  Starting ID for uniquely identifying route plan
      --  int64_t m_routeId{1000000}; // start outside of any task or waypoint id
      m_routeId : AVTAS.LMCP.Types.Int64 := 1_000_000;

      --  the following types are defined in SPARK code
      Mailbox : Route_Aggregator_Mailbox;
      State   : Route_Aggregator_State;
      Config  : Route_Aggregator_Configuration_Data;
   end record;

   overriding
   procedure Configure
     (This     : in out Route_Aggregator_Service;
      XML_Node : DOM.Core.Element;
      Result   : out Boolean);

   overriding
   procedure Initialize
     (This   : in out Route_Aggregator_Service;
      Result : out Boolean);

   overriding
   procedure Process_Received_LMCP_Message
     (This             : in out Route_Aggregator_Service;
      Received_Message : not null Any_LMCP_Message;
      Should_Terminate : out Boolean);

   procedure Check_All_Task_Options_Received
     (This : in out Route_Aggregator_Service);

   procedure BuildMatrixRequests
     (This  : in out Route_Aggregator_Service;
      ReqId : AVTAS.LMCP.Types.Int64;
      AReq  : UniqueAutomationRequest_Any);

end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;
