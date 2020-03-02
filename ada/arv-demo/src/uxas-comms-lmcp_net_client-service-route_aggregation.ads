with DOM.Core;

with Route_Aggregator;                               use Route_Aggregator;
with Route_Aggregator_Communication;                 use Route_Aggregator_Communication;
with Ada.Containers.Ordered_Maps;
with AFRL.CMASI.EntityState;                         use AFRL.CMASI.EntityState;
with Route_Aggregator_Common;                        use Route_Aggregator_Common;
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
     (Key_Type     => Route_Aggregator_Common.Int64,
      Element_Type => TaskPlanOptions_Any);

   type Route_Aggregator_Service is new Service_Base with record
      Entity_Mapping             : Id_EntityState_Mapping.Map;
      Entity_Configurations      : Id_EntityConfiguration_Mapping.Map;
      M_AutoRequestId            : Route_Aggregator_Common.Int64 := 0;
      M_UniqueAutomationRequests : Id_UniqueAutomationRequest_Mapping.Map;
      M_TaskOptions              : Id_TaskPlanOptions_Mapping.Map;

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

end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;
