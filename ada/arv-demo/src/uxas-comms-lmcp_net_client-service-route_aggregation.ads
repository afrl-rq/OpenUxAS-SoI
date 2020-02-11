with DOM.Core;

with Route_Aggregator; use Route_Aggregator; -- from Claire

package UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation is

   type Route_Aggregator_Service is new Service_Base with private;

--     type Route_Aggregator_Service_Ref is access all Route_Aggregator_Service;

   Type_Name : constant String := "RouteAggregatorService";

   Directory_Name : constant String := "";

   --  static const std::vector<std::string>
   --  s_registryServiceTypeNames()
   function Registry_Service_Type_Names return Service_Type_Names_List;

   --  static ServiceBase*
   --  create()
   function Create return Any_Service;

private

   type Route_Aggregator_Service is new Service_Base with record
      State  : Route_Aggregator_State;
      Config : Route_Aggregator_Configuration_Data;
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

end UxAS.Comms.LMCP_Net_Client.Service.Route_Aggregation;
