package PB_Data_Types is
  
  -- Input Message Type ----------------------
  -- Possible messages that can come into this service
  -- -- Note - only one of them can be true at any time
  type in_message_type is (AirVehicleState_in
                        GroundVehicleState_in,
                        TaskAssignmentSummary_in,
                        TaskImplementationResponse_in,
                        SurfaceSurfaceVehicleState_in,
                        UniqueAutomationRequest_in,
                        NoMsg);
  
  type input_message_type is record
    msg : in_message_type;
    id : Positive;
    CorrespondingAutomationRequestID : Positive;
  end record;
     
   
   
  -- Outputs ---------------------
  -- ServiceStatus_out
  -- UniqueAutomationResponse_out
  -- TaskImplementationRequest_out

  type out_message_type is (ServiceStatus_out,
                            UniqueAutomationResponse_out,
                            TaskImplementationRequest_out,
                            NoMsg);

  type output_message_type is record
    msg : out_message_type;
    id : Positive;
    CorrespondingAutomationRequestID : Positive;
  end record;

  
  -- State -----------------------
  -- The PlanBuilder is allowed to do certain operations dependent on the state
  -- of the component. 
  type state_type is (IDLE, IDLE_WAITING, BUSY_REQUESTING, BUSY_WAITING);
   
   
   

end PB_Data_Types;
