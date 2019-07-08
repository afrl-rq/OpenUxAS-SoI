package UxAS.Comms.Transport is

   type Transport_Base is abstract tagged limited record
      --  these are public member data in the C++ version so they are visible
      --  in this base class (even if extensions are private, as they should
      --  be)
      Entity_Id  : UInt32;
      Service_Id : UInt32;
   end record;

end UxAS.Comms.Transport;
