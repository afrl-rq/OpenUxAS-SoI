--  TODO: maybe move contents to package Transport for sharing by children?

package UxAS.Comms.Transport.Socket_Configurations is

   type Socket_Configuration is tagged record
      Network_Name   : Dynamic_String (Capacity => Max_Network_Name_Length );
      Socket_Address : Dynamic_String (Capacity => Max_Socket_Address_Length );
      Is_Receive     : Boolean;
   end record;

end UxAS.Comms.Transport.Socket_Configurations;
