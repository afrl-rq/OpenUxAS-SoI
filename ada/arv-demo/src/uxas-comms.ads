with AVTAS.LMCP.Types;  use AVTAS.LMCP.Types;  -- used by child packages

with Ada.Containers.Formal_Hashed_Sets;
with Ada.Strings.Hash;

with Dynamic_Strings; use Dynamic_Strings;

package UxAS.Comms is

   Subscription_Address_Max_Length : constant := 255; -- arbitrary

   subtype Subscription_Address is Dynamic_String (Capacity => Subscription_Address_Max_Length);
   --  a constrained subtype for the sake of instantiating the Containers generic

   function Hashed_Subscription_Address (Element : Subscription_Address) return Ada.Containers.Hash_Type is
      (Ada.Strings.Hash (Value (Element)));

   pragma Assertion_Policy (Post => Ignore);
   package Subscription_Addresses is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => Subscription_Address,
      Hash                => Hashed_Subscription_Address,
      Equivalent_Elements => "=");
   pragma Assertion_Policy (Post => Suppressible);

   Max_Subscription_Addresses : constant := 255; -- arbitrary

   subtype Subscription_Address_Set is Subscription_Addresses.Set
     (Capacity => Max_Subscription_Addresses,
      Modulus  => Subscription_Addresses.Default_Modulus (Max_Subscription_Addresses));

   --  These constants are used for defining the capacities of the dynamic
   --  strings. They are declared so that others (including child packages)
   --  can reference them when needed.
   Content_String_Max_Length           : constant := 22 * 1024;
   Content_Type_Max_Length             : constant := 255; -- arbitrary
   Descriptor_Max_Length               : constant := 255; -- arbitrary
   Source_Group_Max_Length             : constant := 255; -- arbitrary
   Source_Entity_Id_Max_Length         : constant := 255; -- arbitrary
   Source_Service_Id_Max_Length        : constant := 255; -- arbitrary
   Address_Max_Length                  : constant := 255; -- arbitrary
   Payload_Max_Length                  : constant := 22 * 1024;

   Max_Network_Name_Length             : constant := 255; -- arbitrary
   Max_Socket_Address_Length           : constant := 255; -- arbitrary

   Entity_Id_String_Max_Length         : constant := 255; -- arbitrary
   Service_Id_String_Max_Length        : constant := 255; -- arbitrary

   Msg_Source_Group_Max_Length         : constant := 255; -- arbitrary
   Entity_Type_Max_Length              : constant := 255; -- arbitrary
   Network_Id_Max_Length               : constant := 255; -- arbitrary
   Entity_Id_Max_Length                : constant := 255; -- arbitrary
   Unicast_Message_Max_Length          : constant := 255; -- arbitrary
   Network_Client_Type_Name_Max_Length : constant := 255; -- arbitrary
   Cast_All_Address_Max_Length         : constant := 255; -- arbitrary

end UxAS.Comms;
