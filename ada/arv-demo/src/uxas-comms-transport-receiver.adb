package body UxAS.Comms.Transport.Receiver is

   ------------------------------
   -- Add_Subscription_Address --
   ------------------------------

   procedure Add_Subscription_Address
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean)
   is
      Target : constant Subscription_Address := Instance (Subscription_Address_Max_Length, Address);
      use Subscription_Addresses;  -- a hashed map
      C : Cursor;
   begin
      C := Find (This.Subscriptions, Target);
      if C = No_Element then -- didn't find it
         Insert (This.Subscriptions, Target);
         Add_Subscription_Address_To_Socket (Transport_Receiver_Base'Class (This), Address, Result);  -- dispatching
      end if;
   end Add_Subscription_Address;

   ---------------------------------
   -- Remove_Subscription_Address --
   ---------------------------------

   procedure Remove_Subscription_Address
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean)
   is
      Target : constant Subscription_Address := Instance (Subscription_Address_Max_Length, Address);
      use Subscription_Addresses;  -- a hashed map
      C : Cursor;
   begin
      C := Find (This.Subscriptions, Target);
      if C /= No_Element then -- found it
         Delete (This.Subscriptions, C);
         Remove_Subscription_Address_From_Socket (Transport_Receiver_Base'Class (This), Address, Result);  -- dispatching
      end if;
   end Remove_Subscription_Address;

   ---------------------------------------
   -- Remove_All_Subscription_Addresses --
   ---------------------------------------

   procedure Remove_All_Subscription_Addresses
     (This   : in out Transport_Receiver_Base;
      Result : out Boolean)
   is
   begin
      for Target of This.Subscriptions loop
         Remove_Subscription_Address_From_Socket (Transport_Receiver_Base'Class (This), Value (Target), Result);  -- dispatching
      end loop;
      Subscription_Addresses.Clear (This.Subscriptions);
      Result := Subscription_Addresses.Is_Empty (This.Subscriptions);
   end Remove_All_Subscription_Addresses;

end UxAS.Comms.Transport.Receiver;
