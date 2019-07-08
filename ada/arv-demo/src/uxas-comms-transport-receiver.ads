package UxAS.Comms.Transport.Receiver is

   type Transport_Receiver_Base is abstract new Transport_Base with private;

   type Transport_Receiver_Base_Ref is access all Transport_Receiver_Base;

   type Any_Transport_Receiver_Base is access Transport_Receiver_Base'Class;

   Any_Address_Accepted : constant String := "";
   -- no filtering applied

   --  bool
   --  addSubscriptionAddress(const std::string& address);
   procedure Add_Subscription_Address
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean);

   --  bool
   --  removeSubscriptionAddress(const std::string& address);
   procedure Remove_Subscription_Address
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean);

   --  bool
   --  removeAllSubscriptionAddresses();
   procedure Remove_All_Subscription_Addresses
     (This   : in out Transport_Receiver_Base;
      Result : out Boolean);

   --  bool
   --  addSubscriptionAddressToSocket(const std::string& address) override;
   procedure Add_Subscription_Address_To_Socket
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean)
     is abstract;

   --  bool
   --  removeSubscriptionAddressFromSocket(const std::string& address) override;
   procedure Remove_Subscription_Address_From_Socket
     (This    : in out Transport_Receiver_Base;
      Address : String;
      Result  : out Boolean)
     is abstract;

private

   type Transport_Receiver_Base is abstract new Transport_Base with record
      --  std::unordered_set<std::string> m_subscriptionAddresses;
      Subscriptions : Subscription_Address_Set;
   end record;

end UxAS.Comms.Transport.Receiver;
