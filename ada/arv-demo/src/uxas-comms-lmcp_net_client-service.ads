with DOM.Core;

package UxAS.Comms.LMCP_Net_Client.Service is
   pragma Elaborate_Body;

   type Service_Base is abstract new LMCP_Object_Network_Client_Base with private;

   type Any_Service is access all Service_Base'Class;

   --    ServiceBase::ServiceBase(const std::string& serviceType, const std::string& workDirectoryName)
   --     : m_serviceType(serviceType), m_workDirectoryName(workDirectoryName)
   procedure Construct_Service
     (This                : in out Service_Base;
      Service_Type        : String;
      Work_Directory_Name : String)
     with
       Post'Class => Constructed (This);

   --      /** \brief The <B><i>configureService</i></B> method performs service configuration.
   --       * It must be invoked before calling the <B><i>initializeAndStartService</i></B>.
   --       *
   --       * @param parentOfWorkDirectory parent directory where work directory will be created
   --       * @param serviceXml XML configuration
   --       * @return true if configuration succeeds; false if configuration fails.
   --       */
   --      bool
   --      configureService(const std::string& parentOfWorkDirectory, const std::string& serviceXml);
   procedure Configure_Service
     (This                     : in out Service_Base;
      Parent_Of_Work_Directory : String;
      ServiceXml               : String;
      Result                   : out Boolean)
     with
       Pre'Class  => Constructed (This),
       Post'Class => Configured (This);

   --      /** \brief The <B><i>configureService</i></B> method performs service configuration.
   --       * It must be invoked before calling the <B><i>initializeAndStartService</i></B>.
   --       *
   --       * @param parentOfWorkDirectory parent directory where work directory will be created
   --       * @param serviceXmlNode XML configuration
   --       * @return true if configuration succeeds; false if configuration fails.
   --       */
   --      bool
   --      configureService(const std::string& parentWorkDirectory, const pugi::xml_node& serviceXmlNode);
   procedure Configure_Service
     (This                     : in out Service_Base;
      Parent_Of_Work_Directory : String;
      Service_Xml_Node         : DOM.Core.Element;
      Result                   : out Boolean)
     with
       Pre'Class  => Constructed (This),
       Post'Class => Configured (This);

   --      /** \brief The <B><i>initializeAndStartService</i></B> method performs service
   --       * initialization and startup. It must be invoked after calling the
   --       * <B><i>configureService</i></B> method. Do not use for
   --       * <B><i>ServiceManager</i></B>, instead invoke the
   --       * <B><i>initializeAndStart</i></B> method.
   --       *
   --       * @return true if all initialization and startup succeeds; false if initialization or startup fails.
   --       */
   --      bool
   --      initializeAndStartService();
   procedure Initialize_And_Start_Service
     (This   : in out Service_Base;
      Result : out Boolean)
     with
       Pre'Class => Constructed (This) and Configured (This);

   --       * \brief The <B><i>getUniqueNetworkClientId</i></B> returns a unique service ID.
   --       * It returns the ID from a call to getUniqueNetworkClientId(), which are used as service IDs
   --       *
   --       * @return unique service ID.
   --       */
   --      static int64_t
   --      getUniqueServceId()
   --      {
   --          return (getUniqueNetworkClientId());  // call static routine in base class
   --      };
   function Get_Unique_Service_Id return Int64;

--  public: -- so we provide accessors rather than have a non-private record type with a private component

   --      /** \brief unique ID of the component.  */
   --      std::uint32_t m_serviceId;
   function Get_Service_Id (This : Service_Base) return UInt32
     with Pre'Class => Constructed (This) and Configured (This);

   --      std::string m_serviceType;
   function Get_Service_Type (This : Service_Base) return String
     with Pre'Class => Constructed (This) and Configured (This);

   Service_Type_Max_Length : constant := 255; -- arbitrary

   --      std::string m_workDirectoryName;
   function Get_Work_Directory_Name (This : Service_Base) return String
     with Pre'Class => Constructed (This) and Configured (This);

   Work_Directory_Name_Max_Length : constant := 255; -- arbitrary

-----------------------------------------------------------------------------------------

   --     /** \brief The <B><i>instantiateService</i></B> method creates an instance
   --       * of a service class that inherits from <B><i>ServiceBase</i></B>
   --       *
   --       * @param serviceType type name of the service to be instantiated
   --       * @return instantiated service
   --       */
   function Instantiate_Service (Type_Name : String) return Any_Service;

   function Configured (This : Service_Base) return Boolean;
   function Constructed (This : Service_Base) return Boolean;

   Service_Type_Name_Max_Length : constant := 255; -- arbitrary

   subtype Service_Type_Name is Dynamic_String (Service_Type_Name_Max_Length);

   type Service_Type_Names_List is array (Positive range <>) of Service_Type_Name;

private

   Work_Directory_Path_Max_Length : constant := 255; -- arbitrary

   type Service_Base is abstract new LMCP_Object_Network_Client_Base with record
      Is_Constructed      : Boolean := False;
      Service_Id          : UInt32;
      Service_Type        : Service_Type_Name;
      Work_Directory_Name : Dynamic_String (Work_Directory_Name_Max_Length);
      Work_Directory_Path : Dynamic_String (Work_Directory_Path_Max_Length);

      --  In the C++ version these two components are declared as *private*
      --  for class LMCP_Object_Network_Client_Base, but then declared as
      --  *protected* in Service_Base. They would both be visible in Ada,
      --  therefore their declaration here would be illegal. We use the
      --  components declared in the root baseclass but with their default values
      --  as specified in serviceBase.h, as indicated below.
      --
      --  Is_Configured   : Boolean := False;
      --  Processing_Type : Receive_Processing_Type := LMCP;
      --
      --  TODO: verify this works!!
   end record;

   --  static service creation function implemented with non-null values by subclasses.
   --      static
   --      ServiceBase*
   --      create() { return nullptr; };
   function Create return Any_Service is
      (null);
   --  must match profile for type Service_Creation_Function_Pointer

   type Service_Creation_Function_Pointer is access function return Any_Service;
   -- to designate static function Create in each subclass's package, which when
   -- called, allocates an instance of the packages's subclass type

   --  registers service type name, alias type names and it's create() function for a subclass.
   --
   --      registerServiceCreationFunctionPointers
   procedure Register_Service_Creation_Function_Pointers
     (Service_Type_Names : Service_Type_Names_List;
      Associated_Creator : Service_Creation_Function_Pointer);

--  Every concrete subclass's package MUST call Register_Service_Creation_Function_Pointers
--  during their package body executable part, corresponding to this effect in C++ :
--
--      template <typename T>
--      struct CreationRegistrar
--      {
--          explicit
--          CreationRegistrar(const std::vector<std::string>& registryServiceTypeNames)
--          {
--              ServiceBase::registerServiceCreationFunctionPointers(registryServiceTypeNames, &T::create);
--          }
--      };

end UxAS.Comms.LMCP_Net_Client.Service;
