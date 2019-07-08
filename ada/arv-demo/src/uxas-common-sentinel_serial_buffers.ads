with AVTAS.LMCP.Types;  use AVTAS.LMCP.Types;

with Dynamic_Strings; use Dynamic_Strings;

package UxAS.Common.Sentinel_Serial_Buffers is

   Type_Name : constant String := "SerialStringSentinel";

   Sentinal_Buffer_Max_Capacity : constant := 2 * 1024; -- arbitrary  TODO: see how big it really needs to be

   subtype Buffer_Capacity is Integer range 1 .. Sentinal_Buffer_Max_Capacity;

   type Sentinel_Serial_Buffer (Capacity : Buffer_Capacity) is tagged limited record
      --  These are all public in the C++ version...
      Data                      : Dynamic_String (Capacity);
      Valid_Deserialize_Count   : UInt32 := 0;
      Invalid_Deserialize_Count : UInt32 := 0;
      Disregarded_Data_Count    : UInt32 := 0;
   end record;

   --  std::string
   --  getNextPayloadString(const std::string& newDataChunk);
   procedure Get_Next_Payload_String
     (This           : in out Sentinel_Serial_Buffer;
      New_Data_Chunk : String;
      Result         : out String);

   --  static std::string
   --  createSentinelizedString(const std::string& data);
   function Create_Sentinelized_String (Data : String ) return String;

   --  Supports strings containing only ascii characters
   --  static uint32_t
   --  calculateChecksum(const std::string& str);
   function Calculated_Checksum (Str : String) return UInt32;

   --  static std::unique_ptr<std::string>
   --  getDetectSentinelBaseStringsMessage(const std::string& data);
   function Get_Detect_Sentinel_Base_Strings_Message (Data : String) return String;

   --  static const std::string&
   --  getSerialSentinelBeforePayloadSize() { static std::string s_string("+=+=+=+="); return(s_string); };
   Serial_Sentinel_Before_Payload_Size : constant String (1 .. 8) := "+=+=+=+=";

   --  static const uint32_t
   --  getSerialSentinelBeforePayloadSizeSize() { static const uint32_t s_sz = getSerialSentinelBeforePayloadSize().size(); return(s_sz); };
   Serial_Sentinel_Before_Payload_Size_Size : constant := Serial_Sentinel_Before_Payload_Size'Length;

   --  static const std::string&
   --  getSerialSentinelBeforePayloadSizeBase() { static std::string s_string("+="); return(s_string); };
   Serial_Sentinel_Before_Payload_Size_Base : constant String (1 .. 2) := "+=";

   --  static const uint32_t
   --  getSerialSentinelBeforePayloadSizeBaseSize() { static const uint32_t s_sz = getSerialSentinelBeforePayloadSizeBase().size(); return(s_sz); };
   Serial_Sentinel_Before_Payload_Size_Base_Size : constant := Serial_Sentinel_Before_Payload_Size_Base'Length;

   --  static const std::string&
   --  getSerialSentinelAfterPayloadSize() { static std::string s_string("#@#@#@#@"); return(s_string); };
   Serial_Sentinel_After_Payload_Size : constant String (1 .. 8) := "#@#@#@#@";

   --  static const uint32_t
   --  getSerialSentinelAfterPayloadSizeSize() { static const uint32_t s_sz = getSerialSentinelAfterPayloadSize().size(); return(s_sz); };
   Serial_Sentinel_After_Payload_Size_Size : constant := Serial_Sentinel_After_Payload_Size'Length;

   --  static const std::string&
   --  getSerialSentinelAfterPayloadSizeBase() { static std::string s_string("#@"); return(s_string); };
   Serial_Sentinel_After_Payload_Size_Base : constant String (1 .. 2) := "#@";

   --  static const uint32_t
   --  getSerialSentinelAfterPayloadSizeBaseSize() { static const uint32_t s_sz = getSerialSentinelAfterPayloadSizeBase().size(); return(s_sz); };
   Serial_Sentinel_After_Payload_Size_Base_Size : constant := Serial_Sentinel_After_Payload_Size_Base'Length;

   --  static const std::string&
   --  getSerialSentinelBeforeChecksum() { static std::string s_string("!%!%!%!%"); return(s_string); };
   Serial_Sentinel_Before_Checksum : constant String (1 .. 8) := "!%!%!%!%";

   --  static const uint32_t
   --  getSerialSentinelBeforeChecksumSize() { static const uint32_t s_sz = getSerialSentinelBeforeChecksum().size(); return(s_sz); };
   Serial_Sentinel_Before_Checksum_Size : constant := Serial_Sentinel_Before_Checksum'Length;

   --  static const std::string&
   --  getSerialSentinelBeforeChecksumBase() { static std::string s_string("!%"); return(s_string); };
   Serial_Sentinel_Before_Checksum_Base : constant String (1 .. 2) := "!%";

   --  static const uint32_t
   --  getSerialSentinelBeforeChecksumBaseSize() { static const uint32_t s_sz = getSerialSentinelBeforeChecksumBase().size(); return(s_sz); };
   Serial_Sentinel_Before_Checksum_Base_Size : constant := Serial_Sentinel_Before_Checksum_Base'Length;

   --  static const std::string&
   --  getSerialSentinelAfterChecksum() { static std::string s_string("?^?^?^?^"); return(s_string); };
   Serial_Sentinel_After_Checksum : constant String (1 .. 8) := "?^?^?^?^";

   --  static const uint32_t
   --  getSerialSentinelAfterChecksumSize() { static const uint32_t s_sz = getSerialSentinelAfterChecksum().size(); return(s_sz); };
   Serial_Sentinel_After_Checksum_Size : constant := Serial_Sentinel_After_Checksum'Length;

   --  static const std::string&
   --  getSerialSentinelAfterChecksumBase() { static std::string s_string("?^"); return(s_string); };
   Serial_Sentinel_After_Checksum_Base : constant String (1 .. 2) := "?^";

   --  static const uint32_t
   --  getSerialSentinelAfterChecksumBaseSize() { static const uint32_t s_sz = getSerialSentinelAfterChecksumBase().size(); return(s_sz); };
   Serial_Sentinel_After_Checksum_Base_Size : constant := Serial_Sentinel_After_Checksum_Base'Length;

   --  static const std::string&
   --  getValidIntegerDigits() { static std::string s_string("1234567890"); return(s_string); };
   Valid_Integer_Digits : constant String (1 .. 10) := "1234567890";

end UxAS.Common.Sentinel_Serial_Buffers;
