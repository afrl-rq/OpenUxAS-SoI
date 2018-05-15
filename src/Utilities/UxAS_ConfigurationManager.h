// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_CONFIGURATION_MANAGER_H
#define UXAS_COMMON_CONFIGURATION_MANAGER_H

#include "pugixml.hpp"

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace uxas
{
namespace common
{

/** \class ConfigurationManager
 * 
 * \par The <B><i>ConfigurationManager</i></B> is a singleton class that hosts 
 * UxAS entity configurations loaded from either XML strings or XML configurations. 
 * It also hosts application scope configuration values. Thread-safety not 
 * implemented.
 * 
 * @n
 */
class ConfigurationManager final
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("ConfigurationManager"); return (s_string); };

    /** \brief Accessor for <B><i>ConfigurationManager</i></B> singleton.
     * 
     * @return reference to the singleton instance of <B><i>ConfigurationManager</i></B>.
     */
    static ConfigurationManager&
    getInstance();

    ~ConfigurationManager() { };

private:

    // \brief Prevent direct, public construction (singleton pattern)
    ConfigurationManager() { };

    // \brief Prevent copy construction
    ConfigurationManager(ConfigurationManager const&) = delete;

    // \brief Prevent copy assignment operation
    void operator=(ConfigurationManager const&) = delete;

public:
    
//    //buildUxasMasterFile cfg file UTILITY ONLY
//    bool
//    buildUxasMasterFile();

    /** \brief UxAS component-specific data directory name as a sub-directory of 
     * the application root data directory. TODO - assure uniqueness.
     * 
     * @return data directory name.
     */
    static std::string
    getComponentDataDirectory(const std::string& directoryName)
    { return (s_rootDataInDirectory + directoryName + ((*(directoryName.rbegin()) == '/') ? "" : "/")); };
    
    /** \brief UxAS application root data directory that hosts
     * sub-directories containing input data for components (e.g., services). 
     * Components should only read data from these sub-directories . In-work and 
     * output data should be written to a <i>work</i> directory - see 
     * getRootDataWorkDirectory method.
     * 
     * @return root data directory.
     */
    static std::string
    getRootDataInDirectory() { return (s_rootDataInDirectory); };
    
    /** \brief UxAS application root work directory that hosts
     * sub-directories containing in-work and/or output files created by 
     * components (e.g., services). For the case of reading data, components 
     * should read data from a <i>data</i> directory - see getRootDataInDirectory 
     * method.
     * 
     * @return root data directory.
     */
    static const std::string&
    getRootDataRefDirectory() { return (s_rootDataRefDirectory); };
    
    /** \brief UxAS application root work directory that hosts
     * sub-directories containing in-work and/or output files created by 
     * components (e.g., services). For the case of reading data, components 
     * should read data from a <i>data</i> directory - see getRootDataInDirectory 
     * method.
     * 
     * @return root data directory.
     */
    static const std::string&
    getRootDataWorkDirectory() { return (s_rootDataWorkDirectory); };
    
    /** \brief UxAS entity application start time as duration since epoch in milliseconds.
     * 
     * @return start time since epoch.
     */
    static const int64_t
    getEntityStartTimeSinceEpoch_ms() { return (s_entityStartTimeSinceEpoch_ms); };
    
    /** \brief UxAS entity ID.
     * 
     * @return entity ID.
     */
    static const uint32_t
    getEntityId() { return (s_entityId); };
    
    /** \brief UxAS entity type.
     * 
     * @return VICS entity type as a string value.
     */
    static const std::string&
    getEntityType() { return (s_entityType); };
    
    /** \brief LogManager configuration to include thread ID in log.
     * 
     * @return true implies include thread ID in log statements
     */
    static const bool
    getIsLoggingThreadId() { return (s_isLoggingThreadId); };
    
    /** \brief LogManager configuration to timestamp logs.
     *
     * @return true implies include a timestamp in log file names 
     */
    static const bool
    getIsDataTimeStamp() { return s_isDataTimestamp; };

    /** \brief Zero MQ single-part/multi-part messaging boolean.
     * 
     * @return true if using Zero MQ multi-part messaging; false if using Zero MQ 
     * single-part messaging
     */
    static const bool
    getIsZeroMqMultipartMessage() { return (s_isZeroMqMultipartMessage); };
  
    /** \brief UxAS application run duration (units: seconds).
     * 
     * @return Run duration in seconds.
     */
    static const uint32_t
    getRunDuration_s() { return (s_runDuration_s); };
    
    /** \brief Zero MQ receive socket poll wait duration (units: milliseconds).
     * 
     * @return Wait duration in milliseconds.
     */
    static const uint32_t
    getSerialPortWaitTime_ms() { return (s_serialPortWaitTime_ms); };

    /** \brief UxAS application start delay (units: milliseconds).
     * 
     * @return application start delay in milliseconds.
     */
    static const uint32_t
    getStartDelay_ms() { return (s_startDelay_ms); };

    /** \brief Zero MQ receive socket poll wait duration (units: milliseconds).
     * 
     * @return Wait duration in milliseconds.
     */
    static const int32_t
    getZeroMqReceiveSocketPollWaitTime_ms() { return (s_zeroMqReceiveSocketPollWaitTime_ms); };

    /** \brief The <B><i>loadBaseXmlFile</i></B> method loads base configurations.
     * 
     * @param xmlFilePath location of XML file containing base configuration.
     * @return true if XML load succeeds; false if XML load fails.
     */
    bool
    loadBaseXmlFile(const std::string& xmlFilePath = "./cfg/cfgbase.xml");

    /** \brief The <B><i>loadBaseXmlString</i></B> method loads base configurations.
     * 
     * @param xmlString XML string containing base configuration.
     * @return true if XML load succeeds; false if XML load fails.
     */
    bool
    loadBaseXmlString(const std::string& xmlString);

    /** \brief The <B><i>unloadBaseXml</i></B> method unloads base configurations.
     */
    void
    unloadBaseXml();

    /** \brief The <B><i>unloadXml</i></B> method unloads base configuration.
     */
    void
    unloadXml();

    /** \brief The <B><i>getDefaultServiceXmlNode</i></B> method retrieves the default 
     * configurations for the specified service type.  If the <b>serviceType</b> 
     * parameter is not provided, then all default services configurations 
     * are returned. The configurations are resolved from base XML.
     * 
     * @param serviceType type name of requested service configuration.
     * @return XML string containing service configuration or empty string.
     */
    std::string
    getDefaultServiceXmlNode(const std::string& serviceType = "");

    /** \brief The <B><i>getEnabledBridges</i></B> method returns bridge 
     * configurations for bridges to be enabled at entity startup. 
     * The configurations are resolved from base XML.
     * 
     * @return UxAS XML node containing zero-many Bridge nodes, each containing 
     * a set of configurations.
     */
    pugi::xml_node
    getEnabledBridges();

    /** \brief The <B><i>getEnabledServices</i></B> method returns service 
     * configurations for services to be enabled at entity startup. 
     * The configurations are resolved from base XML.
     * 
     * @return UxAS XML node containing zero-many services.
     */
    pugi::xml_node
    getEnabledServices();

private:

    void
    addComponentXmlNode(pugi::xml_node& uxasNode, const std::string& nodeName);
    
    /** \brief The <B><i>populateEnabledComponentXmlNode</i></B> method adds 
     * zero-many bridge or service configuration nodes as implied by loaded base 
     * XML.
     * 
     * @param uxasNode UxAS XML node to be populated.
     * @param nodeName name of nodes to be added to UxAS XML node (e.g., Bridge, Service).
     * @param typeName name of type that constrains requested configurations (optional).
     */
    void
    populateEnabledComponentXmlNode(pugi::xml_node& uxasNode, const std::string& nodeName);
    
    /** \brief The <B><i>loadXml</i></B> method implements the loading of 
     * base or extension XML.
     * 
     * @param xml either location of XML file or an XML string.
     * @param isFile true implies <b>xml</b> parameter is a file location; false 
     * implies <b>xml</b> parameter is an XML string.
     * @param isBaseXml true implies loading base XML; false implies loading 
     * extension XML.
     * @param isSetEntityPptys true enables setting of entity ID and entity type (optional)
     * from XML; false disables load of entity properties.
     * @return true if XML load succeeds; false if XML load fails.
     */
    bool
    loadXml(const std::string& xml, bool isFile, bool isBaseXml, bool isSetEntityPptys = false);

    /** \brief The <B><i>setEntityValuesFromXmlNode</i></B> method sets entity values 
     * found within attributes of the UxAS node.
     * 
     * @param xmlNode extension XML containing entity values.
     * @return true if entity ID and entity type are set; 
     * false if either entity ID or entity type are not found in XML.
     */
    bool
    setEntityValuesFromXmlNode(const pugi::xml_node& xmlNode);

    /** \brief The <B><i>loadUtilityValuesFromXmlNode</i></B> method loads 
     * found within child nodes of the UxAS node. After loading the values
     * the utility initialization functions are called.
     * 
     * @param xmlNode extension XML containing entity values.
     */
    void
    loadUtilityValuesFromXmlNode(const pugi::xml_node& xmlNode);
    
////cfg_RoadMonitor2_V400.xml
////TcpBridge
////ICET_CCA
////RoadMonitor
////WaypointPlanManager
////VicsInterface
////VicsLogger
////SendTestMessages
////SendIsolationStatus
////SendMessages
////MessageLogger
//
//     //
//     // cfgext.xml (extension XML listing entity services at boot-up with override values if/when required)
//     //
//<?xml version="1.0" encoding="UTF-8" standalone="yes" ?>
//<UxAS FormatVersion="1.0" EntityID="33" EntityType="Aircraft">
//    <!-- DBK, RJT 20150825 notional configuration XML design notes (also see cfgbase.xml) -->
//    <!-- CONCEPT: first read cfgbase.xml file, then read cfgext.xml file (if conflicting values, then value from cfgext.xml is retained) -->
//
//    <!-- entity bridges to instantiate at start-up -->
//    <Bridge Type="LmcpObjectNetworkSerialBridge"/>
//    <!-- TCP bridge using all default values -->
//    <Bridge Type="LmcpObjectNetworkTcpBridge"/>
//    <!-- TCP bridge using all default values - but overriding TcpAddress and IsServer -->/>
//    <Bridge Type="LmcpObjectNetworkTcpBridge" TcpAddress="tcp://127.0.0.1:5557" IsServer="TRUE">
//    <Bridge Type="LmcpObjectNetworkSubscribePushBridge"/>
//
//    <!-- entity services to instantiate at start-up -->
//    <Service Type="MessageLogger">
//        <LogMessage MessageType="lmcp:CMASI:" NumberMessagesToSkip="0"/> <!-- REVIEW: this overrides list of LogMessages in cfgbase.xml -->
//    </Service>
//    <Service Type="VicsInterface"/>
//    <Service Type="VicsLogger"/>
//
//</UxAS>
//
//     //
//     // cfgbase.xml (base XML containing all default values)
//     //
//<?xml version="1.0" encoding="UTF-8" standalone="yes" ?>
//<UxAS FormatVersion="1.0">
//    <!-- DBK, RJT 20150825 notional configuration XML design notes (also see cfgext.xml)  -->
//    <!-- default configurations for bridges and services (which are all components) -->
//    <Bridge Type="LmcpObjectNetworkSerialBridge" BaudRate="57600" SerialPortAddress="/dev/ttyO2"/>
//    <Bridge Type="LmcpObjectNetworkTcpBridge" TcpAddress="tcp://127.0.0.1:5556" Server="FALSE">
//        <SubscribeToMessage MessageType="lmcp:CMASI:"/>
//        <SubscribeToMessage MessageType="lmcp:VICS:"/>
//        <SubscribeToMessage MessageType="lmcp:ISOLATE:"/>
//    </Bridge>
//    <Bridge Type="LmcpObjectNetworkSubscribePushBridge"/>
//        <ExternalZeroMqSubscribeAddress value="tcp://*:5555"/>
//        <ExternalZeroMqPushAddress value="tcp://*:5556"/>
//    <Bridge Type="LmcpObjectNetworkZeroMqZyreBridge">
//        <SubscribeToMessage MessageType="lmcp:UXNATIVE:"/>
//    </Bridge>
//    <Service Type="MessageLogger" FilesPerSubDirectory="1000">
//        <LogMessage MessageType="lmcp:UXNATIVE" NumberMessagesToSkip="0"/>
//        <LogMessage MessageType="lmcp:CreateNewComponent" NumberMessagesToSkip="0"/>
//        <LogMessage MessageType="lmcp:KillComponent" NumberMessagesToSkip="0"/>
//        <LogMessage MessageType="lmcp:ISOLATE:" NumberMessagesToSkip="0"/>
//        <LogMessage MessageType="lmcp:UXCOMM:" NumberMessagesToSkip="0"/>
//        <LogMessage MessageType="lmcp:CMASI:MissionCommand" NumberMessagesToSkip="0" />
//        <LogMessage MessageType="lmcp:CCA_Plan" NumberMessagesToSkip="0" />
//        <LogMessage MessageType="lmcp:SUBTASK" NumberMessagesToSkip="0" />
//    </Service>
//    <Service Type="VicsInterface" SendGreenOnEmptyQueryResponse="TRUE" AmaseMode="TRUE"/>
//    <!-- Saves received vics messages in a structure for retrival by a vics interface component -->
//    <Service Type="VicsLogger" FilesPerSubDirectory="500"/>
//</UxAS>

public:
    static std::string s_rootDataWorkDirectory;
    
private:
    
    static int64_t s_entityStartTimeSinceEpoch_ms;
    static uint32_t s_entityId;
    static std::string s_entityType;
    static bool s_isLoggingThreadId;
    static bool s_isDataTimestamp;
    static bool s_isZeroMqMultipartMessage;
    static uint32_t s_runDuration_s;
    static uint32_t s_serialPortWaitTime_ms;
    static uint32_t s_startDelay_ms;
    static int32_t s_zeroMqReceiveSocketPollWaitTime_ms;

    static std::string s_rootDataInDirectory;
    static std::string s_rootDataRefDirectory;

    static std::unique_ptr<ConfigurationManager> s_instance;
    
    bool m_isEnabledBridgesXmlDocBuilt{false};
    pugi::xml_document m_enabledBridgesXmlDoc;

    bool m_isEnabledServicesXmlDocBuilt{false};
    pugi::xml_document m_enabledServicesXmlDoc;

    bool m_isBaseXmlDocLoaded{false};
    pugi::xml_document m_baseXmlDoc;

};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_CONFIGURATION_MANAGER_H */
