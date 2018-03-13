// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Detection.h
 * Author: SeanR
 *
 * Created on Feb 06 2018
 */

#ifndef UXAS_DAIDALUS_WCV_DETECTION_H
#define UXAS_DAIDALUS_WCV_DETECTION_H



#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "TypeDefs/UxAS_TypeDefs_Timer.h"
#include "Daidalus.h"
#include "Constants/Convert.h"
#include "Position.h"
#include "Velocity.h"
namespace uxas
{
namespace service
{

/*! \class DAIDALUS_WCV_Detection
    \brief This is a basic service that can be used as a template when 
 * constructing new services.

 * 
 * 
 *  @par To add a new service:
 * <ul style="padding-left:1em;margin-left:0">
 * <li>Make copies of the source and header files of this template.</li>
 * <li>Search for the string DAIDALUS_WCV_Detection and Replace it with the new 
 * service name.</li>
 * <li>Change the unique include guard entries, in the header file, i.e. 
 * "UXAS_00_SERVICE_TEMPLATE_H" to match the new service name</li>
 * <li> include the new service header file in ServiceManager.cpp</li>
 * <li> add a dummy instance of the new service in ServiceManager.cpp, e.g.
 * {auto svc = uxas::stduxas::make_unique<uxas::service::MyNewService>();} 
 * Note: this is required to link the new service in when building UxAS</li>
 *  
 * </ul> @n
 * 
 * Configuration String: <Service Type="DAIDALUS_WCV_Detection" OptionString="Option_01" OptionInt="36" />
 * 
 * Options:
 *  - OptionString - sample string option
 *  - OptionInt - sample integer option
 * 
 * Subscribed Messages:
 *  - afrl::cmasi::KeyValuePair
 * 
 * Sent Messages:
 *  - afrl::cmasi::KeyValuePair
 * 
 * 
 */

class DAIDALUS_WCV_Detection : public ServiceBase
{
public:

    /** \brief This string is used to identify this service in XML configuration
     * files, i.e. Service Type="DAIDALUS_WCV_Detection". It is also entered into
     * service registry and used to create new instances of this service. */
    static const std::string&
    s_typeName()
    {
        static std::string s_string("DAIDALUS_WCV_Detection");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };

    /** \brief If this string is not empty, it is used to create a data 
     * directory to be used by the service. The path to this directory is
     * accessed through the ServiceBase variable m_workDirectoryPath. */
    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create()
    {
        return new DAIDALUS_WCV_Detection;
    };

    DAIDALUS_WCV_Detection();

    virtual
    ~DAIDALUS_WCV_Detection();

private:

    static
    ServiceBase::CreationRegistrar<DAIDALUS_WCV_Detection> s_registrar;

    /** brief Copy construction not permitted */
    DAIDALUS_WCV_Detection(DAIDALUS_WCV_Detection const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(DAIDALUS_WCV_Detection const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    bool
    start() override;

    bool
    terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


private:
    // storage for the option entries
    std::string m_option01 = std::string("No Option 1");
    int32_t m_option02{0};
    //DAIDALUS parameters
    int32_t m_lookahead_time = {180};   // seconds--Time horizon of all DAIDALUS functions (time)
    double m_left_trk = {n_Const::c_Convert::toDegrees(n_Const::c_Convert::dPi())}; // degrees--relative maximum horizontal direction maneuver to the left of the current ownship direction (angle)
    double m_right_trk = {n_Const::c_Convert::toDegrees(n_Const::c_Convert::dPi())};    // degrees--relative maximum horizontal direction maneuver to the right of the current ownship direction (angle)
    double m_min_gs = {5.1444}; // meters per second--absolute minimum horizontal speed maneuver (speed)
    double m_max_gs = {360.111};    // meters per second--absolute maximum horizontal speed maneuver (speed)
    double m_min_vs = {-30.48}; // meters per second--absolute minimum vertical speed maneuver (speed)
    double m_max_vs = {30.48};  // meters per second--absolute maximum vertical speed maneuver (speed)
    double m_min_alt = {100*n_Const::c_Convert::dFeetToMeters()};   // meters--absolute minimum altitude maneuver (altitude)
    double m_max_alt = {50000*n_Const::c_Convert::dFeetToMeters()}; // meters--absolute maximum altitude maneuver (altitude)
    double m_trk_step = {1.0};  // degrees--granularity of horizontal direction maneuvers (angle)
    double m_gs_step = {2.57222};   // meters per second--granularity of horizontal speed maneuvers (speed)
    double m_vs_step = {100.0/60.0*n_Const::c_Convert::dFeetToMeters()}; // meters per second--granularity of vertical speed maneuvers (speed)
    double m_alt_step = {100*n_Const::c_Convert::dFeetToMeters()};  // meters--granularity of altitude maneuvers (altitude)
    double m_horizontal_accel = {0.0};  // meters per second per second--horizontal acceleration used in computation of horizontal speed maneuvers (acceleration)
    double m_vertical_accel = {0.0};    // gravity--vertical acceleration used in the computation of horizontal speed maneuvers (acceleration)
    double m_turn_rate = {0.0}; // degrees per second--turn rate used in the computation of horizontal direction maneuvers (angle)
    double m_bank_angle = {0.0};    // degrees--bank angle used in the computation of horizontal direction maneuvers (angle)
    double m_vertical_rate = {0.0}; //meters per second--vertical rate used in the computation of altitude maneuvers (speed)
    int32_t m_recovery_stability_time = {0};  // seconds--time delay to stabilize recovery maneuvers 
    double m_min_horizontal_recovery = {1222.32};   // meters--minimum horizontal separation used in the computation of recovery maneuvers (distance)
    double m_min_vertical_recovery = {450.0*n_Const::c_Convert::dFeetToMeters()}; // meters--minimum vertical separation used in the computation of recovery maneuvers (distance)
    bool m_recovery_trk = {true};   // Boolean--enable computation of horizontal direction recovery maneuvers (boolean)
    bool m_recovery_gs = {true};    // Boolean--enable computation of horizontal speed recovery maneuvers
    bool m_recovery_vs = {true};    // Boolean--enable computation of vertical speed recovery maneuvers
    bool m_recovery_alt = {true};   // Boolean--enable computation of altitude recovery maneuvers
    bool m_ca_bands = {false};  // Boolean--enable computation of collision avoidance maneuvers
    double m_ca_factor = {0.2}; //factor to reduce min horizontal/vertical recovery separation when computing collision avoidance maneuvers (scalar (0,1])
    double m_horizontal_nmac = {500.0*n_Const::c_Convert::dFeetToMeters()};    // meters--Horizontal Near Mid-Air Collision (distance)
    double m_vertical_nmac = {100.0*n_Const::c_Convert::dFeetToMeters()};   // meters--Vertical Near Mid-Air Collision (distance)
    double m_contour_thr = {180.0}; // degrees--threshold relative to ownship horizontal direction for the computation of horizontal contours aka. blobs (angle)
    //double m_DMOD = {}; //meters
    //double m_HMOD = {};   //meters
    //int32_t m_TAUMOD = {35};  //seconds
    //double m_ZTHR= {450*n_Const::c_Convert::dFeetToMeters()}; //meters
    //-*/
    
    //
     struct daidalus_package{
       larcfm::Position daidalusPosition;
        larcfm::Velocity daidalusVelocity;
        double daidalusTime;
    };
    larcfm::Daidalus daa;
    std::unordered_map<int64_t, daidalus_package> daidalusVehicleInfo;

};

} //namespace service
} //namespace uxas

#endif /* UXAS_DAIDALUS_WCV_DETECTION_H */

