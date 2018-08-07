// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   DAIDALUS_WCV_Detection.cpp
 * Author: SeanR
 *
 *
 *
 * <Service Type="DAIDALUS_WCV_Detection" OptionString="Option_01" OptionInt="36" />
 * 
 */

// include header for this service
#include "DAIDALUS_WCV_Detection.h"

#include "afrl/cmasi/AirVehicleState.h"
#include "BandsRegion.h"
#include "Detection3D.h"
#include "Interval.h"
#include "TrafficState.h"
#include "WCVTable.h"
#include "WCV_TAUMOD.h"
#include "WCV_TCPA.h"
#include "WCV_TEP.h"
#include "larcfm/DAIDALUS/DAIDALUSConfiguration.h"
#include "larcfm/DAIDALUS/WellClearViolationIntervals.h"
#include "uxas/messages/uxnative/StartupComplete.h"
#include "stdUniquePtr.h"

#include <iostream>     // std::cout, cerr, etc
#include <cmath>    //cmath::cos, sin, etc
#include <string>   //std::to_string etc


// convenience definitions for the option strings
#define STRING_XML_LOOKAHEADTIME "LookAheadTime"
#define STRING_XML_LEFTTRACK "LeftTrack"
#define STRING_XML_RIGHTTRACK "RightTrack"
#define STRING_XML_MINGROUNDSPEED "MinGroundSpeed"
#define STRING_XML_MAXGROUNDSPEED "MaxGroundSpeed"
#define STRING_XML_MINVERTICALSPEED "MinVerticalSpeed"
#define STRING_XML_MAXVERTICALSPEED "MaxVerticalSpeed"
#define STRING_XML_MINALTITUDE "MinAltitude"
#define STRING_XML_MAXALTITUDE "MaxAltitude"
#define STRING_XML_TRACKSTEP "TrackStep"
#define STRING_XML_GROUNDSPEEDSTEP "GroundSpeedStep"
#define STRING_XML_VERTICALSPEEDSTEP "VerticalSpeedStep"
#define STRING_XML_ALTITUDESTEP "AltitudeStep"
#define STRING_XML_HORIZONTALACCELERATION "HorizontalAcceleration"
#define STRING_XML_VERTICALACCELERATION "VerticalAcceleration"
#define STRING_XML_TURNRATE "TurnRate"
#define STRING_XML_BANKANGLE "BankAngle"
#define STRING_XML_VERTICALRATE "VerticalRate"
#define STRING_XML_RECOVERYSTABILITYTIME "RecoveryStabilityTime"
#define STRING_XML_MINHORIZONTALRECOVERY "MinHorizontalRecovery"
#define STRING_XML_MINVERTICALRECOVERY "MinVerticalRecovery"
#define STRING_XML_ISRECOVERYTRACK "isRecoveryTrack"
#define STRING_XML_ISRECOVERYGROUNDSPEED "isRecoveryGroundSpeed"
#define STRING_XML_ISRECOVERYVERTICALSPEED "isRecoveryVerticalSpeed"
#define STRING_XML_ISRECOVERYALTITUDE "isRecoveryAltitude"
#define STRING_XML_ISCOLLISIONAVOIDANCE "isCollisionAvoidance"
#define STRING_XML_COLLISIONAVOIDANCEFACTOR "CollisionAvoidanceFactor"
#define STRING_XML_HORIZONTALNMAC "HorizontalNMAC"
#define STRING_XML_VERTICALNMAC "VerticalNMAC"
#define STRING_XML_HORIZONTALCONTOURTHRESHOLD "HorizontalContourThreshold"
#define STRING_XML_TTHR "TTHR"
#define STRING_XML_RTCAALERTLEVELS "RTCAAlertLevels"
#define STRING_XML_ALERTTIME1 "AlertTime1"
#define STRING_XML_EARLYALERTTIME1 "EarlyAlertTime1"
#define STRING_XML_ALERTTIME2 "AlertTime2"
#define STRING_XML_EARLYALERTTIME2 "EarlyAlertTime2"
#define STRING_XML_ALERTTIME3 "AlertTime3"
#define STRING_XML_EARLYALERTTIME3 "EarlyAlertTime3"
#define STRING_XML_HORIZONTALDETECTIONTYPE "HorizontalDetectionType"



// useful definitions
#define MILLISECONDTOSECOND 1.0/1000.0

//todo add units to variable names
namespace {
    void makeVelocityXYZ(double u, double v, double w, double Phi_rad, double Theta_rad, double Psi_rad, double& velocityX, double& velocityY, 
            double& velocityZ)
    {
        velocityX = std::cos(Theta_rad)*std::cos(Psi_rad)*u + (std::sin(Phi_rad)*std::sin(Theta_rad)*std::cos(Psi_rad)- 
                std::cos(Phi_rad)*std::sin(Psi_rad))*v + (std::cos(Phi_rad)*std::sin(Theta_rad)*std::cos(Psi_rad) + 
                std::sin(Phi_rad)*std::sin(Psi_rad))*w;
        velocityY = std::cos(Theta_rad)*std::sin(Psi_rad)*u + (std::sin(Phi_rad)*std::sin(Theta_rad)*std::sin(Psi_rad)+ 
                std::cos(Phi_rad)*std::cos(Psi_rad))*v + (std::cos(Phi_rad)*std::sin(Theta_rad)*std::sin(Psi_rad)- 
                std::sin(Phi_rad)*std::cos(Psi_rad))*w;
        velocityZ = -std::sin(Theta_rad)*u + std::sin(Phi_rad)*std::cos(Theta_rad)*v + std::cos(Phi_rad)*std::cos(Theta_rad)*w;
    }
    std::unique_ptr<larcfm::Detection3D> makeDetectionPtr(const std::string type, const larcfm::WCVTable table)
    {
        std::unique_ptr<larcfm::Detection3D> ptr;
        if (type == "TCPA")
        {
            ptr = uxas::stduxas::make_unique<larcfm::WCV_TCPA>(table);
        }
        else if (type == "TEP")
        {
            ptr = uxas::stduxas::make_unique<larcfm::WCV_TEP>(table);
        }
        else
        {
            ptr = uxas::stduxas::make_unique<larcfm::WCV_TAUMOD>(table);
        }
        return ptr;
    }
}

// namespace definitions
namespace uxas  // uxas::
{
namespace service   // uxas::service::
{   

// this entry registers the service in the service creation registry
DAIDALUS_WCV_Detection::ServiceBase::CreationRegistrar<DAIDALUS_WCV_Detection>
DAIDALUS_WCV_Detection::s_registrar(DAIDALUS_WCV_Detection::s_registryServiceTypeNames());

// service constructor
DAIDALUS_WCV_Detection::DAIDALUS_WCV_Detection()
: ServiceBase(DAIDALUS_WCV_Detection::s_typeName(), DAIDALUS_WCV_Detection::s_directoryName()) { }; 

// service destructor
DAIDALUS_WCV_Detection::~DAIDALUS_WCV_Detection() { };

bool DAIDALUS_WCV_Detection::configure(const pugi::xml_node& ndComponent)
{
    bool isSuccess(true);
    bool useBankAngle = false;
    // process options from the XML configuration node:
    if (!ndComponent.attribute(STRING_XML_LOOKAHEADTIME).empty())
    {
       double local_lookahead_time_s = ndComponent.attribute(STRING_XML_LOOKAHEADTIME).as_double();
       if (local_lookahead_time_s > 0.0)
       {
           m_lookahead_time_s = local_lookahead_time_s;
       }
    }
    if (!ndComponent.attribute(STRING_XML_LEFTTRACK).empty())
    {
       double local_left_trk_deg = ndComponent.attribute(STRING_XML_LEFTTRACK).as_double();
       if (local_left_trk_deg > 0.0 && local_left_trk_deg <= 180.0)
       {
           m_left_trk_deg = local_left_trk_deg;
       }
    }
    if (!ndComponent.attribute(STRING_XML_RIGHTTRACK).empty())
    {
       double local_right_trk_deg = ndComponent.attribute(STRING_XML_RIGHTTRACK).as_double();
       if (local_right_trk_deg >0.0 && local_right_trk_deg <=180.0)
       {
           m_right_trk_deg = m_right_trk_deg;
       }
    }
    if (!ndComponent.attribute(STRING_XML_MAXGROUNDSPEED).empty())
    {
       double local_max_gs_mps = ndComponent.attribute(STRING_XML_MAXGROUNDSPEED).as_double();
       if (local_max_gs_mps > 0.0)
       {
           m_max_gs_mps = local_max_gs_mps;
       }
    }
        if (!ndComponent.attribute(STRING_XML_MINGROUNDSPEED).empty())
    {
       double local_min_gs_mps = ndComponent.attribute(STRING_XML_MINGROUNDSPEED).as_double();
       if (local_min_gs_mps >= 0.0 && m_min_gs_mps < m_max_gs_mps)
       {
           m_min_gs_mps = local_min_gs_mps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_MAXVERTICALSPEED).empty())
    {
       double local_max_vs_mps = ndComponent.attribute(STRING_XML_MAXVERTICALSPEED).as_double();
       m_max_vs_mps = local_max_vs_mps;
    }
        if (!ndComponent.attribute(STRING_XML_MINVERTICALSPEED).empty())
    {
       double local_min_vs_mps = ndComponent.attribute(STRING_XML_MINVERTICALSPEED).as_double();
       if (local_min_vs_mps < m_max_vs_mps)
       {
           m_min_vs_mps = local_min_vs_mps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_MAXALTITUDE).empty())
    {
       double local_max_alt_m = ndComponent.attribute(STRING_XML_MAXALTITUDE).as_double();
       m_max_alt_m = local_max_alt_m; 
    }
        if (!ndComponent.attribute(STRING_XML_MINALTITUDE).empty())
    {
       double local_min_alt_m = ndComponent.attribute(STRING_XML_MINALTITUDE).as_double();
       if (local_min_alt_m < m_max_alt_m)
       {
           m_min_alt_m = local_min_alt_m;
       }
    }
    if (!ndComponent.attribute(STRING_XML_TRACKSTEP).empty())
    {
       double local_trk_step_deg = ndComponent.attribute(STRING_XML_TRACKSTEP).as_double();
       if (local_trk_step_deg > 0.0)
       {
           m_trk_step_deg = local_trk_step_deg;
       }
    }
    if (!ndComponent.attribute(STRING_XML_GROUNDSPEEDSTEP).empty())
    {
       double local_gs_step_mps = ndComponent.attribute(STRING_XML_GROUNDSPEEDSTEP).as_double();
       if (local_gs_step_mps > 0.0)
       {
           m_gs_step_mps = local_gs_step_mps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_VERTICALSPEEDSTEP).empty())
    {
       double local_vs_step_mps = ndComponent.attribute(STRING_XML_VERTICALSPEEDSTEP).as_double();
       if (local_vs_step_mps > 0.0)
       {
           m_vs_step_mps = local_vs_step_mps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_ALTITUDESTEP).empty())
    {
       double local_alt_step_m = ndComponent.attribute(STRING_XML_ALTITUDESTEP).as_double();
       if (local_alt_step_m > 0.0)
       {
           m_alt_step_m = local_alt_step_m;
       }
    }
    if (!ndComponent.attribute(STRING_XML_HORIZONTALACCELERATION).empty())
    {
       double local_horizontal_accel_mpsps = ndComponent.attribute(STRING_XML_HORIZONTALACCELERATION).as_double();
       if (local_horizontal_accel_mpsps >= 0.0)
       {
           m_horizontal_accel_mpsps = local_horizontal_accel_mpsps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_VERTICALACCELERATION).empty())
    {
       double local_vertical_accel_G = ndComponent.attribute(STRING_XML_VERTICALACCELERATION).as_double();
       if (local_vertical_accel_G >= 0.0)
       {
           m_vertical_accel_G = local_vertical_accel_G;
       }
    }
    if (!ndComponent.attribute(STRING_XML_TURNRATE).empty())
    {
       double local_turn_rate_degps = ndComponent.attribute(STRING_XML_TURNRATE).as_double();
       if (local_turn_rate_degps >= 0.0)
       {
           m_turn_rate_degps = local_turn_rate_degps;
       }
    }
    if (!ndComponent.attribute(STRING_XML_BANKANGLE).empty())
    {
       useBankAngle = true;
       double local_bank_angle_deg = ndComponent.attribute(STRING_XML_BANKANGLE).as_double();
       if (local_bank_angle_deg >= 0.0 && m_turn_rate_degps != 0.0)
       {
           m_bank_angle_deg = local_bank_angle_deg;
       }
    }
    if (!ndComponent.attribute(STRING_XML_VERTICALRATE).empty())
    {
       double local_vertical_rate_mps = ndComponent.attribute(STRING_XML_VERTICALRATE).as_double();
       if (local_vertical_rate_mps >= 0.0)
       {
           m_vertical_rate_mps = local_vertical_rate_mps;
       }
    }    
    if (!ndComponent.attribute(STRING_XML_RECOVERYSTABILITYTIME).empty())
    {
       double local_recovery_stability_time_s = ndComponent.attribute(STRING_XML_RECOVERYSTABILITYTIME).as_double();
       if (local_recovery_stability_time_s >= 0.0)
       {
           m_recovery_stability_time_s = local_recovery_stability_time_s;
       }
    }
    if (!ndComponent.attribute(STRING_XML_ISRECOVERYTRACK).empty())
    {
       bool local_recovery_trk_bool = ndComponent.attribute(STRING_XML_ISRECOVERYTRACK).as_bool();
       m_recovery_trk_bool = local_recovery_trk_bool;
    }
    if (!ndComponent.attribute(STRING_XML_ISRECOVERYGROUNDSPEED).empty())
    {
       bool local_recovery_gs_bool = ndComponent.attribute(STRING_XML_ISRECOVERYGROUNDSPEED).as_bool();
       m_recovery_gs_bool = local_recovery_gs_bool;
    }
    if (!ndComponent.attribute(STRING_XML_ISRECOVERYVERTICALSPEED).empty())
    {
       bool local_recovery_vs_bool = ndComponent.attribute(STRING_XML_ISRECOVERYVERTICALSPEED).as_bool();
       m_recovery_vs_bool = local_recovery_vs_bool;
    }
    if (!ndComponent.attribute(STRING_XML_ISRECOVERYALTITUDE).empty())
    {
       bool local_recovery_alt_bool = ndComponent.attribute(STRING_XML_ISRECOVERYALTITUDE).as_bool();
       m_recovery_alt_bool = local_recovery_alt_bool;
    }
    if (!ndComponent.attribute(STRING_XML_ISCOLLISIONAVOIDANCE).empty())
    {
       bool local_ca_bands_bool = ndComponent.attribute(STRING_XML_ISCOLLISIONAVOIDANCE).as_bool();
       m_ca_bands_bool = local_ca_bands_bool;
    }
    if (!ndComponent.attribute(STRING_XML_COLLISIONAVOIDANCEFACTOR).empty())
    {
       double local_ca_factor = ndComponent.attribute(STRING_XML_COLLISIONAVOIDANCEFACTOR).as_double();
       if (local_ca_factor > 0.0 && local_ca_factor <= 1.0)
       {
           m_ca_factor = local_ca_factor;
       }
    }
    if (!ndComponent.attribute(STRING_XML_HORIZONTALNMAC).empty())
    {
       double local_horizontal_nmac_m = ndComponent.attribute(STRING_XML_HORIZONTALNMAC).as_double();
       m_horizontal_nmac_m = local_horizontal_nmac_m;
    }
        if (!ndComponent.attribute(STRING_XML_MINHORIZONTALRECOVERY).empty())
    {
       double local_min_horizontal_recovery_m = ndComponent.attribute(STRING_XML_MINHORIZONTALRECOVERY).as_double();
       if (local_min_horizontal_recovery_m > 0.0 && local_min_horizontal_recovery_m >= m_horizontal_nmac_m)
       {
           m_min_horizontal_recovery_m = local_min_horizontal_recovery_m;
           m_DTHR_m = m_min_horizontal_recovery_m;
       }
    }
    if (!ndComponent.attribute(STRING_XML_VERTICALNMAC).empty())
    {
       double local_vertical_nmac_m = ndComponent.attribute(STRING_XML_VERTICALNMAC).as_double();
       m_vertical_nmac_m = local_vertical_nmac_m;
    }
        if (!ndComponent.attribute(STRING_XML_MINVERTICALRECOVERY).empty())
    {
       double local_min_vertical_recovery_m = ndComponent.attribute(STRING_XML_MINVERTICALRECOVERY).as_double();
       if (local_min_vertical_recovery_m > 0.0 && local_min_vertical_recovery_m >= m_vertical_nmac_m)
       {
           m_min_vertical_recovery_m = local_min_vertical_recovery_m;
           m_ZTHR_m = m_min_vertical_recovery_m;
       }
    }

    if (!ndComponent.attribute(STRING_XML_HORIZONTALCONTOURTHRESHOLD).empty())
    {
       double local_contour_thr_deg = ndComponent.attribute(STRING_XML_HORIZONTALCONTOURTHRESHOLD).as_double();
       if (local_contour_thr_deg >= 0.0 && local_contour_thr_deg <= 180.0)
           m_contour_thr_deg = local_contour_thr_deg;
    }
    if (!ndComponent.attribute(STRING_XML_RTCAALERTLEVELS).empty())
    {
        int local_alert_levels = ndComponent.attribute(STRING_XML_RTCAALERTLEVELS).as_int();
        if (local_alert_levels <=3 && local_alert_levels >0)
            m_RTCA_alert_levels = local_alert_levels;
    }
    if (!ndComponent.attribute(STRING_XML_TTHR).empty())
    {
        double local_TTHR_s = ndComponent.attribute(STRING_XML_TTHR).as_double();
        if (local_TTHR_s <= m_lookahead_time_s)
            m_TTHR_s = local_TTHR_s;
    }
    if (!ndComponent.attribute(STRING_XML_EARLYALERTTIME1).empty())
    {
        double local_early_alert_time_1_s = ndComponent.attribute(STRING_XML_EARLYALERTTIME1).as_double();
        if (local_early_alert_time_1_s >= m_lookahead_time_s)
            m_early_alert_time_1_s = local_early_alert_time_1_s;
    }
    if (!ndComponent.attribute(STRING_XML_ALERTTIME1).empty())
    {
        double local_alert_time_1_s = ndComponent.attribute(STRING_XML_ALERTTIME1).as_double();
        if (local_alert_time_1_s < m_early_alert_time_1_s)
            m_alert_time_1_s = local_alert_time_1_s;
    }
    if (!ndComponent.attribute(STRING_XML_EARLYALERTTIME2).empty())
    {
        double local_early_alert_time_2_s = ndComponent.attribute(STRING_XML_EARLYALERTTIME2).as_double();
        if (local_early_alert_time_2_s <= m_early_alert_time_1_s)
            m_early_alert_time_2_s = local_early_alert_time_2_s;
    }
    if (!ndComponent.attribute(STRING_XML_ALERTTIME2).empty())
    {
        double local_alert_time_2_s = ndComponent.attribute(STRING_XML_ALERTTIME2).as_double();
        if (local_alert_time_2_s < m_early_alert_time_2_s && local_alert_time_2_s <= m_alert_time_1_s)
            m_alert_time_2_s = local_alert_time_2_s;
    }
    if (!ndComponent.attribute(STRING_XML_EARLYALERTTIME3).empty())
    {
        double local_early_alert_time_3_s = ndComponent.attribute(STRING_XML_EARLYALERTTIME3).as_double();
        if (local_early_alert_time_3_s <= m_early_alert_time_2_s)
            m_early_alert_time_3_s = local_early_alert_time_3_s;
    }
    if (!ndComponent.attribute(STRING_XML_ALERTTIME3).empty())
    {
        double local_alert_time_3_s = ndComponent.attribute(STRING_XML_ALERTTIME3).as_double();
        if (local_alert_time_3_s < m_early_alert_time_3_s && local_alert_time_3_s <= m_alert_time_2_s)
            m_alert_time_3_s = local_alert_time_3_s;
    }
    if (!ndComponent.attribute(STRING_XML_HORIZONTALDETECTIONTYPE).empty())
    {
        std::string local_horizontal_detection_type = ndComponent.attribute(STRING_XML_HORIZONTALDETECTIONTYPE).as_string();
        if (local_horizontal_detection_type == "TAUMOD" || local_horizontal_detection_type == "TCPA" || local_horizontal_detection_type == "TEP")
        {
            m_horizontal_detection_type == local_horizontal_detection_type;
        }
    }
    m_daa.parameters.setLookaheadTime(m_lookahead_time_s, "s");
    m_daa.parameters.setLeftTrack(m_left_trk_deg, "deg");
    m_daa.parameters.setRightTrack(m_right_trk_deg, "deg");
    m_daa.parameters.setMaxGroundSpeed(m_max_gs_mps, "m/s");
    m_daa.parameters.setMinGroundSpeed(m_min_gs_mps, "m/s");
    m_daa.parameters.setMaxVerticalSpeed(m_max_vs_mps, "m/s");
    m_daa.parameters.setMinVerticalSpeed(m_min_vs_mps, "m/s");
    m_daa.parameters.setMaxAltitude(m_max_alt_m, "m");
    m_daa.parameters.setMinAltitude(m_min_alt_m, "m");
    m_daa.parameters.setTrackStep(m_trk_step_deg, "deg");
    m_daa.parameters.setGroundSpeedStep(m_gs_step_mps, "m/s");
    m_daa.parameters.setVerticalSpeedStep(m_vs_step_mps, "m/s");
    m_daa.parameters.setAltitudeStep(m_alt_step_m, "m");
    m_daa.parameters.setHorizontalAcceleration(m_horizontal_accel_mpsps, "m/s^2");
    m_daa.parameters.setVerticalAcceleration(m_vertical_accel_G, "G");
    m_daa.parameters.setTurnRate(m_turn_rate_degps, "deg/s");
    if (useBankAngle==true)
    {
        m_daa.parameters.setBankAngle(m_bank_angle_deg, "deg");
    }
    m_daa.parameters.setVerticalRate(m_vertical_rate_mps, "m/s");
    m_daa.parameters.setRecoveryStabilityTime(m_recovery_stability_time_s, "s");
    m_daa.parameters.setRecoveryTrackBands(m_recovery_trk_bool);
    m_daa.parameters.setRecoveryGroundSpeedBands(m_recovery_gs_bool);
    m_daa.parameters.setRecoveryVerticalSpeedBands(m_recovery_vs_bool);
    m_daa.parameters.setRecoveryAltitudeBands(m_recovery_alt_bool);
    m_daa.parameters.setCollisionAvoidanceBands(m_ca_bands_bool);
    m_daa.parameters.setCollisionAvoidanceBandsFactor(m_ca_factor);
    m_daa.parameters.setHorizontalNMAC(m_horizontal_nmac_m, "m"); 
    m_daa.parameters.setMinHorizontalRecovery(m_min_horizontal_recovery_m, "m");
    m_daa.parameters.setVerticalNMAC(m_vertical_nmac_m, "m");
    m_daa.parameters.setMinVerticalRecovery(m_min_vertical_recovery_m, "m");
    m_daa.parameters.setHorizontalContourThreshold(m_contour_thr_deg, "deg");
    larcfm::WCVTable alert_level;
    alert_level.setDTHR(m_DTHR_m,"m");
    alert_level.setZTHR(m_ZTHR_m,"m");
    alert_level.setTTHR(m_TTHR_s,"s");
    alert_level.setTCOA(0,"s");
    std::unique_ptr<larcfm::Detection3D> cd = makeDetectionPtr(m_horizontal_detection_type,alert_level);
    larcfm::Detection3D* raw_ptr;
    raw_ptr = cd.get();
    m_daa.parameters.alertor.clear();
    m_daa.parameters.alertor.setConflictAlertLevel(2);
    if (m_RTCA_alert_levels == 3)
    {
        m_daa.parameters.alertor.addLevel(larcfm::AlertThresholds(raw_ptr,m_alert_time_1_s,m_early_alert_time_1_s,larcfm::BandsRegion::FAR));
        m_daa.parameters.alertor.setConflictAlertLevel(1);
    }
    else
    {
        m_daa.parameters.alertor.addLevel(larcfm::AlertThresholds(raw_ptr,m_alert_time_1_s,m_early_alert_time_1_s,larcfm::BandsRegion::NONE));
    }
    if (m_RTCA_alert_levels == 1)
    {
        m_daa.parameters.alertor.addLevel(larcfm::AlertThresholds(raw_ptr,m_alert_time_2_s,m_early_alert_time_2_s,larcfm::BandsRegion::NONE));
        m_daa.parameters.alertor.setConflictAlertLevel(3);
    }    
    else
    {
        m_daa.parameters.alertor.addLevel(larcfm::AlertThresholds(raw_ptr,m_alert_time_2_s,m_early_alert_time_2_s,larcfm::BandsRegion::MID));
    }
    m_daa.parameters.alertor.addLevel(larcfm::AlertThresholds(raw_ptr,m_alert_time_3_s,m_early_alert_time_3_s,larcfm::BandsRegion::NEAR));
    raw_ptr = nullptr;
    addSubscriptionAddress(afrl::cmasi::AirVehicleState::Subscription);
    addSubscriptionAddress(uxas::messages::uxnative::StartupComplete::Subscription);
    std::cout << "Successfully subscribed to AirVehicleState from DAIDALUS_WCV_Detection." << std::endl;
    std::cout << "Successfully subscribed to the StartupComplete from DAIDALUS_WCV_Detection." <<std::endl;
    
    return (isSuccess);
}

bool DAIDALUS_WCV_Detection::initialize()
{
    // perform any required initialization before the service is started

    
    //std::cout << "*** INITIALIZING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
}

bool DAIDALUS_WCV_Detection::start() 
{
    // perform any actions required at the time the service starts
    //std::cout << "*** STARTING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << m_workDirectoryName << "] *** " << std::endl;
    
    return (true);
};

bool DAIDALUS_WCV_Detection::terminate()
{
    // perform any action required during service termination, before destructor is called.
    std::cout << "*** TERMINATING:: Service[" << s_typeName() << "] Service Id[" << m_serviceId << "] with working directory [" << 
            m_workDirectoryName << "] *** " << std::endl;    
    return (true);
}

bool DAIDALUS_WCV_Detection::processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage)
{
    if (afrl::cmasi::isAirVehicleState(receivedLmcpMessage->m_object))
    {
        static bool bFirst = true;
        
        if (bFirst)
        {
            std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> DetectionConfiguration = std::make_shared<larcfm::DAIDALUS::DAIDALUSConfiguration>();
            DetectionConfiguration->setEntityId(m_entityId);
            DetectionConfiguration->setLookAheadTime(m_daa.parameters.getLookaheadTime("s"));
            DetectionConfiguration->setLeftTrack(m_daa.parameters.getLeftTrack("deg"));
            DetectionConfiguration->setRightTrack(m_daa.parameters.getRightTrack("deg"));
            DetectionConfiguration->setMaxGroundSpeed(m_daa.parameters.getMaxGroundSpeed("m/s"));
            DetectionConfiguration->setMinGroundSpeed(m_daa.parameters.getMinGroundSpeed("m/s"));
            DetectionConfiguration->setMaxVerticalSpeed(m_daa.parameters.getMaxVerticalSpeed("m/s"));
            DetectionConfiguration->setMinVerticalSpeed(m_daa.parameters.getMinVerticalSpeed("m/s"));
            DetectionConfiguration->setMaxAltitude(m_daa.parameters.getMaxAltitude("m"));
            DetectionConfiguration->setMinAltitude(m_daa.parameters.getMinAltitude("m"));
            DetectionConfiguration->setTrackStep(m_daa.parameters.getTrackStep("deg"));
            DetectionConfiguration->setGroundSpeedStep(m_daa.parameters.getGroundSpeedStep("m/s"));
            DetectionConfiguration->setVerticalSpeedStep(m_daa.parameters.getVerticalSpeedStep("m/s"));
            DetectionConfiguration->setAltitudeStep(m_daa.parameters.getAltitudeStep("m"));
            DetectionConfiguration->setHorizontalAcceleration(m_daa.parameters.getHorizontalAcceleration("m/s^2"));
            DetectionConfiguration->setVerticalAcceleration(m_daa.parameters.getVerticalAcceleration("G"));
            DetectionConfiguration->setTurnRate(m_daa.parameters.getTurnRate("deg/s"));
            DetectionConfiguration->setBankAngle(m_daa.parameters.getBankAngle("deg"));
            DetectionConfiguration->setVerticalRate(m_daa.parameters.getVerticalRate("m/s"));
            DetectionConfiguration->setRecoveryStabilityTime(m_daa.parameters.getRecoveryStabilityTime("s"));
            DetectionConfiguration->setIsRecoveryTrackBands(m_daa.parameters.isEnabledRecoveryTrackBands());
            DetectionConfiguration->setIsRecoveryGroundSpeedBands(m_daa.parameters.isEnabledRecoveryGroundSpeedBands());
            DetectionConfiguration->setIsRecoveryVerticalSpeedBands(m_daa.parameters.isEnabledRecoveryVerticalSpeedBands());
            DetectionConfiguration->setIsRecoveryAltitudeBands(m_daa.parameters.isEnabledRecoveryAltitudeBands());
            DetectionConfiguration->setIsCollisionAvoidanceBands(m_daa.parameters.isEnabledCollisionAvoidanceBands());
            DetectionConfiguration->setHorizontalNMAC(m_daa.parameters.getHorizontalNMAC("m"));
            DetectionConfiguration->setMinHorizontalRecovery(m_daa.parameters.getMinHorizontalRecovery("m"));
            DetectionConfiguration->setVerticalNMAC(m_daa.parameters.getVerticalNMAC("m"));
            DetectionConfiguration->setMinVerticalRecovery(m_daa.parameters.getMinVerticalRecovery("m"));
            DetectionConfiguration->setHorizontalContourThreshold(m_daa.parameters.getHorizontalContourThreshold("m"));
            DetectionConfiguration->setDTHR(m_DTHR_m);
            DetectionConfiguration->setZTHR(m_ZTHR_m);
            DetectionConfiguration->setTTHR(m_TTHR_s);
            DetectionConfiguration->setRTCAAlertLevels(m_RTCA_alert_levels);
            DetectionConfiguration->setAlertTime1(m_alert_time_1_s);
            DetectionConfiguration->setEarlyAlertTime1(m_early_alert_time_1_s);
            DetectionConfiguration->setAlertTime2(m_alert_time_2_s);
            DetectionConfiguration->setEarlyAlertTime2(m_early_alert_time_2_s);
            DetectionConfiguration->setAlertTime3(m_alert_time_3_s);
            DetectionConfiguration->setEarlyAlertTime3(m_early_alert_time_3_s);
            DetectionConfiguration->setHorizontalDetectionType(m_horizontal_detection_type);
            sendSharedLmcpObjectBroadcastMessage(DetectionConfiguration);
            bFirst = false;
        }
        
        //receive message
        std::shared_ptr<afrl::cmasi::AirVehicleState> airVehicleState = std::static_pointer_cast<afrl::cmasi::AirVehicleState> (receivedLmcpMessage->m_object);
        //Screen output for debugging 
        //std::cout << "DAIDALUS_WCV_Detection has received an AirVehicleState at " << airVehicleState->getTime() <<" ms--from Entity " << 
        //        airVehicleState->getID() << std::endl; 
        //handle message
        std::unordered_map<int64_t, double> detectedViolations;        
        //add air vehicle message state to the Daidalus Object
        MydaidalusPackage vehicleInfo;  
        vehicleInfo.m_daidalusPosition = larcfm::Position::makeLatLonAlt(airVehicleState->getLocation()->getLatitude(), "deg",
                                         airVehicleState->getLocation()->getLongitude(), "deg", airVehicleState->getLocation()->getAltitude(), "m");      
        float u_mps = airVehicleState->getU();
        float v_mps = airVehicleState->getV();
        float w_mps = airVehicleState->getW();
        float Phi_deg = airVehicleState->getRoll();
        float Theta_deg = airVehicleState->getPitch();
        float Psi_deg = airVehicleState->getHeading();  //currently does not account for wind.
        double velocityX_mps, velocityY_mps, velocityZ_mps;
        makeVelocityXYZ(u_mps, v_mps, w_mps, n_Const::c_Convert::toRadians(Phi_deg), n_Const::c_Convert::toRadians(Theta_deg), 
                n_Const::c_Convert::toRadians(Psi_deg), velocityX_mps, velocityY_mps, velocityZ_mps);
        // DAIDALUS expects ENUp reference while UxAS internally used NEDown--covert UxAS velocities to DAIDALUS velocities
        double daidalusVelocityZ_mps = -velocityZ_mps;    
        double daidalusVelocityX_mps = velocityY_mps;
        double daidalusVelocityY_mps = velocityX_mps;
        vehicleInfo.m_daidalusVelocity = larcfm::Velocity::makeVxyz(daidalusVelocityX_mps, daidalusVelocityY_mps, "m/s", daidalusVelocityZ_mps, "m/s");
        vehicleInfo.m_daidalusTime_s = airVehicleState->getTime()*MILLISECONDTOSECOND; // conversion from UxAS representation of time in milliseconds to DAIDALUS representation fo time in seconds
        vehicleInfo.latitude_deg = airVehicleState->getLocation()->getLatitude();
        vehicleInfo.longitude_deg = airVehicleState->getLocation()->getLongitude();
        m_daidalusVehicleInfo[airVehicleState->getID()] = vehicleInfo;
        // Conditional check for appropriateness off a well clear violation check-- 2 known vehicle states including the ownship
        if (m_daidalusVehicleInfo.size()>1 && m_daidalusVehicleInfo.count(m_entityId)>0)    
        { 
            m_daa.setOwnshipState(std::to_string(m_entityId), m_daidalusVehicleInfo[m_entityId].m_daidalusPosition, 
                m_daidalusVehicleInfo[m_entityId].m_daidalusVelocity, m_daidalusVehicleInfo[m_entityId].m_daidalusTime_s); //set DAIDALUS object ownship state
            for (const auto& vehiclePackagedInfo : m_daidalusVehicleInfo)
            {
                //add intruder traffic state to DAIDALUS object
                if ((vehiclePackagedInfo.first!=m_entityId) && 
                        (std::abs(m_daidalusVehicleInfo[m_entityId].m_daidalusTime_s - vehiclePackagedInfo.second.m_daidalusTime_s) <= m_staleness_time_s)) //--TODO add staleness check to this statement or put check on outer most if
                    {
                        m_daa.addTrafficState(std::to_string(vehiclePackagedInfo.first), vehiclePackagedInfo.second.m_daidalusPosition, 
                                vehiclePackagedInfo.second.m_daidalusVelocity, vehiclePackagedInfo.second.m_daidalusTime_s);
                        //Screen output for debugging
                        //std::cout << "Added Entity " << it_intruderId->first << " as an intruder to Entity " << m_entityId << std::endl; --TODO delete before commiting to repository
                    }
            }
            //Following conditional always executes.  Necessary if full state vehicle information is not passed along to DAIDALUS
            if (m_daa.numberOfAircraft()>1) //Perform well_clear violation check if DAIDALUS object contains ownship and at least one intruder traffic state
            {
                // Determine the time to violation of the wellclear volume of the ownship by each intruder aircaft
                for (int intruderIndex = 1; intruderIndex<=m_daa.numberOfAircraft()-1; ++intruderIndex)
                {
                    double timeToViolation_s = m_daa.timeToViolation(intruderIndex);
                    if (timeToViolation_s != PINFINITY && timeToViolation_s != NaN)
                    { 
                        detectedViolations[std::stoi(m_daa.getAircraftState(intruderIndex).getId(),nullptr,10)] = timeToViolation_s;
                        //std::cout << "Collision with intruder " <<m_daa.getAircraftState(intruderIndex).getId() << " in " << timeToViolation << " seconds" << std::endl;--TODO delete
                    }
                }
                //send out response
                //std::cout << "Number of aircraft according to DAIDALUS: " << m_daa.numberOfAircraft() << std::endl;--TODO delete
                //if (!detectedViolations.empty())    //compute conflict bands and compose violation message only if violations are detected
                {
                    //Create DAIDALUS bands object and compute conflict/peripheral bands
                    larcfm::KinematicMultiBands m_daa_bands(m_daa.parameters);
                    m_daa.kinematicMultiBands(m_daa_bands);
                    std::shared_ptr<larcfm::DAIDALUS::WellClearViolationIntervals>  nogo_ptr = 
                            std::make_shared<larcfm::DAIDALUS::WellClearViolationIntervals>();  //Compose violations message
                    larcfm::TrafficState daa_own = m_daa.getOwnshipState();
                    for (auto itViolations = detectedViolations.cbegin(); itViolations !=detectedViolations.cend(); itViolations++)
                    {
                        nogo_ptr->getEntityList().push_back(itViolations->first);
                        nogo_ptr->getTimeToViolationList().push_back(itViolations->second);
                    }
                    nogo_ptr->setEntityId(m_entityId);  //Ownship Id
                    nogo_ptr->setCurrentHeading(daa_own.track("deg"));  //DAIDALUS current heading--0deg = TrueNorth Currently does not account for wind
                    nogo_ptr->setCurrentGoundSpeed(daa_own.groundSpeed("m/s")); //DAIDALUS current ground speed--does not account for wind
                    nogo_ptr->setCurrentVerticalSpeed(daa_own.verticalSpeed("m/s"));    //DAIDALUS current vertical speed--does not account for wind
                    nogo_ptr->setCurrentAltitude(daa_own.altitude("m"));    //DAIDALUS current altitude
                    nogo_ptr->setCurrentLatitude(m_daidalusVehicleInfo[m_entityId].latitude_deg);    //Current ownship latitude
                    nogo_ptr->setCurrentLongitude(m_daidalusVehicleInfo[m_entityId].longitude_deg);  //Current ownship longitude
                    nogo_ptr->setCurrentTime(m_daidalusVehicleInfo[m_entityId].m_daidalusTime_s);
                    
                    for (int ii = 0; ii < m_daa_bands.trackLength(); ii++)  //ground track bands
                    {
                        std::unique_ptr<larcfm::DAIDALUS::GroundHeadingInterval> pTempPtr (new larcfm::DAIDALUS::GroundHeadingInterval);
                        larcfm::Interval iv = m_daa_bands.track(ii,"deg");
                        double lower_trk_deg = iv.low; //lower bound on interval
                        double upper_trk_deg = iv.up;   //upper bound on interval
                        larcfm::BandsRegion::Region regionType = m_daa_bands.trackRegion(ii);   //region classification for above interval
                        //Currently only considering conflict bands classified as NEAR, MID, or FAR
                        if (regionType == larcfm::BandsRegion::FAR || regionType == larcfm::BandsRegion::MID || regionType == larcfm::BandsRegion::NEAR)
                        {
                            larcfm::DAIDALUS::BandsRegion::BandsRegion temp_regionType;
                            if (regionType == larcfm::BandsRegion::FAR)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::FAR;
                            }
                            else if (regionType == larcfm::BandsRegion::MID)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::MID;
                            }
                            else
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::NEAR;
                            }
                            pTempPtr->getGroundHeadings()[0] = lower_trk_deg;
                            pTempPtr->getGroundHeadings()[1] = upper_trk_deg;
                            nogo_ptr->getWCVGroundHeadingIntervals().push_back(pTempPtr.release());
                            nogo_ptr->getWCVGroundHeadingRegions().push_back(temp_regionType);
                        }
                        else if (regionType == larcfm::BandsRegion::RECOVERY)
                        {
                            std::unique_ptr<larcfm::DAIDALUS::GroundHeadingRecoveryInterval> pRecoveryPtr (new larcfm::DAIDALUS::GroundHeadingRecoveryInterval);
                            pRecoveryPtr->getRecoveryGroundHeadings()[0] = lower_trk_deg;
                            pRecoveryPtr->getRecoveryGroundHeadings()[1] = upper_trk_deg;
                            nogo_ptr->getRecoveryGroundHeadingIntervals().push_back(pRecoveryPtr.release());
                        }
                        
                    }
                    
                    for (int ii = 0; ii < m_daa_bands.groundSpeedLength();++ii) //ground speed bands
                    {
                        std::unique_ptr<larcfm::DAIDALUS::GroundSpeedInterval> pTempPtr (new larcfm::DAIDALUS::GroundSpeedInterval);
                        larcfm::Interval iv = m_daa_bands.groundSpeed(ii, "mps");
                        double lower_gs_mps = iv.low;
                        double upper_gs_mps =iv.up;
                        larcfm::BandsRegion::Region regionType = m_daa_bands.groundSpeedRegion(ii);
                        if (regionType == larcfm::BandsRegion::FAR || regionType == larcfm::BandsRegion::MID || regionType == larcfm::BandsRegion::NEAR)
                        {
                            larcfm::DAIDALUS::BandsRegion::BandsRegion temp_regionType;
                            if (regionType == larcfm::BandsRegion::FAR)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::FAR;
                            }
                            else if (regionType == larcfm::BandsRegion::MID)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::MID;
                            }
                            else
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::NEAR;
                            }
                            pTempPtr->getGroundSpeeds()[0] = lower_gs_mps;
                            pTempPtr->getGroundSpeeds()[1] = upper_gs_mps;
                            nogo_ptr->getWCVGroundSpeedIntervals().push_back(pTempPtr.release());
                            nogo_ptr->getWCVGroundSpeedRegions().push_back(temp_regionType);
                        }
                        else if (regionType == larcfm::BandsRegion::RECOVERY)
                        {
                            std::unique_ptr<larcfm::DAIDALUS::GroundSpeedRecoveryInterval> pRecoveryPtr (new larcfm::DAIDALUS::GroundSpeedRecoveryInterval);
                            pRecoveryPtr->getRecoveryGroundSpeeds()[0] = lower_gs_mps;
                            pRecoveryPtr->getRecoveryGroundSpeeds()[1] = upper_gs_mps;
                            nogo_ptr->getRecoveryGroundSpeedIntervals().push_back(pRecoveryPtr.release());
                        }
                        
                    }
                    
                    for (int ii =0; ii < m_daa_bands.verticalSpeedLength();++ii)    //vertical speed bands
                    {
                        std::unique_ptr<larcfm::DAIDALUS::VerticalSpeedInterval> pTempPtr (new larcfm::DAIDALUS::VerticalSpeedInterval);
                        larcfm::Interval iv = m_daa_bands.verticalSpeed(ii, "mps");
                        double lower_vs_mps = iv.low;
                        double upper_vs_mps = iv.up;
                        larcfm::BandsRegion::Region regionType = m_daa_bands.verticalSpeedRegion(ii);
                        if (regionType == larcfm::BandsRegion::FAR || regionType == larcfm::BandsRegion::MID || regionType == larcfm::BandsRegion::NEAR)
                        {
                            larcfm::DAIDALUS::BandsRegion::BandsRegion temp_regionType;
                            if (regionType == larcfm::BandsRegion::FAR)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::FAR;
                            }
                            else if (regionType == larcfm::BandsRegion::MID)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::MID;
                            }
                            else
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::NEAR;
                            }
                            pTempPtr->getVerticalSpeeds()[0] = lower_vs_mps;
                            pTempPtr->getVerticalSpeeds()[1] = upper_vs_mps;
                            nogo_ptr->getWCVVerticalSpeedIntervals().push_back(pTempPtr.release());
                            nogo_ptr->getWCVVerticalSpeedRegions().push_back(temp_regionType);
                        }
                        else if (regionType == larcfm::BandsRegion::RECOVERY)
                        {
                            std::unique_ptr<larcfm::DAIDALUS::VerticalSpeedRecoveryInterval> pRecoveryPtr (new larcfm::DAIDALUS::VerticalSpeedRecoveryInterval);
                            pRecoveryPtr->getRecoveryVerticalSpeed()[0] = lower_vs_mps;
                            pRecoveryPtr->getRecoveryVerticalSpeed()[1] = upper_vs_mps;
                            nogo_ptr->getRecoveryVerticalSpeedIntervals().push_back(pRecoveryPtr.release());
                        }
                        
                    }
                    
                    for (int ii = 0; ii < m_daa_bands.altitudeLength(); ++ii)   //altitude bands
                    {
                        std::unique_ptr<larcfm::DAIDALUS::AltitudeInterval> pTempPtr (new larcfm::DAIDALUS::AltitudeInterval);
                        larcfm::Interval iv = m_daa_bands.altitude(ii, "m");
                        double lower_alt_m = iv.low;
                        double upper_alt_m = iv.up;
                        larcfm::BandsRegion::Region regionType = m_daa_bands.altitudeRegion(ii);
                        if (regionType == larcfm::BandsRegion::FAR || regionType == larcfm::BandsRegion::MID || regionType == larcfm::BandsRegion::NEAR)
                        {
                            larcfm::DAIDALUS::BandsRegion::BandsRegion temp_regionType;
                            if (regionType == larcfm::BandsRegion::FAR)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::FAR;
                            }
                            else if (regionType == larcfm::BandsRegion::MID)
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::MID;
                            }
                            else
                            {
                                temp_regionType = larcfm::DAIDALUS::BandsRegion::NEAR;
                            }
                            pTempPtr->getAltitude()[0] = lower_alt_m;
                            pTempPtr->getAltitude()[1] = upper_alt_m;
                            nogo_ptr->getWCVAlitudeIntervals().push_back(pTempPtr.release());
                            nogo_ptr->getWCVAltitudeRegions().push_back(temp_regionType);
                        }
                        else if (regionType == larcfm::BandsRegion::RECOVERY)
                        {
                            std::unique_ptr<larcfm::DAIDALUS::AltitudeRecoveryInterval> pRecoveryPtr (new larcfm::DAIDALUS::AltitudeRecoveryInterval);
                            pRecoveryPtr->getRecoveryAltitude()[0] = lower_alt_m;
                            pRecoveryPtr->getRecoveryAltitude()[1] = upper_alt_m;
                            nogo_ptr->getRecoveryAltitudeIntervals().push_back(pRecoveryPtr.release());
                        }
                        
                    }
                    
                    //Screen output for debugging --TODO: DELETE LOOP AND SCREEN OUTPUT
                    for (auto itViolations = detectedViolations.cbegin(); itViolations != detectedViolations.cend(); itViolations++)
                    {
                        if (itViolations->second <= 25)
                        std::cout << "Entity " << m_entityId << "'s well clear volume will be violated by Entity " << itViolations->first << " in " 
                                << itViolations->second <<" seconds!!" << std::endl<<std::endl; //--TODO delete
                       // std::cout << m_nogo_trk_deg <<  std::endl;--TODO delete
                    }
                    sendSharedLmcpObjectBroadcastMessage(nogo_ptr);
                }
                //else //Screen output for debugging --
                {
                    //std::cout << "No violation of well clear volume detected :^)" << std::endl; //--TODO delete
                    //--TODO figure out what the appropriate action should be when there is no violation detected
                }
            }
        }
    }
    //Compose and send DAIDALUS configuration message
    if (uxas::messages::uxnative::isStartupComplete(receivedLmcpMessage->m_object))
    {
        /*std::shared_ptr<larcfm::DAIDALUS::DAIDALUSConfiguration> DetectionConfiguration = std::make_shared<larcfm::DAIDALUS::DAIDALUSConfiguration>();
        DetectionConfiguration->setEntityId(m_entityId);
        DetectionConfiguration->setLookAheadTime(m_daa.parameters.getLookaheadTime("s"));
        DetectionConfiguration->setLeftTrack(m_daa.parameters.getLeftTrack("deg"));
        DetectionConfiguration->setRightTrack(m_daa.parameters.getRightTrack("deg"));
        DetectionConfiguration->setMaxGroundSpeed(m_daa.parameters.getMaxGroundSpeed("mps"));
        DetectionConfiguration->setMinGroundSpeed(m_daa.parameters.getMinGroundSpeed("mps"));
        DetectionConfiguration->setMaxVerticalSpeed(m_daa.parameters.getMaxVerticalSpeed("mps"));
        DetectionConfiguration->setMinVerticalSpeed(m_daa.parameters.getMinVerticalSpeed("mps"));
        DetectionConfiguration->setMaxAltitude(m_daa.parameters.getMaxAltitude("m"));
        DetectionConfiguration->setMinAltitude(m_daa.parameters.getMinAltitude("m"));
        DetectionConfiguration->setTrackStep(m_daa.parameters.getTrackStep("deg"));
        DetectionConfiguration->setGroundSpeedStep(m_daa.parameters.getGroundSpeedStep("mps"));
        DetectionConfiguration->setVerticalSpeedStep(m_daa.parameters.getVerticalSpeedStep("mps"));
        DetectionConfiguration->setAltitudeStep(m_daa.parameters.getAltitudeStep("m"));
        DetectionConfiguration->setHorizontalAcceleration(m_daa.parameters.getHorizontalAcceleration("m/s^2"));
        DetectionConfiguration->setVerticalAcceleration(m_daa.parameters.getVerticalAcceleration("G"));
        DetectionConfiguration->setTurnRate(m_daa.parameters.getTurnRate("deg/s"));
        DetectionConfiguration->setBankAngle(m_daa.parameters.getBankAngle("deg"));
        DetectionConfiguration->setVerticalRate(m_daa.parameters.getVerticalRate("mps"));
        DetectionConfiguration->setRecoveryStabilityTime(m_daa.parameters.getRecoveryStabilityTime("s"));
        DetectionConfiguration->setIsRecoveryTrackBands(m_daa.parameters.isEnabledRecoveryTrackBands());
        DetectionConfiguration->setIsRecoveryGroundSpeedBands(m_daa.parameters.isEnabledRecoveryGroundSpeedBands());
        DetectionConfiguration->setIsRecoveryVerticalSpeedBands(m_daa.parameters.isEnabledRecoveryVerticalSpeedBands());
        DetectionConfiguration->setIsRecoveryAltitudeBands(m_daa.parameters.isEnabledRecoveryAltitudeBands());
        DetectionConfiguration->setIsCollisionAvoidanceBands(m_daa.parameters.isEnabledCollisionAvoidanceBands());
        DetectionConfiguration->setHorizontalNMAC(m_daa.parameters.getHorizontalNMAC("m"));
        DetectionConfiguration->setMinHorizontalRecovery(m_daa.parameters.getMinHorizontalRecovery("m"));
        DetectionConfiguration->setVerticalNMAC(m_daa.parameters.getVerticalNMAC("m"));
        DetectionConfiguration->setMinVerticalRecovery(m_daa.parameters.getMinVerticalRecovery("m"));
        DetectionConfiguration->setHorizontalContourThreshold(m_daa.parameters.getHorizontalContourThreshold("m"));
        DetectionConfiguration->setDTHR(m_DTHR_m);
        DetectionConfiguration->setZTHR(m_ZTHR_m);
        DetectionConfiguration->setTTHR(m_TTHR_s);
        DetectionConfiguration->setRTCAAlertLevels(m_RTCA_alert_levels);
        DetectionConfiguration->setAlertTime1(m_alert_time_1_s);
        DetectionConfiguration->setEarlyAlertTime1(m_early_alert_time_1_s);
        DetectionConfiguration->setAlertTime2(m_alert_time_2_s);
        DetectionConfiguration->setEarlyAlertTime2(m_early_alert_time_2_s);
        DetectionConfiguration->setAlertTime3(m_alert_time_3_s);
        DetectionConfiguration->setEarlyAlertTime3(m_early_alert_time_3_s);
        DetectionConfiguration->setHorizontalDetectionType(m_horizontal_detection_type);
        sendSharedLmcpObjectBroadcastMessage(DetectionConfiguration);   */
    }
    return false;
}

} //namespace service
} //namespace uxas
