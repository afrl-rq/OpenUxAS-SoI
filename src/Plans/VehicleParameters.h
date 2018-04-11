// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION IS RELEASED "AS IS." THE
//    U.S.GOVERNMENT MAKES NO WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, CONCERNING
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION, INCLUDING, WITHOUT LIMITATION,
//    ANY WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
//    WILL THE U.S. GOVERNMENT BE LIABLE FOR ANY DAMAGES, INCLUDING ANY LOST PROFITS,
//    LOST SAVINGS OR OTHER INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE,
//    OR INABILITY TO USE, THIS SOFTWARE OR ANY ACCOMPANYING DOCUMENTATION, EVEN IF
//    INFORMED IN ADVANCE OF THE POSSIBILITY OF SUCH DAMAGES.
//
// Vehicle.h: interface for the CVehicle class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(VEHICLE_PARAMETERS_H__301D6590_12D0_4F65_8B3F_89B507DCC41F__INCLUDED_)
#define VEHICLE_PARAMETERS_H__301D6590_12D0_4F65_8B3F_89B507DCC41F__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

#include "Polygon.h"

//#include "IncludeLMCP.h"

#include "afrl/cmasi/AirVehicleConfiguration.h"
#include "afrl/vehicles/SurfaceVehicleConfiguration.h"
#include "afrl/vehicles/GroundVehicleConfiguration.h"
#include "afrl/cmasi/WavelengthBand.h"

#include <iostream>

namespace n_FrameworkLib
{
    //! sensor footprint parameters

    class CSensorFootprint
    {
    public:

        CSensorFootprint() :
        m_horizantalToLeadingEdge_m(0.0),
        m_horizantalToTrailingEdge_m(0.0),
        m_horizantalToCenter_m(0.0),
        m_widthCenter_m(0.0),
        m_slantRangeToCenter_m(0.0)
        { };

        ~CSensorFootprint() { };

        CSensorFootprint(const CSensorFootprint& rhs) {
            operator =(rhs);
        };

        void operator =(const CSensorFootprint& rhs) {
            dGetHorizantalToLeadingEdge_m() = rhs.dGetHorizantalToLeadingEdge_m();
            dGetHorizantalToTrailingEdge_m() = rhs.dGetHorizantalToTrailingEdge_m();
            dGetHorizantalToCenter_m() = rhs.dGetHorizantalToCenter_m();
            dGetWidthCenter_m() = rhs.dGetWidthCenter_m();
            dGetSlantRangeToCenter_m() = rhs.dGetSlantRangeToCenter_m();
        }

    public:

        double& dGetHorizantalToLeadingEdge_m() {
            return (m_horizantalToLeadingEdge_m);
        };

        const double& dGetHorizantalToLeadingEdge_m()const {
            return (m_horizantalToLeadingEdge_m);
        };

        double& dGetHorizantalToTrailingEdge_m() {
            return (m_horizantalToTrailingEdge_m);
        };

        const double& dGetHorizantalToTrailingEdge_m()const {
            return (m_horizantalToTrailingEdge_m);
        };

        double& dGetHorizantalToCenter_m() {
            return (m_horizantalToCenter_m);
        };

        const double& dGetHorizantalToCenter_m()const {
            return (m_horizantalToCenter_m);
        };

        double& dGetWidthCenter_m() {
            return (m_widthCenter_m);
        };

        const double& dGetWidthCenter_m()const {
            return (m_widthCenter_m);
        };
        
        const double& dGetSlantRangeToCenter_m()const {
            return (m_slantRangeToCenter_m);
        };

        double& dGetSlantRangeToCenter_m() {
            return (m_slantRangeToCenter_m);
        };

    protected:
        double m_horizantalToLeadingEdge_m;
        double m_horizantalToTrailingEdge_m;
        double m_horizantalToCenter_m;
        double m_widthCenter_m;
        double m_slantRangeToCenter_m;
    };

    //! Stores settings required to obtain a particular ground sample distance

    class CGSD_Settings
    {
    public: //typedefs
        typedef afrl::cmasi::WavelengthBand::WavelengthBand WAVELENGTHBAND_t;

    public:

        CGSD_Settings();

        CGSD_Settings(const int iPayloadID_Sensor, const int iPayloadID_Gimbal, const double& dHorizantalFOV_rad, const double& altitude_m,
                const double& dGimbalElevation_rad,
                const double& dAspectRatio,
                const double& gsd_m,
                const WAVELENGTHBAND_t& wbWaveLengthBand = afrl::cmasi::WavelengthBand::AllAny);

    public:

        CGSD_Settings(const CGSD_Settings& rhs);

        void operator =(const CGSD_Settings& rhs);

    public:
        
        void CalculateFootprint(const bool& dRecalculate=false);

        double dGetHorizantalToLeadingEdge_m() {
            CalculateFootprint();
            return (sensorGetFootprint().dGetHorizantalToLeadingEdge_m());
        };
        double dGetHorizantalToTrailingEdge_m() {
            CalculateFootprint();
            return (sensorGetFootprint().dGetHorizantalToTrailingEdge_m());
        };
        double dGetHorizantalToCenter_m() {
            CalculateFootprint();
            return (sensorGetFootprint().dGetHorizantalToCenter_m());
        };
        double dGetWidthCenter_m() {
            CalculateFootprint();
            return (sensorGetFootprint().dGetWidthCenter_m());
        };
        double dGetSlantRangeToCenter_m() {
            CalculateFootprint();
            return (sensorGetFootprint().dGetSlantRangeToCenter_m());
        };
        
    public:

        int& iGetPayloadID_Sensor() {
            return (m_iPayloadID_Sensor);
        };

        const int& iGetPayloadID_Sensor()const {
            return (m_iPayloadID_Sensor);
        };

        int& iGetPayloadID_Gimbal() {
            return (m_iPayloadID_Gimbal);
        };

        const int& iGetPayloadID_Gimbal()const {
            return (m_iPayloadID_Gimbal);
        };

        double& dGetHorizantalFOV_rad() {
            return (m_dHorizantalFOV_rad);
        };

        const double& dGetHorizantalFOV_rad()const {
            return (m_dHorizantalFOV_rad);
        };

        double& dGetAltitude_m() {
            return (m_altitude_m);
        };

        const double& dGetAltitude_m()const {
            return (m_altitude_m);
        };

        double& dGetGimbalElevation_rad() {
            return (m_dGimbalElevation_rad);
        };

        const double& dGetGimbalElevation_rad()const {
            return (m_dGimbalElevation_rad);
        };

        double& dGetAspectRatio() {
            return (m_dAspectRatio);
        };

        const double& dGetAspectRatio()const {
            return (m_dAspectRatio);
        };

        WAVELENGTHBAND_t& wbGetWaveLengthBand() {
            return (m_wbWaveLengthBand);
        };

        const WAVELENGTHBAND_t& wbGetWaveLengthBand()const {
            return (m_wbWaveLengthBand);
        };

        CSensorFootprint& sensorGetFootprint() {
            return (m_sensorFootprint);
        };

        const CSensorFootprint& sensorGetFootprint()const {
            return (m_sensorFootprint);
        };
        
        /*! \brief accessor function for: bool m_bFootprintCalculated */
        bool& bGetFootprintCalculated() {
            return (m_bFootprintCalculated);
        };

        /*! \brief accessor function for: bool m_bFootprintCalculated */
        const bool& bGetFootprintCalculated()const {
            return (m_bFootprintCalculated);
        };

        /*! \brief accessor function for: bool m_bFootprintCalculated */
        void SetFootprintCalculated_b(const bool& bFootprintCalculated) {
            m_bFootprintCalculated = bFootprintCalculated;
        };

        /*! \brief accessor function for: double m_dGSD_m */
        double& dGetGSD_m() {
            return (m_gsd_m);
        };

        /*! \brief accessor function for: double m_dGSD_m */
        const double& dGetGSD_m()const {
            return (m_gsd_m);
        };

    protected:
        int m_iPayloadID_Sensor;
        int m_iPayloadID_Gimbal;
        double m_dHorizantalFOV_rad;
        double m_altitude_m;
        double m_dGimbalElevation_rad;
        double m_dAspectRatio;
        WAVELENGTHBAND_t m_wbWaveLengthBand;
        CSensorFootprint m_sensorFootprint;
        /*! \brief  this flag indicates whether (true) or not (false) the sensor footprint has been calculated*/
        bool m_bFootprintCalculated;
        /*! \brief  the ground sample distance for these settings*/
        double m_gsd_m;
    };

    //! Manages the parameters that describe the dynamic, sensor, and  weapon capabilities of the vehicle
    class CVehicleParameters
    {
    public: //typedefs
        typedef std::shared_ptr<afrl::cmasi::PayloadConfiguration> PTR_PAYLOADCONFIGURATION_t;
        typedef std::vector<PTR_PAYLOADCONFIGURATION_t> V_PTR_PAYLOADCONFIGURATION_t;

        typedef std::shared_ptr<V_PTR_PAYLOADCONFIGURATION_t> PTR_V_PTR_PAYLOADCONFIGURATION_t;
        typedef std::shared_ptr<CBoundary> PTR_BOUNDARY_t;

        typedef std::vector<float> V_FLOAT_t;
        typedef std::shared_ptr<CGSD_Settings> PTR_CGSD_SETTINGS_t;
        typedef std::pair <uint32_t, PTR_CGSD_SETTINGS_t> GSD_PAIR_t;
        typedef std::multimap<uint32_t, PTR_CGSD_SETTINGS_t> MM_UI32_GSD_SETTINGS_t;


        typedef afrl::cmasi::WavelengthBand::WavelengthBand WAVELENGTHBAND_t;

    public:

        CVehicleParameters();
        CVehicleParameters(const avtas::lmcp::Object* pConfiguration);
        virtual ~CVehicleParameters() { };

        // copy constructer
        CVehicleParameters(const CVehicleParameters& rhs);

        void CopySimpleMembers(const CVehicleParameters& rhs);
        
        void operator=(const CVehicleParameters& rhs);
        void operator=(const afrl::cmasi::AirVehicleConfiguration& rhs);
        void operator=(const afrl::vehicles::SurfaceVehicleConfiguration& rhs);
        void operator=(const afrl::vehicles::GroundVehicleConfiguration& rhs);

    public:

        void CalculateGSD_Settings();
        // GSD - Can the vehicle achieve given GSD? (yes/no)
        // GSD - Does the vehicle have to change altitude to obtain GSD? (yes/no)
        // GSD - Which altitudes can the vehicle use to obtain the given GSD? (list of max altitudes and corresponding sensor configurations)
        bool bCalculateGSD_Settings(const double& assignedAltitude_m);

        bool bFindGSDSettingsForAltitude(const double& gsd_m, double& altitudeDesired_m, CGSD_Settings& gsdSettings,
                afrl::cmasi::WavelengthBand::WavelengthBand wvlngthBand = afrl::cmasi::WavelengthBand::AllAny);

        bool bCanVehicleAchieveGSD(const double& gsd_m, double& altitudeMin_m,afrl::cmasi::WavelengthBand::WavelengthBand wvlngthBand);


    public: // interface to AirVehicleConfiguration

        //double& dGetCommandedSpeed_mps(){return(m_dCommandedVelocity_mps);};
        //double& dGetAltitudeNominal_m(){return(m_dAltitudeNominal_m);};
        //double& dGetSpeedNominal_mps(){return(m_dSpeedNominal_mps);};
        //double& dGetSpeedMax_mps(){return(m_dSpeedMax_mps);};
        //double& dGetSpeedMin_mps(){return(m_dSpeedMin_mps);};

        //double& dGetWeaponsLaunchMax_m(){return(m_dWeaponsLaunchMax_m);};
        //double& dGetWeaponsLaunchMin_m(){return(m_dWeaponsLaunchMin_m);};
        //double& dGetStandOffClassify_m(){return(m_dStandOffClassify_m);};
        //double& dGetStandOffAttack_m(){return(m_dStandOffAttack_m);};
        //double& dGetStandOffVerify_m(){return(m_dStandOffVerify_m);};
        //double& dGetFreeToTurnClassify_m(){return(m_dFreeToTurnClassify_m);};
        //double& dGetFreeToTurnAttack_m(){return(m_dFreeToTurnAttack_m);};
        //double& dGetFreeToTurnVerify_m(){return(m_dFreeToTurnVerify_m);};

        /** A list of all payload configurations (e.g. gimballed sensors) for this vehicle (Units: None)*/

    public:

        const double& dGetGimbalElevationStepSize_rad()const {
            return (m_dGimbalElevationStepSize_rad);
        };

        const double& dGetCameraHorizantalFOVStepSize_rad()const {
            return (m_dCameraHorizantalFOVStepSize_rad);
        };

        double& dGetGimbalElevationPrefered_rad() {
            return (m_dGimbalElevationPrefered_rad);
        };

        const double& dGetGimbalElevationPrefered_rad()const {
            return (m_dGimbalElevationPrefered_rad);
        };

        MM_UI32_GSD_SETTINGS_t& mmui32setGetGsdSettings() {
            return (m_mmui32setGsdSettings);
        };

        const MM_UI32_GSD_SETTINGS_t& mmui32setGetGsdSettings()const {
            return (m_mmui32setGsdSettings);
        };

        double& dGetAssignedAltitude_m() {
            return (m_assignedAltitude_m);
        };

        const double& dGetAssignedAltitude_m()const {
            return (m_assignedAltitude_m);
        };

        double& dGetAltitudeMax_m() {
            return (m_altitudeMax_m);
        };

        const double& dGetAltitudeMax_m()const {
            return (m_altitudeMax_m);
        };

        double& dGetAltitudeMin_m() {
            return (m_altitudeMin_m);
        };

        const double& dGetAltitudeMin_m()const {
            return (m_altitudeMin_m);
        };

        double& dGetCommandTurnRadius_m() {
            return (m_commandTurnRadius_m);
        };

        const double& dGetCommandTurnRadius_m()const {
            return (m_commandTurnRadius_m);
        };

        double& dGetCommandedSpeed_mps() {
            return (m_commandSpeed_mps);
        };

        const double& dGetCommandedSpeed_mps()const {
            return (m_commandSpeed_mps);
        };

        double& dGetMaximumRange_m() {
            return (m_maximumRange_m);
        };

        const double& dGetMaximumRange_m()const {
            return (m_maximumRange_m);
        };

        double& dGetMaximumTimeEndurance_s() {
            return (m_dMaximumTimeEndurance_s);
        };

        const double& dGetMaximumTimeEndurance_s()const {
            return (m_dMaximumTimeEndurance_s);
        };

        /*! \brief accessor function for: double m_dSpeedNominal_mps */
        double& dGetSpeedNominal_mps() {
            return (m_dSpeedNominal_mps);
        };

        /*! \brief accessor function for: double m_dSpeedNominal_mps */
        const double& dGetSpeedNominal_mps()const {
            return (m_dSpeedNominal_mps);
        };

        /*! \brief accessor function for: double m_dSpeedNominal_mps */
        void SetSpeedNominal_mps_d(const double& dSpeedNominal_mps) {
            m_dSpeedNominal_mps = dSpeedNominal_mps;
        };
        /*! \brief accessor function for: double m_dSpeedMax_mps */
        double& dGetSpeedMax_mps() {
            return (m_dSpeedMax_mps);
        };

        /*! \brief accessor function for: double m_dSpeedMax_mps */
        const double& dGetSpeedMax_mps()const {
            return (m_dSpeedMax_mps);
        };
        /*! \brief accessor function for: double m_dSpeedMax_mps */
        void SetSpeedMax_mps_d(const double& dSpeedMax_mps) {
            m_dSpeedMax_mps = dSpeedMax_mps;
        };

        /*! \brief accessor function for: double m_dSpeedMin_mps */
        double& dGetSpeedMin_mps() {
            return (m_dSpeedMin_mps);
        };

        /*! \brief accessor function for: double m_dSpeedMin_mps */
        const double& dGetSpeedMin_mps()const {
            return (m_dSpeedMin_mps);
        };

        /*! \brief accessor function for: double m_dSpeedMin_mps */
        void SetSpeedMin_mps_d(const double& dSpeedMin_mps) {
            m_dSpeedMin_mps = dSpeedMin_mps;
        };

        /*! \brief accessor function for: double m_dMaxBankAngle_deg */
        double& dGetMaxBankAngle_deg() {
            return (m_dMaxBankAngle_deg);
        };

        /*! \brief accessor function for: double m_dMaxBankAngle_deg */
        const double& dGetMaxBankAngle_deg()const {
            return (m_dMaxBankAngle_deg);
        };

        /*! \brief accessor function for: double m_dMaxBankAngle_deg */
        void SetMaxBankAngle_deg_d(const double& dMaxBankAngle_deg) {
            m_dMaxBankAngle_deg = dMaxBankAngle_deg;
        };
        
        /*! \brief accessor function for: PTR_V_PTR_PAYLOADCONFIGURATION_t m_ptr_vPayloadConfigurationList */
        PTR_V_PTR_PAYLOADCONFIGURATION_t& ptr_vGetPayloadConfigurationList() {
            return (m_ptr_vPayloadConfigurationList);
        };

        /*! \brief accessor function for: PTR_V_PTR_PAYLOADCONFIGURATION_t m_ptr_vPayloadConfigurationList */
        const PTR_V_PTR_PAYLOADCONFIGURATION_t& ptr_vGetPayloadConfigurationList()const {
            return (m_ptr_vPayloadConfigurationList);
        };

        /*! \brief accessor function for: PTR_V_PTR_PAYLOADCONFIGURATION_t m_ptr_vPayloadConfigurationList */
        void SetPayloadConfigurationList_ptr_v(const PTR_V_PTR_PAYLOADCONFIGURATION_t& ptr_vPayloadConfigurationList) {
            m_ptr_vPayloadConfigurationList = ptr_vPayloadConfigurationList;
        };

        /*! \brief accessor function for: PTR_BOUNDARY_t m_ptr_AreaOfOperations */
        PTR_BOUNDARY_t& ptr_GetAreaOfOperations() {
            return (m_ptr_AreaOfOperations);
        };

        /*! \brief accessor function for: PTR_BOUNDARY_t m_ptr_AreaOfOperations */
        const PTR_BOUNDARY_t& ptr_GetAreaOfOperations()const {
            return (m_ptr_AreaOfOperations);
        };

        /*! \brief accessor function for: PTR_BOUNDARY_t m_ptr_AreaOfOperations */
        void SetAreaOfOperations_ptr_(const PTR_BOUNDARY_t& ptr_AreaOfOperations) {
            m_ptr_AreaOfOperations = ptr_AreaOfOperations;
        };

        /*! \brief accessor function for: uint32_t m_ui32RoadGraphID */
        uint32_t& ui32GetRoadGraphID() {
            return (m_ui32RoadGraphID);
        };

        /*! \brief accessor function for: uint32_t m_ui32RoadGraphID */
        const uint32_t& ui32GetRoadGraphID()const {
            return (m_ui32RoadGraphID);
        };

        /*! \brief accessor function for: uint32_t m_ui32RoadGraphID */
        void SetRoadGraphID_ui32(const uint32_t& ui32RoadGraphID) {
            m_ui32RoadGraphID = ui32RoadGraphID;
        };

        
    protected:

        const double m_dGimbalElevationStepSize_rad;
        const double m_dCameraHorizantalFOVStepSize_rad;
        double m_dGimbalElevationPrefered_rad;

        MM_UI32_GSD_SETTINGS_t m_mmui32setGsdSettings; //uses Altitude as the index to look up GSD, altitude and zoom level
        double m_assignedAltitude_m;
        double m_altitudeMax_m;
        double m_altitudeMin_m;
        double m_commandTurnRadius_m;
        double m_commandSpeed_mps; // needs to be set from the air vehicle configuration profile, or the vehicle info in the plan request
        double m_maximumRange_m; //this comes from the AirVehicleState message (EnergyAvailable/ActualEnergyRate*dGetCommandedSpeed_mps()
        double m_dMaximumTimeEndurance_s; //this comes from the AirVehicleState message (EnergyAvailable/ActualEnergyRate)
        /*! \brief  */
        double m_dSpeedNominal_mps;
        /*! \brief  */
        double m_dSpeedMax_mps;
        /*! \brief  */
        double m_dSpeedMin_mps;
        /*! \brief  */
        double m_dMaxBankAngle_deg;
        
        /*! \brief A list of all payload configurations (e.g. gimballed sensors) for this vehicle (Units: None)*/
        /*  these are copied from the vehicle configuration*/
        PTR_V_PTR_PAYLOADCONFIGURATION_t m_ptr_vPayloadConfigurationList;

        /*! \brief  represents a keep-in boundary for the vehicle, if present*/
        PTR_BOUNDARY_t m_ptr_AreaOfOperations;
        /*! \brief  for road vehicles this is the ID of the road network to use*/
        uint32_t m_ui32RoadGraphID;

        
        
    };


    ostream &operator <<(ostream &os, const CVehicleParameters& vehprmRhs);


} //namespace n_FrameworkLib

#endif // !defined(VEHICLE_PARAMETERS_H__301D6590_12D0_4F65_8B3F_89B507DCC41F__INCLUDED_)
