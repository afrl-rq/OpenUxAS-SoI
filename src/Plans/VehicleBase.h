// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   VehicleBase.h
 * Author: steve
 *
 * Created on August 22, 2014, 12:39 PM
 */

#ifndef VEHICLEBASE_H
#define    VEHICLEBASE_H


//#include "GlobalDefines.h"
#include "BaseObject.h"
#include "Assignment.h"
#include "VehicleParameters.h"

#include "afrl/cmasi/AirVehicleConfiguration.h"

namespace n_FrameworkLib
{

class c_VehicleBase : public CBaseObject, public CAssignment, public CVehicleParameters
{
public:
    enum n_enVehicleType_t 
    {
        envehicleNone,
        envehicleUAV,
        envehicleSurfaceVehicle,
        envehicleGroundVehicle,
        envehicleMunition,
        envehicleAFRLMAV,
        envehicleBAT3,
        envehicleCustom,
        envehicleUnknown,
        envehicleNumberEntries
    };
    
public:

    c_VehicleBase() :
    	CBaseObject(1),
		m_vehicleType(envehicleUAV),
		m_iVisibilityVertexIndex(-1),
		m_bUseTaskEligibility(false),
		m_dHeadingInitial_rad(0.0)
    {};
    
    c_VehicleBase(const int& iID,
    		const double& dNorth_m, const double& dEast_m, const double& dPositionZ_m,
            const double& dPsi_rad,
            const double& dDistancePrevious = 0.0,
            const n_enVehicleType_t& vehicleType = envehicleMunition
            ) :
            	CBaseObject(iID, dNorth_m, dEast_m, dPositionZ_m, dPsi_rad),
				CAssignment(iID, dNorth_m, dEast_m, dPositionZ_m, dPsi_rad, dDistancePrevious),
				m_vehicleType(vehicleType),
				m_iVisibilityVertexIndex(-1),
				m_bUseTaskEligibility(false),
				m_dHeadingInitial_rad(dPsi_rad)
    {
        stringstream sstrFileName;
        sstrFileName << "V_" << iGetID();
        strGetBaseFileName() = sstrFileName.str();
    };

    c_VehicleBase(afrl::cmasi::AirVehicleConfiguration* pAirVehicleConfiguration) :
    	CBaseObject(pAirVehicleConfiguration->getID()),
		CVehicleParameters(pAirVehicleConfiguration),
		m_vehicleType(envehicleUAV),
		m_iVisibilityVertexIndex(-1),
		m_bUseTaskEligibility(false),
		m_dHeadingInitial_rad(0.0)
    {
        stringstream sstrFileName;
        sstrFileName << "V_" << iGetID();
        strGetBaseFileName() = sstrFileName.str();
    };

    c_VehicleBase(afrl::vehicles::SurfaceVehicleConfiguration* pSurfaceVehicleConfiguration) :
    	CBaseObject(pSurfaceVehicleConfiguration->getID()),
		CVehicleParameters(pSurfaceVehicleConfiguration),
		m_vehicleType(envehicleSurfaceVehicle),
		m_iVisibilityVertexIndex(-1),
		m_bUseTaskEligibility(false),
		m_dHeadingInitial_rad(0.0)
    {
        stringstream sstrFileName;
        sstrFileName << "V_" << iGetID();
        strGetBaseFileName() = sstrFileName.str();
    };

    c_VehicleBase(afrl::vehicles::GroundVehicleConfiguration* pGroundVehicleConfiguration) :
    	CBaseObject(pGroundVehicleConfiguration->getID()),
		CVehicleParameters(pGroundVehicleConfiguration),
		m_vehicleType(envehicleGroundVehicle),
		m_iVisibilityVertexIndex(-1),
		m_bUseTaskEligibility(false),
		m_dHeadingInitial_rad(0.0)
    {
        stringstream sstrFileName;
        sstrFileName << "V_" << iGetID();
        strGetBaseFileName() = sstrFileName.str();
    };

    
    
    
    virtual ~c_VehicleBase() { };

    c_VehicleBase(const c_VehicleBase& rhs):
    CBaseObject(rhs),
    CAssignment(rhs),
    CVehicleParameters(rhs)
    {
        CopySimpleMembers(rhs);
    };

    void operator=(const c_VehicleBase& rhs) 
    {
        CBaseObject::operator =(rhs);
        CAssignment::operator =(rhs);
        CVehicleParameters::operator =(rhs);
        CopySimpleMembers(rhs);
    };

    void CopySimpleMembers(const c_VehicleBase& rhs) 
    {
        vehicleGetType() = rhs.vehicleGetType();
        iGetVisibilityVertexIndex() = rhs.iGetVisibilityVertexIndex();
        vuiGetTaskEligibility() = rhs.vuiGetTaskEligibility();
        bGetUseTaskEligibility() = rhs.bGetUseTaskEligibility();
        strGetBaseFileName() = rhs.strGetBaseFileName();
        stringstream sstrFileName;
        sstrFileName << "V_" << rhs.iGetID();
        strGetBaseFileName() = sstrFileName.str();
        dGetHeadingInitial_rad() = rhs.dGetHeadingInitial_rad();
    };

        void operator +=(const CAssignment& rhs) {
            c_VehicleBase::CAssignment::operator +=(rhs);
        }

        bool operator ==(const int& iRHS) {
            if (iGetID() == iRHS) {
                return (true);
            }
            return (false);
        }
        void operator=(const CPosition& rhs) {
            c_VehicleBase::CBaseObject::CPosition::operator =(rhs);
        };
        void operator=(const CBaseObject& rhs) {
            c_VehicleBase::CBaseObject::CPosition::operator =(rhs);
            SetID(rhs.iGetID());
            SetHeading(rhs.dGetHeading());
        };



public: //member functions

    bool bSetVehicleType(const n_enVehicleType_t& vehicleType) 
    {
        bool bReturn(true);
        vehicleGetType() = vehicleType;
        //InitializeVehicleType(vehicleGetType());
        return (bReturn);
    };

        void UpdateVehicleStateFromAssignment() {
            m_north_m = posGetPositionAssignedLast().m_north_m;
            m_east_m = posGetPositionAssignedLast().m_east_m;
            SetHeadingFinal(dCalculateFinalHeading_rad());
            SetHeading(dGetHeadingFinal());
        };

        void UpdateVehicleStateFromAssignment(const double& dHeadingFinal_rad) {
            m_north_m = posGetPositionAssignedLast().m_north_m;
            m_east_m = posGetPositionAssignedLast().m_east_m;
            SetHeadingFinal(dHeadingFinal_rad);
            SetHeading(dGetHeadingFinal());
        };

        bool bIsObjectiveEligible(const int& iObjectiveID) {
            bool bReturn(true);

            if (bGetUseTaskEligibility()) {
                auto itTaskID = vuiGetTaskEligibility().begin();
                for (; itTaskID != vuiGetTaskEligibility().end(); itTaskID++) {
                    if (static_cast<int> (*itTaskID) == iObjectiveID) {
                        break;
                    }
                } //for(auto itTaskID=vuiGetTaskEligibility().begin();
                if (itTaskID == vuiGetTaskEligibility().end()) {
                    // this task id not in the list
                    bReturn = false;
                }
            } //if(bGetUseTaskEligibility())
            return (bReturn);
        };
    
public: //accessors

    n_enVehicleType_t& vehicleGetType() {
        return (m_vehicleType);
    };

    const n_enVehicleType_t& vehicleGetType() const {
        return (m_vehicleType);
    };

    int& iGetVisibilityVertexIndex() {
        return (m_iVisibilityVertexIndex);
    };

    const int& iGetVisibilityVertexIndex()const {
        return (m_iVisibilityVertexIndex);
    };

    std::vector<uint32_t>& vuiGetTaskEligibility() {
        return (m_vuiTaskEligibility);
    };

    const std::vector<uint32_t>& vuiGetTaskEligibility()const {
        return (m_vuiTaskEligibility);
    };

    bool& bGetUseTaskEligibility() {
        return (m_bUseTaskEligibility);
    };

    const bool& bGetUseTaskEligibility()const {
        return (m_bUseTaskEligibility);
    };

    string& strGetBaseFileName() {
        return (m_strBaseFileName);
    };

    const string& strGetBaseFileName()const {
        return (m_strBaseFileName);
    };

    double& dGetHeadingInitial_rad() {
        return (m_dHeadingInitial_rad);
    };

    const double& dGetHeadingInitial_rad()const {
        return (m_dHeadingInitial_rad);
    };

protected:
    n_enVehicleType_t m_vehicleType;
    int m_iVisibilityVertexIndex; //used while building the visibility graph
    std::vector<uint32_t> m_vuiTaskEligibility;
    bool m_bUseTaskEligibility;
    std::string m_strBaseFileName;
    double m_dHeadingInitial_rad;
};

} //namespace n_FrameworkLib


#endif    /* VEHICLEBASE_H */

