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
// TaskAssignment.h: interface for the CTaskAssignment class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_TASKASSIGNMENT_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_)
#define AFX_TASKASSIGNMENT_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"

#include <vector>


namespace n_FrameworkLib
{

class CTaskAssignment  
{
public:
    enum n_enTaskType_t 
    {
        taskAnotherLook_01,
        taskAnotherLook_02,
        taskLoiter,
        taskObjective,
        taskSearch,
        taskClassify,
        taskAttack,
        taskVerify,
        taskFinished,
        taskUnknown,
        taskNumberEntries
    };
    
public:        //typedefs
    typedef std::vector<CTaskAssignment> V_TASKASSIGNMENT_t;
    typedef std::vector<CTaskAssignment>::iterator V_TASKASSIGNMENT_IT_t;
    typedef std::vector<CTaskAssignment>::const_iterator V_TASKASSIGNMENT_CONST_IT_t;


public:    //constructors/destructors

    CTaskAssignment(int iTaskID=-1,int iObjectID=-1,n_enTaskType_t taskType=taskUnknown,double dMinimumTaskCost=0.0,double dTimePrerequisite=0.0)
        :m_iTaskID(iTaskID),
        m_iObjectiveID(iObjectID),
        m_taskType(taskType),
        m_dMinimumTaskCost(dMinimumTaskCost),
        m_dTimePrerequisite(dTimePrerequisite)
    {};

    virtual ~CTaskAssignment(){};

    // copy constructer
    CTaskAssignment(const CTaskAssignment& rhs)
    {
        iGetTaskID() = rhs.iGetTaskID();
        iGetObjectiveID() = rhs.iGetObjectiveID();
        taskGetType() = rhs.taskGetType();
        dGetMinimumTaskCost() = rhs.dGetMinimumTaskCost();
        dGetTimePrerequisite() = rhs.dGetTimePrerequisite();
    }
    // = operator
    void operator =(const CTaskAssignment& rhs)
    {
        iGetTaskID() = rhs.iGetTaskID();
        iGetObjectiveID() = rhs.iGetObjectiveID();
        taskGetType() = rhs.taskGetType();
        dGetMinimumTaskCost() = rhs.dGetMinimumTaskCost();
        dGetTimePrerequisite() = rhs.dGetTimePrerequisite();
    }

public:    //accessor functions

    int& iGetTaskID(){return(m_iTaskID);};
    const int& iGetTaskID()const{return(m_iTaskID);};

    int& iGetObjectiveID(){return(m_iObjectiveID);};
    const int& iGetObjectiveID()const{return(m_iObjectiveID);};

    n_enTaskType_t& taskGetType(){return(m_taskType);};
    const n_enTaskType_t& taskGetType()const{return(m_taskType);};

    double& dGetMinimumTaskCost(){return(m_dMinimumTaskCost);};
    const double& dGetMinimumTaskCost()const{return(m_dMinimumTaskCost);};

    double& dGetTimePrerequisite(){return(m_dTimePrerequisite);};
    const double& dGetTimePrerequisite()const{return(m_dTimePrerequisite);};

protected:    //storage
    int m_iTaskID;                //id number for the task, must be unique amoung all tasks
    int m_iObjectiveID;            //id number for the object of the task
    n_enTaskType_t m_taskType;    //type of task to be performed
    double m_dMinimumTaskCost;            //minimum distance vehicle needs to fly to accomplish task
    double m_dTimePrerequisite;
};

}    //namespace n_FrameworkLib

#endif // !defined(AFX_TASKASSIGNMENT_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_)
