// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Constants_Control.h
 * Author: steve
 *
 * Created on September 25, 2015, 4:47 PM
 */

#ifndef CONSTANTS_CONTROL_H
#define    CONSTANTS_CONTROL_H

#include <string>
#include "Constants/Constant_Strings.h"

namespace n_Const
{   

    using PlanCost_t = int32_t; // this is for path planning
    
    /*! \class c_Constants_Control
        \brief this class contains "singleton" constants for the UxAS software.

     *  @par Description:
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li>  - 
     * 
     * </ul> @n
     */
class c_Constants_Control
{
public: //constants
    
    // in-process socket addresses
/*! @name In-Process Socket Addresses
 *   
 */
///@{
//! 
    static const std::string& strGetInProc_ThreadControl(){static std::string strString("inproc://thread_control");return(strString);};
    static const std::string& strGetInProc_FromMessageHub(){static std::string strString("inproc://from_message_hub");return(strString);};
    static const std::string& strGetInProc_ToMessageHub(){static std::string strString("inproc://to_message_hub");return(strString);};
    static const std::string& strGetInProc_ConfigurationHub(){static std::string strString("inproc://configuration_hub");return(strString);};
    static const std::string& strGetInProc_ManagerThreadControl(){static std::string strString("inproc://manager_thread_control");return(strString);};
///@}

    // thread control messages
/*! @name Thread Control Messages
 *   
 */
///@{
//! 
    /*! \brief this message is sent to the Component Manager to terminate all of the threads.  */
    static const std::string& strGetMsg_KillAll(){static std::string strString("ctrlKillAll");return(strString);};
    /*! \brief this message is sent to the Component Manager to terminate the thread with the ID given in the message, e.g. "ctrlKillComponent:10000".  */
    static const std::string& strGetMsg_KillComponent(){static std::string strString("ctrlKillComponent");return(strString);};
    // TODO:: is this used anywhere???
    static const std::string& strGetMsg_LoadXmlConfigutation(){static std::string strString("ctrlLoadXmlConfigutation");return(strString);};
    
///@}


};

};      //namespace n_UxAS_Constants

#endif    /* CONSTANTS_CONTROL_H */

