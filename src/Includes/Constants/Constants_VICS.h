// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Constants_VICS.h
 * Author: steve
 *
 * Created on February 26, 2014, 7:20 PM
 */

#ifndef CONSTANTS_VICS_H
#define    CONSTANTS_VICS_H

#include <string>
#include <cstdint>

namespace n_Const
{   

    /*! \class c_Constant_VICS
        \brief this class contains "singleton" constants for VICS message handling.

     *  @par Description:
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li>  - 
     * 
     * </ul> @n
     */
class c_Constant_VICS
{
public: //constants
    
    // 
/*! @name VICS Constant Strings
 *   
 */
///@{
//! 
    
    static const uint32_t& ui32GetGhostUgsIdOffset(){static uint32_t ui32Value(10000);return(ui32Value);};
    static const uint32_t& ui32GetUgsTaskIdOffset(){static uint32_t ui32Value(1000);return(ui32Value);};
    
    
    static const std::string& strGetEntityType_UGS(){static std::string strString("UGS");return(strString);};
    static const std::string& strGetEntityType_UAV(){static std::string strString("UAV");return(strString);};
    
    
//SAVE MESSAGE FORMAT
//NAME FORMAT::
//     $$_TTTTTTTTTT_OOOOOOO_MMMMMMM_FORMATTEDTIME
//WHERE:
//     $$ - message type
//     TTTTTTTTTT - time in seconds since 1/1/1970
//     OOOOOOO - Originator ID
//     MMMMMMM - Message ID
//     FORMATTEDTIME - is a time string

//  regex filter
//  "_\\d{10}_\\d{7}_\\d{7}"

//#define STRING_INTRUDER_ALERT ""    
    static const std::string& strGetTypeString_IntruderAlert(){static std::string strString("IA");return(strString);};
//#define STRING_STATE_TRANSITION ""    
    static const std::string& strGetTypeString_StateTransition(){static std::string strString("ST");return(strString);};
//#define STRING_DISMOUNT_MESSAGE ""    
    static const std::string& strGetTypeString_DismountMessage(){static std::string strString("DM");return(strString);};
//#define STRING_QUERY_MESSAGE ""    
    static const std::string& strGetTypeString_QueryMessage(){static std::string strString("QM");return(strString);};
//#define STRING_QUERY_RESPONSE_MESSAGE ""    
    static const std::string& strGetTypeString_QueryResponse(){static std::string strString("QR");return(strString);};

//#define FILE_NAME_TYPE_POSITION (0)
    static const uint32_t ui32GetType_Position(){return(0);};
//#define FILE_NAME_TYPE_SIZE (2)    
    static const uint32_t ui32GetType_Size(){return(2);};
//#define FILE_NAME_TIME_POSITION (FILE_NAME_TYPE_POSITION + FILE_NAME_TYPE_SIZE + 1)    
    static const uint32_t ui32GetTime_Position(){return(ui32GetType_Position() + ui32GetType_Size() + 1);};
//#define FILE_NAME_TIME_SIZE (10)    
    static const uint32_t ui32GetTime_Size(){return(14);};
//#define FILE_NAME_ORIGINATOR_ID_POSITION (FILE_NAME_TIME_POSITION + FILE_NAME_TIME_SIZE + 1)    
    static const uint32_t ui32GetOriginatorID_Position(){return(ui32GetTime_Position() + ui32GetTime_Size() + 1);};
//#define FILE_NAME_ORIGINATOR_ID_SIZE (7)    
    static const uint32_t ui32GetOriginatorID_Size(){return(7);};
//#define FILE_NAME_MESSAGE_ID_POSITION (FILE_NAME_ORIGINATOR_ID_POSITION + FILE_NAME_ORIGINATOR_ID_SIZE + 1)    
    static const uint32_t ui32getMessageID_Position(){return(ui32GetOriginatorID_Position() + ui32GetOriginatorID_Size() + 1);};
//#define FILE_NAME_MESSAGE_ID_SIZE (8)    
    static const uint32_t ui32getMessageID_Size(){return(8);};
//#define FILE_NAME_BASE_SIZE (FILE_NAME_TYPE_SIZE + 1 + FILE_NAME_TIME_SIZE + 1 + FILE_NAME_ORIGINATOR_ID_SIZE + 1 + FILE_NAME_MESSAGE_ID_SIZE)    
    static const uint32_t ui32GetFleNameBase_Size(){return(ui32GetType_Size() + 1 + ui32GetTime_Size() + 1 + ui32GetOriginatorID_Size() + 1 + ui32getMessageID_Size());};

// DIRECTORIES
//#define DIRECTORY_VICS_MESSAGES ""
    static const std::string& strGetDirectoryVICS_Messages(){static std::string strString("VICS_Messages/");return(strString);};
//#define DIRECTORY_VICS_MESSAGES_GENERAL ""
    static const std::string& strGetDirectoryGeneralMessages(){static std::string strString("GeneralMessages/");return(strString);};
//#define DIRECTORY_VICS_MESSAGES_INTRUDER_ALERT ""
    static const std::string& strGetDirectoryIntruderAlertMessages(){static std::string strString("IntruderAlertMessages/");return(strString);};
//#define DIRECTORY_VICS_MESSAGES_STATE_TRANSITION ""
    static const std::string& strGetDirectoryStateTransitionMessages(){static std::string strString("StateTransitionMessages/");return(strString);};
//#define DIRECTORY_VICS_MESSAGES_DISMOUNT ""
    static const std::string& strGetDirectoryDismountMessages(){static std::string strString("DismountMessages/");return(strString);};
    
    
///@}


};

};      //namespace n_Const



#endif    /* CONSTANTS_VICS_H */

