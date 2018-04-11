// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Constant_Strings.h
 * Author: steve
 *
 * Created on January 22, 2013, 2:20 PM
 */

#ifndef CONSTANT_STRINGS_H
#define    CONSTANT_STRINGS_H

#include <string>

namespace n_Const
{   

    /*! \class c_Constant_Strings
        \brief this class contains "singleton" constant strings for the UxAS software.

     *  @par Description:
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li>  - 
     * 
     * </ul> @n
     */
class c_Constant_Strings
{
public: //constants
    
    // 
/*! @name MessagePassing Strings
 *   
 */
///@{
//! 
    static const std::string& strGetSTARTUP_COMPLETE(){static std::string strString("STARTUP_COMPLETE");return(strString);};
    static const std::string& strgetID(){static std::string strString("VehicleID");return(strString);};
    static const std::string& strGetUgsID(){static std::string strString("UgsID");return(strString);};
    static const std::string& strGetSendMessageQuery(){static std::string strString("SendMessageQuery");return(strString);};
    static const std::string& strGetDetectionLocation(){static std::string strString(strGetPrepend_lmcp()+ ":DetectionLocation");return(strString);};
    static const std::string& strGetRawIntruderAlert(){static std::string strString(strGetPrepend_lmcp()+ ":RAW:IntruderAlert");return(strString);};
    static const std::string& strGetSubTaskResponse(){static std::string strString(strGetPrepend_lmcp()+ ":SUBTASK:Response");return(strString);};
    static const std::string& strGetCCA_Plan(){static std::string strString(strGetPrepend_lmcp()+ ":CCA_Plan:");return(strString);};
    static const std::string& strGetVicsStorage(){static std::string strString(strGetPrepend_lmcp()+ ":VicsStorage");return(strString);};
    
    static const std::string& strGetImpactHeartbeat(){static std::string strString(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":IMPACT:ImpactHeartbeat");return(strString);};
    static const std::string& GetCreateNewServiceString(){static std::string strString(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":UXNATIVE:CreateNewService");return(strString);};
    static const std::string& GetKillServiceString(){static std::string strString(n_Const::c_Constant_Strings::strGetPrepend_lmcp() + ":UXNATIVE:KillService");return(strString);};
    
    static const std::string& strGetCurentTime(){static std::string strString("CurrentTime");return(strString);};
    static const std::string& strGetTestMessage(){static std::string strString(strGetPrepend_lmcp()+ ":TestMessage");return(strString);};
    static const std::string& strGetRangeTestMessage(){static std::string strString(strGetPrepend_lmcp()+ ":RangeTestMessage");return(strString);};
    
    /*! \brief this is prefixed to the zyre uuid to facilitate pub/sub message passing, e.g. "ZYRE_ADDAB7B8586C404A9DB00F35D6651D1F".  */
    static const std::string& strGetZyrePrefix(){static std::string strString("ZYRE_");return(strString);};
    /*! \brief this is prefixed to the zyre uuid to facilitate pub/sub message passing only to zyre (not from), e.g. "TOZYRE_ADDAB7B8586C404A9DB00F35D6651D1F".  */
    static const std::string& strGetZyreToPrefix(){static std::string strString("TOZYRE_");return(strString);};
    /*! \brief this is the string used to separate components in an xml string for zyre.  */
    static const std::string& strGetZyreComponentSeparator(){static std::string strString("::");return(strString);};
    /*! \brief this is the string used to identify the VICS EntityID string in the zyre header.  */
    static const std::string& strGetZyreEntityID(){static std::string strString("ZyreEntityID");return(strString);};
    /*! \brief this is the string used to identify the VICS EntityID string in the zyre header.  */
    static const std::string& strGetZyreVicsEntityType(){static std::string strString("ZyreVicsEntityType");return(strString);};
    /*! \brief this is the string used to identify the component configuration string in the zyre header.  */
    static const std::string& strGetZyreConfiguration(){static std::string strString("ZyreConfiguration");return(strString);};
    
    /*! \brief this is prepended to the key for LMCP messages.  */
    static const std::string& strGetPrepend_lmcp(){static std::string strString("lmcp");return(strString);};
    /*! \brief this is prepended to the key for json messages.  */
    static const std::string& strGetPrepend_json(){static std::string strString("json");return(strString);};
    /*! \brief this is prepended to the key for unknown message types.  */
    static const std::string& strGetPrepend_unknown(){static std::string strString("unknown");return(strString);};
    
    
    
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetTimeSent_s(){static std::string strString("TimeSent_s");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetPayload(){static std::string strString("Payload");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strgetMessageID(){static std::string strString("MessageId");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetMessageType(){static std::string strString("MessageType");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSenderID(){static std::string strString("SenderID");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSenderLatitude_deg(){static std::string strString("SenderLatitude_deg");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSenderLongitude_deg(){static std::string strString("SenderLongitude_deg");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSenderAltitude_m(){static std::string strString("SenderAltitude_m");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSentTime_s(){static std::string strString("SentTime_s");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceivedTime_s(){static std::string strString("ReceivedTime_s");return(strString);};
     /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceiverID(){static std::string strString("ReceiverID");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceiverLatitude_deg(){static std::string strString("ReceiverLatitude_deg");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceiverLongitude_deg(){static std::string strString("ReceiverLongitude_deg");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceiverAltitude_m(){static std::string strString("ReceiverAltitude_m");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetReceiverHeading_deg(){static std::string strString("ReceiverHeading_deg");return(strString);};
    
   /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetCommTimeDelay_s(){static std::string strString("GetCommTimeDelay_s");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetCommDistance_m(){static std::string strString("CommDistance_m");return(strString);};
    /*! \brief used as the key in a key/value pair  */
    static const std::string& strGetSentMessageSize_bytes(){static std::string strString("SentMessageSize_bytes");return(strString);};
   
///@}


};

};      //namespace n_Const

#endif    /* CONSTANT_STRINGS_H */

