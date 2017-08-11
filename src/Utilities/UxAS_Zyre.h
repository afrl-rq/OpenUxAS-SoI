/* 
 * File:   UxAS_Zyre.h
 * Author: steve
 *
 * Created on February 24, 2014, 6:15 PM
 */

#ifndef UXAS_ZYRE_H
#define	UXAS_ZYRE_H


#include "czmq.h"
#include "zyre.h"

#include <cstring>
#include <string>

namespace n_ZMQ
{

//// ZYRE HELPER FUNCTIONS
//    typedef std::shared_ptr<zyre_t> PTR_ZYRE_t;
//    typedef std::shared_ptr<zctx_t> PTR_ZCTX_t;

    
static void
zmsgPopstr (zmsg_t *self,std::string& strMessage)
{
    assert (self);
    strMessage = "";
    uint32_t ui32Length(zframe_size(zmsg_first(self)));
    char* pString  = zmsg_popstr(self);
    //std::cerr << "szLength[" << szLength << "]" << std::endl;
    if(pString)
    {
        strMessage = std::string(pString,ui32Length);
        delete pString;
        pString = 0;
    }
}

    
static int
s_SendString (void *socket, bool more,const std::string strString)
{
    assert (socket);
    
    int len = strString.size();
    zmq_msg_t message;
    zmq_msg_init_size (&message,len);
    memcpy (zmq_msg_data (&message),strString.c_str(), len);
    int rc = zmq_sendmsg (socket, &message, more? ZMQ_SNDMORE: 0);

    return rc == -1? -1: 0;
}



//  ---------------------------------------------------------------------
//  Return the item at the specified key, or null
static void ZhashLookup(zhash_t *headers,const std::string& strKey,std::string& strValue)
{
    std::string strReturn;
    char * cstrKey = new char [strKey.length()+1];
    std::strcpy (cstrKey, strKey.c_str());
    strValue = "";
    const char* pcValue = static_cast<const char*>(zhash_lookup (headers,cstrKey));
    if(pcValue)
    {
        strValue = pcValue;
    }
    delete[] cstrKey; cstrKey = 0;
}

//  ---------------------------------------------------------------------
//  Set node header; these are provided to other nodes during discovery
//  and come in each ENTER message.
static void zyreSetHeaderEntry(zyre_t* pZyreNode,const std::string& strKey,const std::string& strValue)
{
        char * cstrKey = new char [strKey.length()+1];
        std::strcpy (cstrKey,strKey.c_str());
        char * cstrValue = new char [strValue.length()+1];
        std::strcpy (cstrValue, strValue.c_str());
        zyre_set_header(pZyreNode,cstrKey,"%s",cstrValue);
        delete[] cstrKey; cstrKey = 0;
        delete[] cstrValue; cstrValue = 0;
}

//  ---------------------------------------------------------------------
//  Join a named group; after joining a group you can send messages to
//  the group and all Zyre nodes in that group will receive them.
static void zyreJoin(zyre_t* pZyreNode,const std::string& strZyreGroup)
{
        char * cstrZyreGroup = new char [strZyreGroup.length()+1];
        std::strcpy (cstrZyreGroup, strZyreGroup.c_str());
        zyre_join(pZyreNode,cstrZyreGroup);
        delete[] cstrZyreGroup; cstrZyreGroup = 0;
}


//  ---------------------------------------------------------------------
//  Send message to single peer, specified as a UUID string
//  Destroys message after sending

static int zyreWhisper (zyre_t* pZyreNode,std::string& strPeer,const std::string strMessage)
{
    assert (pZyreNode);
    assert(!strPeer.empty());

    zmsg_t *msg = zmsg_new ();
    zmsg_addmem (msg,strMessage.data(),strMessage.length());
    zyre_whisper(pZyreNode,const_cast<char*>(strPeer.c_str()),&msg);
    
    return 0;
}

static int zyreWhisper2 (zyre_t* pZyreNode,const std::string& strPeer,const std::string strMessage)
{
    assert (pZyreNode);
    assert(!strPeer.empty());

    zmsg_t *msg = zmsg_new ();
    zmsg_addmem (msg,strMessage.data(),strMessage.length());
    zyre_whisper(pZyreNode,const_cast<char*>(strPeer.c_str()),&msg);
    
    return 0;
}


//  ---------------------------------------------------------------------
//  Send message to a named group
//  Destroys message after sending

static int zyreShout (zyre_t* pZyreNode,std::string& strGroup,const std::string strMessage)
{
    assert(pZyreNode);
    assert(!strGroup.empty());

    zmsg_t *msg = zmsg_new ();
    zmsg_addmem (msg,strMessage.data(),strMessage.length());
    zyre_shout(pZyreNode,const_cast<char*>(strGroup.c_str()),&msg);
    
    return 0;
}




} //namespace n_ZMQ



#endif	/* UXAS_ZYRE_H */

