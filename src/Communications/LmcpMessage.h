// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_DATA_LMCP_MESSAGE_H
#define UXAS_MESSAGE_DATA_LMCP_MESSAGE_H

#include "MessageAttributes.h"

#include "avtas/lmcp/Factory.h"

#include "stdUniquePtr.h"

#include <string>
#include <tuple>

namespace uxas
{
namespace communications
{
namespace data
{

/** \class LmcpMessage
 * 
 * \par Description:
 * Message object containing message attributes and payload.
 * 
 * \n
 */
class LmcpMessage
{
public:
    LmcpMessage()
    {
    };

    LmcpMessage(std::unique_ptr<MessageAttributes> messageAttributes, std::unique_ptr<avtas::lmcp::Object> lmcpObject)
    {
        m_attributes = std::move(messageAttributes);
        m_object = std::move(lmcpObject);
    };

    /** \brief Message attributes associated with the payload.
     * 
     * @return message attributes
     */
    std::unique_ptr<MessageAttributes> m_attributes;

    /** \brief Data payload to be transported.
     * 
     * @return data string sent/received via message system.
     */
    std::shared_ptr<avtas::lmcp::Object> m_object;

};

}; //namespace data
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_DATA_LMCP_MESSAGE_H */
