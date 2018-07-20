// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_DATA_ADDRESSED_ATTRIBUTED_MESSAGE_H
#define UXAS_MESSAGE_DATA_ADDRESSED_ATTRIBUTED_MESSAGE_H

#include "AddressedMessage.h"
#include "MessageAttributes.h"

#include "UxAS_Log.h"

#include "stdUniquePtr.h"

#include <string>
#include <tuple>

namespace uxas
{
namespace communications
{
namespace data
{

/** \class AddressedAttributedMessage
 * 
 * \par Description:
 * Data object consisting of message address, attributes and payload.
 * 
 * \n
 */
class AddressedAttributedMessage : public AddressedMessage
{
public:
    //address$contentType|descriptor|sourceEntityId||sourceServiceId$payload
    //sourceGroup can be empty string
    uint32_t s_minimumDelimitedAddressAttributeMessageStringLength{11};

    static const std::string&
    s_typeName() { static std::string s_string("AddressedAttributedMessage"); return (s_string); };

    AddressedAttributedMessage()
    : AddressedMessage() { };

    bool
    setAddressAttributesAndPayload(const std::string address, const std::string contentType, const std::string descriptor, 
    const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId, const std::string payload)
    {
        if (!AddressedMessage::isValidAddress(address))
        {
            m_isValid = false;
            return (m_isValid);
        }

        if (payload.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAndPayload payload must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        m_messageAttributes = uxas::stduxas::make_unique<MessageAttributes>();
        if (m_messageAttributes->setAttributes(std::move(contentType), std::move(descriptor), std::move(sourceGroup), std::move(sourceEntityId), std::move(sourceServiceId)))
        {
            m_address.clear();
            m_payload.clear();
            m_address = address;
            m_payload = payload;
            m_string = m_address + s_addressAttributesDelimiter() + m_messageAttributes->getString() + s_addressAttributesDelimiter() + m_payload;
            m_isValid = true;
            return (m_isValid);
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAttributesAndPayload failed to initialize message attributes");
            m_isValid = false;
            return (m_isValid);
        }
   };
   
   bool
   updateSourceAttributes(const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId)
   {
       m_isValid = m_isValid & m_messageAttributes->updateSourceAttributes(sourceGroup, sourceEntityId, sourceServiceId);
       m_string = m_address + s_addressAttributesDelimiter() + m_messageAttributes->getString() + s_addressAttributesDelimiter() + m_payload;
       return (m_isValid);
   };

    bool
    updateAddress(const std::string address)
    {
        m_address = address;
        m_string = m_address + s_addressAttributesDelimiter() + m_messageAttributes->getString() + s_addressAttributesDelimiter() + m_payload;
        return (m_isValid);
    }

    bool
    setAddressAttributesAndPayloadFromDelimitedString(const std::string delimitedString)
    {
        if (delimitedString.length() >= s_minimumDelimitedAddressAttributeMessageStringLength)
        {
            return (parseAddressedAttributedMessageStringAndSetFields(std::move(delimitedString)));
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAttributesAndPayloadFromDelimitedString delimited string length must be >= ", s_minimumDelimitedAddressAttributeMessageStringLength);
            m_isValid = false;
            return (false);
        }
    };

    /** \brief Message address, attribute and payload combined into a single, 
     * delimited string.
     * 
     * @return Message string consisting of concatenated address, attribute 
     * fields and payload (overload method).
     */
    const std::string&
    getString() const override
    {
        if (m_messageAttributes)
        {
            return m_string;
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::getString returning empty string since message attributes have been detached");
            return (s_emptyString);
        }
    };

    /** \brief Ownership transfer accessor for message attributes.
     * 
     * @return message attributes
     */
    std::unique_ptr<MessageAttributes>
    getMessageAttributesOwnership()
    {
        return (std::move(m_messageAttributes));
    };

    /** \brief Read-only accessor for message attributes.
     * 
     * @return message attributes
     */
    const std::unique_ptr<MessageAttributes>&
    getMessageAttributesReference()
    {
        return (m_messageAttributes);
    };

protected:

    bool
    parseAddressedAttributedMessageStringAndSetFields(const std::string delimitedString)
    {
        std::string::size_type endOfAddressDelimIndex = delimitedString.find(*(s_addressAttributesDelimiter().c_str()));
        if (endOfAddressDelimIndex == std::string::npos
            || endOfAddressDelimIndex > (delimitedString.length() - s_minimumDelimitedAddressAttributeMessageStringLength))
        {
            UXAS_LOG_ERROR(s_typeName(), "::parseAddressedAttributedMessageStringAndSetFields failed to parse address from delimited string ", delimitedString);
            m_isValid = false;
            return (m_isValid);
        }
        
        std::string::size_type endOfMessageAttributesDelimIndex = delimitedString.find(*(s_addressAttributesDelimiter().c_str()), (endOfAddressDelimIndex + 1));
        if (endOfMessageAttributesDelimIndex == std::string::npos)
        {
            UXAS_LOG_ERROR(s_typeName(), "::parseAddressedAttributedMessageStringAndSetFields failed to parse message attribute string from delimited string ", delimitedString);
            m_isValid = false;
            return (m_isValid);
        }
        else if (endOfMessageAttributesDelimIndex == (delimitedString.length() - 1))
        {
            UXAS_LOG_ERROR(s_typeName(), "::parseAddressedAttributedMessageStringAndSetFields payload must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        m_messageAttributes = uxas::stduxas::make_unique<MessageAttributes>();
        if (!m_messageAttributes->setAttributesFromDelimitedString(
            delimitedString.substr(endOfAddressDelimIndex + 1, endOfMessageAttributesDelimIndex - (endOfAddressDelimIndex + 1))))
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAttributesAndPayload failed to initialize message attributes");
            m_isValid = false;
            return (m_isValid);
        }

        m_address.clear();
        m_payload.clear();
        m_address = delimitedString.substr(0, endOfAddressDelimIndex);
        m_payload = delimitedString.substr(endOfMessageAttributesDelimIndex + 1, delimitedString.length() - (endOfMessageAttributesDelimIndex + 1));
        m_string = delimitedString;
        m_isValid = true;
        return (m_isValid);
    };

    static std::string s_emptyString;
    std::unique_ptr<MessageAttributes> m_messageAttributes;

};

}; //namespace data
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_DATA_ADDRESSED_ATTRIBUTED_MESSAGE_H */

/** DESIGN NOTES
         address (notional example values: "uxas.project.isolate.IntruderAlert", "eId12sId14", "uxas.roadmonitor")
         contentType (e.g., "lmcp", "json", "xml")
         descriptor (e.g., "afrl.cmasi.AirVehicleState" if contentType="lmcp" or a json content descriptor; intent is some flexibility on values depending on contentType)
         senderGroup (notional example values: "fusion", "fusion.operator.sensor", "uxas", "agent", "uxas.roadmonitor")
         senderEntityId
         senderServiceId
         payload
 */
