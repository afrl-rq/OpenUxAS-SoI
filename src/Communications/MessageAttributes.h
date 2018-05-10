// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_DATA_MESSAGE_ATTRIBUTES_H
#define UXAS_MESSAGE_DATA_MESSAGE_ATTRIBUTES_H

#include "AddressedMessage.h"

#include <string>
#include <tuple>

namespace uxas
{
namespace communications
{
namespace data
{

/** \class MessageAttributes
 * 
 * \par Description:
 * Data object containing message attributes.
 * 
 * \n
 */
class MessageAttributes final
{
public:
    //contentType|descriptor|sourceGroup|sourceEntityId|sourceServiceId
    //sourceGroup can be empty string
    uint32_t s_minimumDelimitedAddressAttributeMessageStringLength{8};
    uint32_t s_attributeCount{5};

    static const std::string&
    s_typeName() { static std::string s_string("MessageAttributes"); return (s_string); };

    MessageAttributes() { };

    bool
    setAttributes(const std::string contentType, const std::string descriptor,
                  const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId)
    {
        if (contentType.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes contentType must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        if (descriptor.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes descriptor must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        if (sourceEntityId.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes sourceEntityId must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        if (sourceServiceId.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes sourceServiceId must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        m_contentType.clear();
        m_descriptor.clear();
        m_sourceGroup.clear();
        m_sourceEntityId.clear();
        m_sourceServiceId.clear();
        m_string.clear();
        
        m_contentType = contentType;
        m_descriptor = descriptor;
        m_sourceGroup = sourceGroup;
        m_sourceEntityId = sourceEntityId;
        m_sourceServiceId = sourceServiceId;
        
        m_string = m_contentType + AddressedMessage::s_fieldDelimiter()
                + m_descriptor + AddressedMessage::s_fieldDelimiter()
                + m_sourceGroup + AddressedMessage::s_fieldDelimiter()
                + m_sourceEntityId + AddressedMessage::s_fieldDelimiter()
                + m_sourceServiceId;

        m_isValid = true;
        return (m_isValid);
    };
    
    bool
    updateSourceAttributes(const std::string sourceGroup, const std::string sourceEntityId, const std::string sourceServiceId)
    {
        m_sourceGroup = sourceGroup;
        m_sourceEntityId = sourceEntityId;
        m_sourceServiceId = sourceServiceId;
        
        if (sourceEntityId.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes sourceEntityId must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }

        if (sourceServiceId.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAttributes sourceServiceId must be non-empty");
            m_isValid = false;
            return (m_isValid);
        }
        
        m_string = m_contentType + AddressedMessage::s_fieldDelimiter()
                + m_descriptor + AddressedMessage::s_fieldDelimiter()
                + m_sourceGroup + AddressedMessage::s_fieldDelimiter()
                + m_sourceEntityId + AddressedMessage::s_fieldDelimiter()
                + m_sourceServiceId;
        return (m_isValid);
    };

    bool
    setAttributesFromDelimitedString(const std::string delimitedString)
    {
        if (delimitedString.length() >= s_minimumDelimitedAddressAttributeMessageStringLength)
        {
            return (parseMessageAttributesStringAndSetFields(std::move(delimitedString)));
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAndPayloadFromDelimitedString delimited string length must be >= ", s_minimumDelimitedAddressAttributeMessageStringLength);
            m_isValid = false;
            return m_isValid;
        }
    };

    bool
    isValid()
    {
        return m_isValid;
    };

    /** \brief Content type of payload (e.g., "json", "lmcp", "text", "xml"). 
     * Valid values for content type are a controlled list. Cannot be an empty 
     * string. 
     * 
     * @return content type
     */
    const std::string&
    getContentType() const
    {
        return m_contentType;
    };

    /** \brief Descriptive qualifier for the payload. 
     * Example values: "afrl.cmasi.AirVehicleState" (LMCP full type name) 
     * for case LMCP payload; json qualifying descriptor. Generally, is additional 
     * description of the payload beyond the content type value. Valid values 
     * for descriptor are a controlled list - but less constrained than content 
     * type. TODO REVIEW Cannot be an empty string. 
     * 
     * @return payload qualifying descriptor
     */
    const std::string&
    getDescriptor() const
    {
        return m_descriptor;
    };

    /** \brief Multi-cast address to which the sending service subscribes. Can 
     * be an empty string. 
     * 
     * @return group address
     */
    const std::string&
    getSourceGroup() const
    {
        return m_sourceGroup;
    };

    /** \brief Entity ID of the host of the sending service. 
     * Cannot be an empty string. 
     * 
     * @return UxAS entity ID
     */
    const std::string&
    getSourceEntityId() const
    {
        return m_sourceEntityId;
    };

    /** \brief Service ID of the sending service. Cannot be an empty string. 
     * 
     * @return UxAS entity ID
     */
    const std::string&
    getSourceServiceId() const
    {
        return m_sourceServiceId;
    };

    /** \brief Attribute fields combined into a single, delimited string.
     * 
     * @return concatenated attribute fields.
     */
    const std::string&
    getString() const
    {
        return m_string;
    };

protected:

    bool
    parseMessageAttributesStringAndSetFields(const std::string delimitedString)
    {
        std::vector<std::string> tokens = uxas::common::StringUtil::split(delimitedString, *(AddressedMessage::s_fieldDelimiter().c_str()));
        if (tokens.size() == uxas::communications::data::MessageAttributes::s_attributeCount)
        {
            return (setAttributes(std::move(tokens.at(0)), std::move(tokens.at(1)), std::move(tokens.at(2)), std::move(tokens.at(3)), std::move(tokens.at(4))));
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::parseMessageAttributesStringAndSetFields string must consist of ",  s_attributeCount, " delimited fields");
            m_isValid = false;
            return (m_isValid);
        }
    };

    bool m_isValid{false};
    std::string m_string;
    std::string m_contentType;
    std::string m_descriptor;
    std::string m_sourceGroup;
    std::string m_sourceEntityId;
    std::string m_sourceServiceId;

};

}; //namespace data
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_DATA_MESSAGE_ATTRIBUTES_H */
