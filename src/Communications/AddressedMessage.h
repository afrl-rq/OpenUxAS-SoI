// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_MESSAGE_DATA_ADDRESSED_MESSAGE_H
#define UXAS_MESSAGE_DATA_ADDRESSED_MESSAGE_H

#include "UxAS_Log.h"
#include "UxAS_StringUtil.h"

#include <string>
#include <cstdint>

namespace uxas
{
namespace communications
{
namespace data
{

/** \class AddressedMessage
 * 
 * \par Description:
 * Data object containing message address and payload.
 * 
 * \n
 */
class AddressedMessage
{
public:
    //address$payload
    uint32_t s_minimumDelimitedAddressMessageStringLength{3};

    /**
     * s_addressAttributesDelimiter character (must not be present within address)
     * @return 
     */
    static std::string&
    s_addressAttributesDelimiter() { static std::string s_string("$"); return (s_string); };

    /**
     * s_fieldDelimiter character
     * @return 
     */
    static std::string&
    s_fieldDelimiter() { static std::string s_string("|"); return (s_string); };

    static bool
    isValidAddress(const std::string& address)
    {
        if (address.length() < 1)
        {
            UXAS_LOG_ERROR(s_typeName(), "::isValidAddress address must be non-empty");
            return (false);
        }
        else if (address.find(*(s_addressAttributesDelimiter().c_str())) != std::string::npos)
        {
            UXAS_LOG_ERROR(s_typeName(), "::isValidAddress address cannot contain delimiter character ", s_addressAttributesDelimiter());
            return (false);
        }

        return (true);
    };

    static const std::string&
    s_typeName() { static std::string s_string("AddressedMessage"); return (s_string); };

    AddressedMessage() { };

    virtual ~AddressedMessage() { }

    bool
    setAddressAndPayload(const std::string address, const std::string payload)
    {
        if (!isValidAddress(address))
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

        m_address.clear();
        m_payload.clear();
        
        m_address = address;
        m_payload = payload;
        
        m_string = m_address + s_addressAttributesDelimiter() + m_payload;
        
        m_isValid = true;
        return (m_isValid);
    };

    bool
    setAddressAndPayloadFromDelimitedString(const std::string delimitedString)
    {
        if (delimitedString.length() >= s_minimumDelimitedAddressMessageStringLength)
        {
            return (parseAddressedMessageStringAndSetFields(std::move(delimitedString)));
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::setAddressAndPayloadFromDelimitedString delimited string length must be >= ", s_minimumDelimitedAddressMessageStringLength);
            m_isValid = false;
            return (m_isValid);
        }
    };

    bool
    isValid()
    {
        return m_isValid;
    };

    /** \brief Messaging address used by message system to deliver message to 
     * appropriate recipients.  Example values: "afrl.cmasi.AirVehicleState" 
     * (LMCP full type name) for case of LMCP object broadcast or "e14s12" for 
     * case of uni-cast to a specific service (e.g., service with ID 12 hosted 
     * by entity with ID 14). Cannot be an empty string. 
     * 
     * @return message address
     */
    const std::string&
    getAddress() const
    {
        return m_address;
    };

    /** \brief Data payload to be transported.
     * 
     * @return data string sent/received via message system.
     */
    const std::string&
    getPayload() const
    {
        return m_payload;
    };

    /** \brief Message address and payload combined into a single, delimited string.
     * 
     * @return Message string consisting of concatenated address and payload.
     */
    virtual
    const std::string&
    getString() const
    {
        return (m_string);
    };

protected:

    bool
    parseAddressedMessageStringAndSetFields(const std::string delimitedString)
    {
        std::string::size_type endOfAddressDelimIndex = delimitedString.find(*(s_addressAttributesDelimiter().c_str()));
        if (endOfAddressDelimIndex != std::string::npos
            && endOfAddressDelimIndex <= (delimitedString.length() - s_minimumDelimitedAddressMessageStringLength)) // delimiter found and payload size > 0
        {
            std::string address = delimitedString.substr(0, endOfAddressDelimIndex);
            std::string payload = delimitedString.substr(endOfAddressDelimIndex + 1, delimitedString.length() - (endOfAddressDelimIndex + 1));
            return (setAddressAndPayload(std::move(address), std::move(payload)));
        }
        else
        {
            UXAS_LOG_ERROR(s_typeName(), "::parseAddressedMessageStringAndSetFields delimited string must contain delimiter and have non-empty payload");
            m_isValid = false;
            return (m_isValid);
        }
    };

    bool m_isValid{false};
    std::string m_string;
    std::string m_address;
    std::string m_payload;

};

}; //namespace data
}; //namespace communications
}; //namespace uxas

#endif /* UXAS_MESSAGE_DATA_ADDRESSED_MESSAGE_H */
