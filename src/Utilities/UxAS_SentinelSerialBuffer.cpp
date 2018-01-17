// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "UxAS_SentinelSerialBuffer.h"

#include "UxAS_Log.h"

#include "stdUniquePtr.h"
#include "UxAS_StringUtil.h"

#include <iostream>
#include <sstream>
#include <queue>

namespace uxas
{
namespace common
{

uint32_t
SentinelSerialBuffer::calculateChecksum(const std::string& str)
{
    uint32_t chksum = 0;
    uint32_t sz = (str.size() > UINT32_MAX ? UINT32_MAX : str.size());
    const uint8_t* bytes = reinterpret_cast<const uint8_t*> (str.c_str());
    for (uint32_t ii = 0; ii < sz; ii++)
    {
        chksum += bytes[ii];
    }
    return chksum;
};

std::string
SentinelSerialBuffer::createSentinelizedString(const std::string& data)
{
    std::unique_ptr<std::string> detectedSentinelBaseStrings = getDetectSentinelBaseStringsMessage(data);
    if (detectedSentinelBaseStrings)
    {
        UXAS_LOG_INFORM(s_typeName(), "::createSentinelizedString creating payload string containing sentinel substrings.  ", detectedSentinelBaseStrings->c_str());
    }
    return (getSerialSentinelBeforePayloadSize() + std::to_string(data.size())
             + getSerialSentinelAfterPayloadSize() + data + getSerialSentinelBeforeChecksum()
             + std::to_string(calculateChecksum(data)) + getSerialSentinelAfterChecksum());
};

std::unique_ptr<std::string>
SentinelSerialBuffer::getDetectSentinelBaseStringsMessage(const std::string& data)
{
    //TODO - simplify
    std::unique_ptr<std::string> detectMsg = uxas::stduxas::make_unique<std::string>();
    auto befPayloadSzBase = data.find(getSerialSentinelBeforePayloadSizeBase());
    auto aftPayloadSzBase = data.find(getSerialSentinelAfterPayloadSizeBase());
    auto befChecksumBase = data.find(getSerialSentinelBeforeChecksumBase());
    auto aftChecksumBase = data.find(getSerialSentinelAfterChecksumBase());
    if (befPayloadSzBase != std::string::npos)
    {
        detectMsg = uxas::stduxas::make_unique<std::string>();
        detectMsg->append("Found `" + getSerialSentinelBeforePayloadSizeBase() + "` substring in position " + std::to_string(befPayloadSzBase));
    }
    if (aftPayloadSzBase != std::string::npos)
    {
        if (!detectMsg)
        {
            detectMsg = uxas::stduxas::make_unique<std::string>();
            detectMsg->append("Found `" + getSerialSentinelAfterPayloadSizeBase() + "` substring in position " + std::to_string(aftPayloadSzBase));
        }
        else
        {
            detectMsg->append("; found `" + getSerialSentinelAfterPayloadSizeBase() + "` substring in position " + std::to_string(aftPayloadSzBase));
        }
    }
    if (befChecksumBase != std::string::npos)
    {
        if (!detectMsg)
        {
            detectMsg = uxas::stduxas::make_unique<std::string>();
            detectMsg->append("Found `" + getSerialSentinelBeforeChecksumBase() + "` substring in position " + std::to_string(befChecksumBase));
        }
        else
        {
            detectMsg->append("; found `" + getSerialSentinelBeforeChecksumBase() + "` substring in position " + std::to_string(befChecksumBase));
        }
    }
    if (aftChecksumBase != std::string::npos)
    {
        if (!detectMsg)
        {
            detectMsg = uxas::stduxas::make_unique<std::string>();
            detectMsg->append("Found `" + getSerialSentinelAfterChecksumBase() + "` substring in position " + std::to_string(aftChecksumBase));
        }
        else
        {
            detectMsg->append("; found `" + getSerialSentinelAfterChecksumBase() + "` substring in position " + std::to_string(aftChecksumBase));
        }
    }
    return (detectMsg);
};

std::string
SentinelSerialBuffer::getNextPayloadString(const std::string& newDataChunk)
{
    UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString BEFORE appending [newDataChunk]", newDataChunk);
    UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString BEFORE append [m_data]", m_data);
    m_data.append(newDataChunk);
    UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString AFTER  append [m_data]", m_data);
    auto aftChecksum = m_data.find(getSerialSentinelAfterChecksum());
    if (aftChecksum == std::string::npos)
    {
        UXAS_LOG_INFORM(s_typeName(), "::getNextPayloadString does not contain complete data segment");
        return std::string("");
    }
    auto inspectLength = aftChecksum + getSerialSentinelAfterChecksumSize();
    bool isValid{true};
    auto befChecksum = m_data.rfind(getSerialSentinelBeforeChecksum(), aftChecksum);
    if (befChecksum == std::string::npos)
    {
        isValid = false;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString before-checksum marker is missing");
    }
    auto aftPayloadSz = m_data.rfind(getSerialSentinelAfterPayloadSize(), befChecksum);
    if (aftPayloadSz == std::string::npos)
    {
        isValid = false;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString after-payload marker is missing");
    }
    auto befPayloadSz = m_data.rfind(getSerialSentinelBeforePayloadSize(), aftPayloadSz);
    if (befPayloadSz == std::string::npos)
    {
        isValid = false;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString before-payload marker is missing");
    }
    if (!isValid)
    {
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString erasing invalid data segment: ", m_data.substr(0, inspectLength));
        m_data.erase(0, inspectLength);
        UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString buffer contents (after erasure): ", m_data);
        return std::string("");
    }

    auto totalLen = aftChecksum + getSerialSentinelAfterChecksumSize() - befPayloadSz;
    std::string wholeStr = m_data.substr(befPayloadSz, totalLen);
    m_data.erase(befPayloadSz, totalLen);
    if (befPayloadSz > 0)
    {
        // disregard data and log
        m_disregardedDataCount++;
        std::string invalidData = m_data.substr(0, befPayloadSz);
        m_data.erase(0, befPayloadSz);
        std::unique_ptr<std::string> detectedSentinelBaseStrings = getDetectSentinelBaseStringsMessage(invalidData);
        if (detectedSentinelBaseStrings)
        {
            UXAS_LOG_INFORM(s_typeName(), "::getNextPayloadString detected partial sentinel markers in disregarded data: ", detectedSentinelBaseStrings->c_str());
        }
        UXAS_LOG_INFORM(s_typeName(), "::getNextPayloadString erased disregarded data from front of data queue: ", invalidData);

        // update indices for use with valid data
        aftPayloadSz = aftPayloadSz - befPayloadSz;
        befChecksum = befChecksum - befPayloadSz;
        aftChecksum = aftChecksum - befPayloadSz;
        befPayloadSz = 0;
    }

    std::string payloadSzStr = wholeStr.substr(getSerialSentinelBeforePayloadSizeSize(), aftPayloadSz - getSerialSentinelBeforePayloadSizeSize());
    UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::getNextPayloadString payloadSzStr=", payloadSzStr);
    std::string chksumStr = wholeStr.substr(befChecksum + getSerialSentinelBeforeChecksumSize(), aftChecksum - befChecksum - getSerialSentinelBeforeChecksumSize());
    UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::getNextPayloadString chksumStr=", chksumStr);
    
    bool isValidPayloadSzStr = true;
    if (payloadSzStr.find_first_not_of(getValidIntegerDigits()) != std::string::npos)
    {
        isValidPayloadSzStr = false;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString detected invalid payload size string: ", payloadSzStr);
    }
    bool isValidChecksumStr = true;
    if (chksumStr.find_first_not_of(getValidIntegerDigits()) != std::string::npos)
    {
        isValidChecksumStr = false;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString detected invalid checksum string: ", chksumStr);
    }

    if (isValidPayloadSzStr && isValidChecksumStr)
    {
        std::string payload = wholeStr.substr(aftPayloadSz + getSerialSentinelAfterPayloadSizeSize(), befChecksum - aftPayloadSz - getSerialSentinelAfterPayloadSizeSize());
        UXAS_LOG_DEBUG_VERBOSE(s_typeName(), "::getNextPayloadString payload=", payload);

        if (static_cast<int>(payload.size()) == std::stoi(payloadSzStr))
        {
            uint32_t calcChksum = calculateChecksum(payload);
            if (static_cast<int>(calcChksum) == std::stoi(chksumStr))
            {
                m_validDeserializeCount++;
                UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString m_validDeserializeCount=", m_validDeserializeCount);
                UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString m_invalidDeserializeCount=", m_invalidDeserializeCount);
                return payload;
            }
            else
            {
                m_invalidDeserializeCount++;
                UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString ignoring invalid data segment since calculated checksum=", calcChksum, " does not equal chksumStr=", chksumStr, " for payload=", payload);
            }
        }
        else
        {
            m_invalidDeserializeCount++;
            UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString ignoring invalid data segment since calculated payload size=", payload.size(), " does not equal payloadSzStr=", payloadSzStr, " for payload=", payload);
        }
    }
    else
    {
        m_invalidDeserializeCount++;
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString ignoring invalid data segment having invalid ", 
                 (!isValidPayloadSzStr && !isValidChecksumStr ? "payload size and checksum strings" 
                : (isValidPayloadSzStr ? "payload size string" : "checksum string")));
    }

    UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString m_validDeserializeCount=", m_validDeserializeCount);
    if (m_invalidDeserializeCount < 1)
    {
        UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString m_invalidDeserializeCount=", m_invalidDeserializeCount);
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), "::getNextPayloadString m_invalidDeserializeCount=", m_invalidDeserializeCount);
    }
    
    if (m_disregardedDataCount < 1)
    {
        UXAS_LOG_DEBUGGING(s_typeName(), "::getNextPayloadString m_disregardedDataCount=", m_disregardedDataCount);
    }
    else
    {
        UXAS_LOG_INFORM(s_typeName(), "::getNextPayloadString m_disregardedDataCount=", m_disregardedDataCount);
    }

    return std::string("");
};

}; //namespace common
}; //namespace uxas
