// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_SENTINEL_SERIAL_BUFFER_H
#define UXAS_COMMON_SENTINEL_SERIAL_BUFFER_H

#include <memory>
#include <string>

namespace uxas
{
namespace common
{

class SentinelSerialBuffer
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("SerialStringSentinel"); return (s_string); };

    // assuming the following strings are never present within the combined string containing payload size, payload and payload checksum
    //      "+="
    //      "=+"
    //      "#@"
    //      "@#"
    //      "!%"
    //      "%!"
    //      "?^"
    //      "^?"
    //
    // 8 char markers:
    // "+=+=+=+=123#@#@#@#@" // lmcpObjPayloadSize
    // "#@#@#@#@abcxyz123!%!%!%!%" // rawPayload
    // "!%!%!%!%789?^?^?^?^" // lmcpObjPayloadChksum
    // "+=+=+=+=123#@#@#@#@abcxyz123!%!%!%!%789?^?^?^?^" // lmcpObjPayloadSize, rawPayload and lmcpObjPayloadChksum (combined into single string)

    static const std::string& 
    getSerialSentinelBeforePayloadSize() { static std::string s_string("+=+=+=+="); return(s_string); };

    static const uint32_t 
    getSerialSentinelBeforePayloadSizeSize() { static const uint32_t s_sz = getSerialSentinelBeforePayloadSize().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelBeforePayloadSizeBase() { static std::string s_string("+="); return(s_string); };

    static const uint32_t 
    getSerialSentinelBeforePayloadSizeBaseSize() { static const uint32_t s_sz = getSerialSentinelBeforePayloadSizeBase().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelAfterPayloadSize() { static std::string s_string("#@#@#@#@"); return(s_string); };

    static const uint32_t 
    getSerialSentinelAfterPayloadSizeSize() { static const uint32_t s_sz = getSerialSentinelAfterPayloadSize().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelAfterPayloadSizeBase() { static std::string s_string("#@"); return(s_string); };

    static const uint32_t 
    getSerialSentinelAfterPayloadSizeBaseSize() { static const uint32_t s_sz = getSerialSentinelAfterPayloadSizeBase().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelBeforeChecksum() { static std::string s_string("!%!%!%!%"); return(s_string); };

    static const uint32_t 
    getSerialSentinelBeforeChecksumSize() { static const uint32_t s_sz = getSerialSentinelBeforeChecksum().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelBeforeChecksumBase() { static std::string s_string("!%"); return(s_string); };

    static const uint32_t 
    getSerialSentinelBeforeChecksumBaseSize() { static const uint32_t s_sz = getSerialSentinelBeforeChecksumBase().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelAfterChecksum() { static std::string s_string("?^?^?^?^"); return(s_string); };

    static const uint32_t 
    getSerialSentinelAfterChecksumSize() { static const uint32_t s_sz = getSerialSentinelAfterChecksum().size(); return(s_sz); };

    static const std::string& 
    getSerialSentinelAfterChecksumBase() { static std::string s_string("?^"); return(s_string); };

    static const uint32_t 
    getSerialSentinelAfterChecksumBaseSize() { static const uint32_t s_sz = getSerialSentinelAfterChecksumBase().size(); return(s_sz); };
    
    static const std::string& 
    getValidIntegerDigits() { static std::string s_string("1234567890"); return(s_string); };

    SentinelSerialBuffer() { };

private:

    /** \brief Copy construction not permitted */
    SentinelSerialBuffer(SentinelSerialBuffer const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(SentinelSerialBuffer const&) = delete;

public:
    
    /**
     * Supports strings containing only ascii characters
     * @param str
     * @return 
     */
    static uint32_t
    calculateChecksum(const std::string& str);
    
    static std::string
    createSentinelizedString(const std::string& data);

    static std::unique_ptr<std::string>
    getDetectSentinelBaseStringsMessage(const std::string& data);

    /**
     * multi-thread safety not implemented
     * @param data
     * @return 
     */
    std::string
    getNextPayloadString(const std::string& newDataChunk);
    
    std::string m_data;
    uint32_t m_validDeserializeCount{0};
    uint32_t m_invalidDeserializeCount{0};
    uint32_t m_disregardedDataCount{0};
    
};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_SENTINEL_SERIAL_BUFFER_H */
