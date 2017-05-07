// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_XML_UTIL_H
#define UXAS_COMMON_XML_UTIL_H

#include <string>

namespace uxas
{
namespace common
{

class XmlUtil
{
public:

    static const std::string&
    s_typeName() { static std::string s_string("XmlUtil"); return (s_string); };

    XmlUtil() { };

private:

    /** \brief Copy construction not permitted */
    XmlUtil(XmlUtil const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(XmlUtil const&) = delete;

public:
    
    static void
    escapeXmlQuoteApostropheChars(std::string& xml)
    {
        while (true)
        {
            std::string::size_type idx = xml.rfind("\"");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 1, "&quot;");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind("'");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 1, "&apos;");
        }
    };

    //" &quot; ' &apos; < &lt; > &gt; & &amp;
    static void
    escapeXmlAmpersandLessThanGreaterThanChars(std::string& xml)
    {
        while (true)
        {
            std::string::size_type idx = xml.rfind("&");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 1, "&amp;");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind("<");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 1, "&lt;");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind(">");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 1, "&gt;");
        }
    };

    static void
    escapeXmlChars(std::string& xml)
    {
        escapeXmlAmpersandLessThanGreaterThanChars(xml);
        escapeXmlQuoteApostropheChars(xml);
    };
    
    static void
    unescapeXmlQuoteApostropheChars(std::string& xml)
    {
        while (true)
        {
            std::string::size_type idx = xml.rfind("&quot;");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 6, "\"");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind("&apos;");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 6, "'");
        }
    };

    //" &quot; ' &apos; < &lt; > &gt; & &amp;
    static void
    unescapeXmlAmpersandLessThanGreaterThanChars(std::string& xml)
    {
        while (true)
        {
            std::string::size_type idx = xml.rfind("&lt;");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 4, "<");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind("&gt;");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 4, ">");
        }
        while (true)
        {
            std::string::size_type idx = xml.rfind("&amp;");
            if (idx == std::string::npos)
            {
                break;
            }
            xml.replace(idx, 5, "&");
        }
    };

    static void
    unescapeXmlChars(std::string& xml)
    {
        unescapeXmlQuoteApostropheChars(xml);
        unescapeXmlAmpersandLessThanGreaterThanChars(xml);
    };
    
};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_XML_UTIL_H */
