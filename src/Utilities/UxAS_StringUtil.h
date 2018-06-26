// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_STRING_UTIL_H
#define UXAS_COMMON_STRING_UTIL_H

#include <string>
#include <sstream>
#include <vector>

namespace uxas
{
namespace common
{

class StringUtil
{
public:

    /** \brief Static function that returns a new string vector containing 
     * substrings found within provided string.  Empty string tokens are retained.
     * 
     * @param value String having substrings delimited by delimiter character.
     * @param delimiter Character used as boundary between substrings.
     * @param maxTokenCount Maximum count of strings returned in string vector (optional).
     * @return 
     */
    static
    std::vector<std::string>
    split(const std::string &value, char delimiter, uint32_t maxTokenCount = UINT32_MAX, bool isAppendToBack = false)
    {
        std::vector<std::string> tokens;
        std::stringstream ss(value);
        std::string item;
        uint32_t emplaceCount = 0;
        while (std::getline(ss, item, delimiter))
        {
            if (emplaceCount < maxTokenCount)
            {
                tokens.emplace_back(item);
            }
            else
            {
                tokens.back().append(item);
            }

            if (++emplaceCount == maxTokenCount && !isAppendToBack)
            {
                break;
            }
        }
        if (emplaceCount < maxTokenCount && 
            value.find_last_of(delimiter) == (value.size()-1))
        {
            tokens.emplace_back("");
        }
        return tokens;
    };
    
    static inline void ReplaceAll(std::string &str, const std::string& from, const std::string& to)
    {
        size_t start_pos = 0;
        while((start_pos = str.find(from, start_pos)) != std::string::npos) {
            str.replace(start_pos, from.length(), to);
            start_pos += to.length();
        }
    };

};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_STRING_UTIL_H */
