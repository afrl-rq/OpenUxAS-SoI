// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#ifndef UXAS_COMMON_FILE_UTIL_H
#define UXAS_COMMON_FILE_UTIL_H

#include "UxAS_Log.h"
#include "UxAS_StringUtil.h"

#include <fstream>
#include <string>
#include <vector>

#define EXTRACT_FILES_NIX_DIR_DELIMITER '/'

namespace uxas
{
namespace common
{

class FileUtil
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("FileUtil");
        return (s_string);
    };

    FileUtil() { };

private:

    static const std::string&
    getDefaultDelimiter()
    {
        static std::string s_string("+=!%+=!%+=!%+=!%");
        return (s_string);
    };

    static const std::string&
    getValidIntegerDigits()
    {
        static std::string s_string("1234567890");
        return (s_string);
    };

    /** \brief Copy construction not permitted */
    FileUtil(FileUtil const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(FileUtil const&) = delete;

public:

    static std::vector<std::string>
    readTextLines(const std::string& inputFilePath)
    {
        std::vector<std::string> lines;
        std::ifstream inFile(inputFilePath);
        if (inFile.is_open())
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::readTextLines open input file [", inputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::readTextLines failed to open input file [", inputFilePath, "]");
            return (std::move(lines));
        }
        std::string oneLine;
        while (std::getline(inFile, oneLine))
        {
            lines.push_back(oneLine);
        }
        return (std::move(lines));
    };

    static bool
    writeTextLines(std::vector<std::string>& textLines, const std::string& outputFilePath)
    {
        std::ofstream outFile(outputFilePath, std::ios::ate);
        if (outFile.is_open())
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::writeTextLines opened output file [", outputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::writeTextLines failed to open output file [", outputFilePath, "]");
            return (false);
        }

        for (auto& line : textLines)
        {
            outFile << line << std::endl;
        }
        
        outFile.close();
        return (true);
    };

    static std::vector<uint8_t>
    readBinaryFile(const std::string& inputFilePath)
    {
        UXAS_LOG_DEBUGGING(s_typeName(), "::readBinaryFile inputFilePath [", inputFilePath, "]");

        std::vector<uint8_t> failedReadZeroBytes;

        // open binary file at the end
        std::ifstream inFile(inputFilePath, std::ios::ate | std::ios::binary);

        if (inFile.is_open())
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::readBinaryFile opened input file [", inputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::readBinaryFile failed to open input file [", inputFilePath, "]");
            return (failedReadZeroBytes);
        }

        // Calculate size
        size_t end = inFile.tellg();
        inFile.seekg(0, std::ios::beg);
        size_t start = inFile.tellg();
        size_t len = end - start;
        if (len > 0)
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::readBinaryFile input file [", inputFilePath, "] has length [", len, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::readBinaryFile input file [", inputFilePath, "] unexpectedly has length [", len, "]");
            return (failedReadZeroBytes);
        }

        std::vector<uint8_t> binaryBytes(len, 0);
        char* buffer = new char[len];
        if (inFile.read(buffer, len))
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::readBinaryFile read input file [", inputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::readBinaryFile failed to read input file [", inputFilePath, "] - inFile.gcount() [", inFile.gcount(), "]");
            return (failedReadZeroBytes);
        }
        
        binaryBytes.assign(buffer, buffer + len);
        inFile.close();
        delete[] buffer;
        return (std::move(binaryBytes));
    };

    static bool
    writeBinaryFile(const std::vector<uint8_t>& bytes, const std::string& outputFilePath)
    {
        std::ofstream outFile(outputFilePath, std::ios::out | std::ofstream::binary); // std::ios::ate ??
        if (outFile.is_open())
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::writeBinaryFile opened output file [", outputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::writeBinaryFile failed to open output file [", outputFilePath, "]");
            return (false);
        }

        if (outFile.write((char*)&bytes[0], bytes.size()))
        {
            UXAS_LOG_DEBUGGING(s_typeName(), "::writeBinaryFile wrote output file [", outputFilePath, "]");
        }
        else
        {
            UXAS_LOG_WARN(s_typeName(), "::writeBinaryFile failed to write output file [", outputFilePath, "] - outFile.rdstate() [", outFile.rdstate(), "]");
            return (false);
        }

        outFile.close();
        
        return (true);
    };
};

}; //namespace common
}; //namespace uxas

#endif /* UXAS_COMMON_FILE_UTIL_H */
        