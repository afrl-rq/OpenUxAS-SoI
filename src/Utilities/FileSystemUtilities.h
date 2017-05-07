// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   FileSystemUtilities.h
 * Author: steve
 *
 * Created on January 13, 2014, 9:19 PM
 */

#ifndef FILE_SYSTEM_UTILITIES_H
#define FILE_SYSTEM_UTILITIES_H

#include <cstdint> // uint32_t
#include <string>       //string
#include <sstream>      //stringstream

namespace uxas
{
namespace common
{
namespace utilities
{

    

/*! \class c_FileSystemUtilities
    \brief This class manages access to the files system. It creates unique directories,
 * adds new sub-directories to keep the number of files below a given number, and 
 * add prefixes the files with index numbers .
 * 
 */
    class c_FileSystemUtilities
    {
    public:
        c_FileSystemUtilities(){}; // no constructing
        virtual ~c_FileSystemUtilities() { };

    private:
        c_FileSystemUtilities(const c_FileSystemUtilities& orig) = delete; //no copying
        c_FileSystemUtilities& operator=(const c_FileSystemUtilities&) = delete; //no copying


    public: //static methods

        static bool bFindUniqueFileName(const std::string& strFileNameBase, const std::string& strPath,std::string& strPathFileName, const bool& isAddExtension=true);
        static bool bSaveStringToUniqueFile(const std::string& strSaveString, const std::string& strFileNameBase, const std::string& strPath, const bool& isAddExtension=true);
        static bool bSaveStringToFile(const std::string& strSaveString,const std::string& strFileNameBase,const std::string& strPath,
                                        const std::string& strSubDirectoryPrefix, const uint32_t& ui32FilesPerSubdirectory, std::stringstream& sstreamErrors);
        static bool bCreateUniqueDirectory(const std::string& strDataPath, const std::string& strDirectoryPrefix, std::string& strNewPath, std::stringstream& sstreamErrors);
        static bool bCreateDirectory(const std::string& strDataPath,std::stringstream& sstrErrors);

    }; // c_FileSystemUtilities
    
    
}       //namespace utilities
}       //namespace common
}       //namespace uxas

#endif /* FILE_SYSTEM_UTILITIES_H */

