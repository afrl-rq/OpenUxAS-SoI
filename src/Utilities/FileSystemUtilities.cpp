// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   FileSystemUtilities.cpp
 * Author: steve
 *
 * Created on January 13, 2014, 9:19 PM
 */



#include "TimeUtilities.h"

#include "FileSystemUtilities.h"

#include "UxAS_Log.h"

#include "Constants/Constants_FileSystem.h"

//BOOST FILESYSTEM
#include "boost/filesystem/fstream.hpp"
#include "boost/filesystem/operations.hpp"
#include "boost/regex.hpp"

#include <fstream>      //std::ofstream


namespace uxas
{
namespace common
{
namespace utilities
{

    bool c_FileSystemUtilities::bFindUniqueFileName(const std::string& strFileNameBase, const std::string& strPath,std::string& strPathFileName, const bool& isAddExtension)
    {
    	std::stringstream sstrErrors;
        const bool bSuccess = bCreateDirectory(strPath, sstrErrors);
        if (bSuccess)
        {
            // check to see how many files are in directory
            size_t szNumberFiles(0);
            boost::filesystem::directory_iterator end_itr; // Default ctor yields past-the-end
            // count the number of entries in the directory (could just count files)
            for (boost::filesystem::directory_iterator itDirectorySub(strPath); itDirectorySub != end_itr; ++itDirectorySub)
            {
                szNumberFiles++;
            }

            std::string strWorkingPathFile;
            
            szNumberFiles++;
            std::stringstream sstrNewFileName;
            sstrNewFileName << std::setfill('0') << std::setw(n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()) << szNumberFiles
                    << "_" << strFileNameBase;
            if(isAddExtension)
            {
#ifdef _WIN32
                sstrNewFileName << ".xml";
#else
                sstrNewFileName 
                        << "_" << strFileNameBase << "_" << std::setprecision(5) << uxas::common::utilities::c_TimeUtilities::strGetTimeNow();
#endif
            }
            strPathFileName = strPath + "/" + sstrNewFileName.str();

        } //if (bCreateDirectory(strPath, sstrErrors))

        return (bSuccess);
    }
    
    bool c_FileSystemUtilities::bSaveStringToUniqueFile(const std::string& strSaveString, const std::string& strFileNameBase, const std::string& strPath, const bool& isAddExtension)
    {
        bool bSuccess(true);
        std::stringstream sstrErrors;
        
        std::string pathFileName;
        bSuccess = bFindUniqueFileName(strFileNameBase,strPath,pathFileName,isAddExtension);
        if (bSuccess)
        {
            std::ofstream ofsLogFile(pathFileName.c_str(), (std::ios_base::out | std::ios_base::app));
            ofsLogFile << strSaveString << std::endl;
            ofsLogFile.close();
        } //if (bCreateDirectory(strPath, sstrErrors))

        return (bSuccess);
    }
    
    bool c_FileSystemUtilities::bSaveStringToFile(const std::string& strSaveString, const std::string& strFileNameBase, const std::string& strPath,
            const std::string& strSubDirectoryPrefix, const uint32_t& ui32FilesPerSubdirectory, std::stringstream& sstrErrors)
    {
        bool bSuccess(true);

        //std::cout << "IIIII c_FileSystemUtilities::bSaveStringToFile-> strPath[" << strPath << "]" << "\n";
        // if the path does not exist, then create it
        if (bCreateDirectory(strPath, sstrErrors))
        {
            // check directories/files with a FILE_NAME_NUMBER_DIGITS digit prefix
            std::stringstream sstrFilter;
            sstrFilter << "\\d{" << n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits() << "}_.*";
            const boost::regex my_filter(sstrFilter.str());
            boost::smatch what;

            boost::filesystem::directory_iterator itDirectory(strPath);
            boost::filesystem::directory_iterator end_itr; // Default ctor yields past-the-end
            boost::filesystem::path pthPathSave; // save the directory with the largest "numerical" name
            int iDirectoryNumberMax = 0;
            bool bAddNewDirectory(false);

            //find the subdirectory that has the largest number prefix
            for (; itDirectory != end_itr; itDirectory++)
            {
                if (boost::filesystem::is_directory(itDirectory->status()))
                {
                    if (boost::regex_match(itDirectory->path().filename().string(), what, my_filter))
                    {
                        int iDirectoryNumberTemp{0};
                        try
                        {
                            iDirectoryNumberTemp = std::stoi(itDirectory->path().filename().string().substr(0, n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()));
                        }
                        catch (std::exception& ex)
                        {
                            UXAS_LOG_ERROR("c_FileSystemUtilities","::GetTaskIdFromStringId failed to directory prefix in itDirectory->path() [",itDirectory->path().filename().string(),"]; EXCEPTION: ",ex.what());
                        }
                        if (iDirectoryNumberTemp > iDirectoryNumberMax)
                        {
                            iDirectoryNumberMax = iDirectoryNumberTemp;
                            pthPathSave = itDirectory->path();
                        }
                    }
                }
            }

            std::string strWorkingPathFile(strPath);
            if (!pthPathSave.empty())
            {
                // found largest directory, now check to see how many files are in it
                size_t szNumberFiles(0);
                // count the number of entries in the directory (could just count files)
                for (boost::filesystem::directory_iterator itDirectorySub(pthPathSave); itDirectorySub != end_itr; ++itDirectorySub)
                {
                    szNumberFiles++;
                }

                if (szNumberFiles >= ui32FilesPerSubdirectory)
                {
                    bAddNewDirectory = true;
                }
                else
                {
                    szNumberFiles++;
                    std::stringstream sstrNewFileName;
                    sstrNewFileName << std::setfill('0') << std::setw(n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()) << szNumberFiles
#ifdef _WIN32
                            << "_" << strFileNameBase << ".xml";
#else
                            << "_" << strFileNameBase << "_" << uxas::common::utilities::c_TimeUtilities::strGetTimeNow();
#endif
                    strWorkingPathFile = pthPathSave.generic_string() + "/" + sstrNewFileName.str();
                }
            }
            else //if(itDirectory != end_itr)
            {
                bAddNewDirectory = true;
            } //if(itDirectory != end_itr)

            if (bAddNewDirectory)
            {
                std::stringstream sstrNewFileName;
                sstrNewFileName << std::setfill('0') << std::setw(n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()) << 1
#ifdef _WIN32
                        << "_" << strFileNameBase << ".xml";
#else
                        << "_" << strFileNameBase << "_" << uxas::common::utilities::c_TimeUtilities::strGetTimeNow();
#endif
                iDirectoryNumberMax++;
                std::stringstream sstrNewSubDirectoryName;
                sstrNewSubDirectoryName << std::setfill('0') << std::setw(n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()) << iDirectoryNumberMax << "_" << strSubDirectoryPrefix;
                strWorkingPathFile = strPath + sstrNewSubDirectoryName.str();
                if (!bCreateDirectory(strWorkingPathFile, sstrErrors))
                {
                    bSuccess = false;
                    std::cout << "ERROR:: c_FileSystemUtilities::bSaveStringToFile:: Create new subdirectory [" << sstrErrors.str() << "]" << std::endl;
                }
                strWorkingPathFile = strPath + sstrNewSubDirectoryName.str() + "/" + sstrNewFileName.str();
            }

            // if everything went well, write the file to the directory
            if (bSuccess)
            {
                std::ofstream ofsLogFile(strWorkingPathFile.c_str(), (std::ios_base::out | std::ios_base::app));
                ofsLogFile << strSaveString << std::endl;
                ofsLogFile.close();

                //std::cout << "TEST:: c_FileSystemUtilities::bSaveStringToFile:strWorkingPathFile[" << strWorkingPathFile << std::endl;
            }


        } //if(bCreateDirectory(strPath,sstrErrors))
        return (bSuccess);
    }

    bool c_FileSystemUtilities::bCreateUniqueDirectory(const std::string& strDataPath, const std::string& strDirectoryPrefix, std::string& strNewPath, std::stringstream & sstreamErrors)
    {
        bool bSuccess(true);

        //std::cout << "IIIII c_FileSystemUtilities::bCreateUniqueDirectory-> strDataPath[" << strDataPath << "]" << "\n";
        bSuccess = bCreateDirectory(strDataPath, sstreamErrors);

        if (bSuccess)
        {
            boost::filesystem::directory_iterator itDirectory(strDataPath);
            boost::filesystem::directory_iterator end_itr; // Default ctor yields past-the-end
            int iDirectoryNumberMax = 0;

            // check directories with a FILE_NAME_NUMBER_DIGITS digit prefix
            std::stringstream sstrFilter;
            sstrFilter << "\\d{" << n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits() << "}_.*";
            const boost::regex my_filter(sstrFilter.str());
            boost::smatch what;

            for (; itDirectory != end_itr; itDirectory++)
            {
                if (boost::filesystem::is_directory(itDirectory->status()))
                {
                    if (boost::regex_match(itDirectory->path().filename().string(), what, my_filter))
                    {
                        int iDirectoryNumberTemp{0};
                        try
                        {
                            iDirectoryNumberTemp = std::stoi(itDirectory->path().filename().string().substr(0, n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()));
                        }
                        catch (std::exception& ex)
                        {
                            UXAS_LOG_ERROR("c_FileSystemUtilities","::GetTaskIdFromStringId failed to directory prefix in itDirectory->path() [",itDirectory->path().filename().string(),"]; EXCEPTION: ",ex.what());
                        }
                        if (iDirectoryNumberTemp > iDirectoryNumberMax)
                        {
                            iDirectoryNumberMax = iDirectoryNumberTemp;
                        }
                    }
                }
            }
            iDirectoryNumberMax++;
            std::stringstream sstrNewDirectoryName;
            sstrNewDirectoryName << std::setfill('0') << std::setw(n_Const::c_Constants_FileSystem::ui32GetNumberPrefixDigits()) << iDirectoryNumberMax << "_"
#ifdef _WIN32
                    << strDirectoryPrefix << "/";
#else
                    << strDirectoryPrefix << "_"
                    << uxas::common::utilities::c_TimeUtilities::strGetTimeNow()
                    << "/";
#endif
            strNewPath = strDataPath + sstrNewDirectoryName.str();
            bSuccess = bCreateDirectory(strNewPath, sstreamErrors);
        } //if(bSuccess)

        return (bSuccess);
    };

    bool c_FileSystemUtilities::bCreateDirectory(const std::string& strDataPath, std::stringstream & sstrErrors)
    {
        bool bSuccess(true);

        //std::cout << "IIIII c_FileSystemUtilities::bCreateDirectory-> strDataPath[" << strDataPath << "]" << "\n";
        // make sure path exists
        if (!boost::filesystem::exists(strDataPath))
        {
            boost::system::error_code ec;
            boost::filesystem::path pthDataPathLocal(strDataPath);
            try
            {
                boost::filesystem::create_directories(pthDataPathLocal, ec);
                if (ec != boost::system::errc::success)
                {
                    sstrErrors << "Failed to create directory: [" << pthDataPathLocal.generic_string() << "] ERROR:[" << ec.message() << "]" << std::endl;
                    std::cout << "IIIII sstrErrors[" << sstrErrors.str() << "]" << "\n";
                    bSuccess = false;
                }
            }
            catch (boost::filesystem::filesystem_error &e)
            {
                //std::cerr << e.what() << std::endl; 
                sstrErrors << "Failed to create directory: [" << pthDataPathLocal.generic_string() << "] ERROR:[" << e.what() << "]" << std::endl;
                bSuccess = false;
            }
        } //if (!boost::filesystem::exists(strDataPath))
        return (bSuccess);
    };


}       //namespace utilities
}       //namespace common
}       //namespace uxas
