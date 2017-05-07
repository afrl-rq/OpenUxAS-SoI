// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Constants_FileSystem.h
 * Author: steve
 *
 * Created on January 22, 2013, 2:20 PM
 */

#ifndef CONSTANTS_FILE_SYSTEM_H
#define    CONSTANTS_FILE_SYSTEM_H

#include <cstdint> // uint32_t

namespace n_Const
{   

    /*! \class c_Constants_FileSystem
        \brief this class contains "singleton" constants for the file system functions.

     *  @par Description:
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li>  - 
     * 
     * </ul> @n
     */
class c_Constants_FileSystem
{
public: //constants
    
    // 
/*! @name MessagePassing Strings
 *   
 */
///@{
//! 
    static const uint32_t& ui32GetNumberPrefixDigits(){static uint32_t ui32Digits(4);return(ui32Digits);};
///@}


};

};      //namespace n_UxAS_Constants

#endif    /* CONSTANTS_FILE_SYSTEM_H */

