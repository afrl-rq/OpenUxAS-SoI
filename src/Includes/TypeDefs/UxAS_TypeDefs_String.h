// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UxAS_TypeDefs_String.h
 * Author: steve
 *
 * Created on December 10, 2013, 3:19 PM
 */

#ifndef UXAS_TYPEDEFS_STRING_H
#define    UXAS_TYPEDEFS_STRING_H

//#ifndef __STDC_FORMAT_MACROS
//#define __STDC_FORMAT_MACROS  // PRId32,  printf("test uint64_t : %" PRIu64 "\n", ui64);
//#endif
//#include <cinttypes> // define new print formatting 

#include <string>
#include <vector>
#include <deque>
#include <unordered_map>
#include <cstdint>      //int32_t
#include <memory>   //std::shard_ptr

namespace n_Typedefs
{
    typedef std::shared_ptr<std::string> PTR_STRING_t;

    typedef std::unordered_map<std::string,PTR_STRING_t> UM_STRING_PTR_STRING_t;
    typedef std::unordered_map<std::string,PTR_STRING_t>::iterator UM_STRING_PTR_STRING_IT_t;
    typedef std::unordered_map<std::string,PTR_STRING_t>::const_iterator UM_STRING_PTR_STRING_CONST_IT_t;

    typedef std::unordered_map<std::string,uint32_t> UM_STRING_UI32_t;
    typedef std::unordered_map<std::string,uint32_t>::iterator UM_STRING_UI32_IT_t;
    typedef std::unordered_map<std::string,uint32_t>::const_iterator UM_STRING_UI32_CONST_IT_t;

    typedef std::unordered_multimap<std::string,uint32_t> UMM_STRING_UI32_t;
    typedef std::unordered_multimap<std::string,uint32_t>::iterator UMM_STRING_UI32_IT_t;
    typedef std::unordered_multimap<std::string,uint32_t>::const_iterator UMM_STRING_UI32_CONST_IT_t;

    typedef std::vector<std::string> V_STRING_t;
    typedef std::vector<std::string>::iterator V_STRING_IT_t;
    typedef std::vector<std::string>::const_iterator V_STRING_CONST_IT_t;
     
    typedef std::vector<PTR_STRING_t> V_PTR_STRING_t;
    typedef std::vector<PTR_STRING_t>::iterator V_PTR_STRING_IT_t;
    typedef std::vector<PTR_STRING_t>::const_iterator V_PTR_STRING_CONST_IT_t;
     
    typedef std::deque<PTR_STRING_t> DQ_PTR_STRING_t;
    typedef std::deque<PTR_STRING_t>::iterator DQ_PTR_STRING_IT_t;
    typedef std::deque<PTR_STRING_t>::const_iterator DQ_PTR_STRING_CONST_IT_t;
     
    typedef std::unordered_map<std::string,std::string> UM_STRING_STRING_t;
    typedef std::unordered_map<std::string,std::string>::iterator UM_STRING_STRING_IT_t;
    typedef std::unordered_map<std::string,std::string>::const_iterator UM_STRING_STRING_CONST_IT_t;
     
}       //namespace n_Typedefs



#endif    /* UXAS_TYPEDEFS_STRING_H */

