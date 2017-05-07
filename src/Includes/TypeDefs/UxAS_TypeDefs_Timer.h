// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UxAS_TypeDefs_Timer.h
 * Author: steve
 *
 * Created on December 10, 2013, 3:14 PM
 */

#ifndef UXAS_TYPEDEFS_TIMER_H
#define    UXAS_TYPEDEFS_TIMER_H

//#ifndef __STDC_FORMAT_MACROS
//#define __STDC_FORMAT_MACROS  // PRId32,  printf("test uint64_t : %" PRIu64 "\n", ui64);
//#endif
//#include <cinttypes> // define new print formatting 

#include <CallbackTimer.h>
#include <memory>       //std::shared_ptr

namespace n_Typedefs
{

    typedef std::shared_ptr<uxas::common::utilities::c_CallbackTimer> PTR_CALLBACK_TIMER_t;
    
}       //namespace n_Typedefs

#endif    /* UXAS_TYPEDEFS_TIMER_H */

