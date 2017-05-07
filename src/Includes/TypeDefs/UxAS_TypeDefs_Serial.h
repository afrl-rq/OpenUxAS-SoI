// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UxAS_TypeDefs_Serial.h
 * Author: steve
 *
 * Created on February 14, 2014, 4:43 PM GMT
 */

#ifndef UXAS_TYPEDEFS_SERIAL_H
#define	UXAS_TYPEDEFS_SERIAL_H

#include "serial/serial.h"
#include <memory>       //std::shared_ptr

namespace n_Typedefs
{

    typedef std::shared_ptr<serial::Serial> PTR_SERIAL_t;
    
}       //namespace n_Typedefs

#endif	/* UXAS_TYPEDEFS_SERIAL_H */

