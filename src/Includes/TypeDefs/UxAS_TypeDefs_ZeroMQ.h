// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   UxAS_TypeDefs_ZeroMQ.h
 * Author: steve
 *
 * Created on December 18, 2013, 3:46 PM
 */

#ifndef UXAS_TYPEDEFS_ZEROMQ_H
#define    UXAS_TYPEDEFS_ZEROMQ_H

#include <memory>       //std::shared_ptr

#include "zmq.hpp"

namespace n_Typedefs
{

    typedef std::shared_ptr<zmq::context_t> PTR_ZMQ_CONTEXT_t;
    typedef std::shared_ptr<zmq::socket_t> PTR_ZMQ_SOCKET_t;
    
    
}       //namespace n_Typedefs

#endif    /* UXAS_TYPEDEFS_ZEROMQ_H */

