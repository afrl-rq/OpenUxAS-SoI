// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   ArrayReferenceFwd.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_ARRAY_REFERENCE_FWD_HPP
#define DMPL_ARRAY_REFERENCE_FWD_HPP

#include <climits>
#include "utility.hpp"

namespace madara
{

namespace knowledge
{

namespace containers
{

enum { VAR_LEN = UINT_MAX };

#ifdef USE_VAR_TMPL
template <typename T, size_t d0 = 0, size_t ...dN>
class ArrayReference;
#else
template <typename T, DMPL_DECL_DIMS_DEFAULT>
class ArrayReference;
#endif

namespace detail
{

template<typename T>
struct ArrayReference_0
{
#ifdef USE_VAR_TMPL
  typedef class ArrayReference<T> type;
#else
  typedef ArrayReference<T, DMPL_ZERO_DIMS> type;
#endif
};

}
}
}
}

#endif
