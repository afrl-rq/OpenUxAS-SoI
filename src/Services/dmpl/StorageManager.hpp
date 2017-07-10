// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   StorageManager.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_STORAGE_MANAGER_FWD_HPP
#define DMPL_STORAGE_MANAGER_FWD_HPP

namespace madara
{

namespace knowledge
{

namespace containers
{

namespace StorageManager
{

namespace detail
{
using namespace ::madara::knowledge::containers::detail;

template<typename T>
class Stateless;

template<typename T>
struct get_sm_info;

template <typename T>
struct get_sm_info
{
  typedef detail::Stateless<T> sm_type;
  typedef T data_type;
  typedef T storage_type;
};
}

}
}
}
}

#endif
