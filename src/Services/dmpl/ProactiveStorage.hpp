/**
 * Copyright (c) 2015 Carnegie Mellon University. All Rights Reserved.

 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:

 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following acknowledgments
 * and disclaimers.

 * 2. Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following
 * disclaimer in the documentation and/or other materials provided
 * with the distribution.

 * 3. The names "Carnegie Mellon University," "SEI" and/or "Software
 * Engineering Institute" shall not be used to endorse or promote
 * products derived from this software without prior written
 * permission. For written permission, please contact
 * permission@sei.cmu.edu.

 * 4. Products derived from this software may not be called "SEI" nor
 * may "SEI" appear in their names without prior written permission of
 * permission@sei.cmu.edu.

 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:

 * This material is based upon work funded and supported by the
 * Department of Defense under Contract No. FA8721-05-C-0003 with
 * Carnegie Mellon University for the operation of the Software
 * Engineering Institute, a federally funded research and development
 * center.

 * Any opinions, findings and conclusions or recommendations expressed
 * in this material are those of the author(s) and do not necessarily
 * reflect the views of the United States Department of Defense.

 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE
 * ENGINEERING INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS"
 * BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND,
 * EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT
 * LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR MERCHANTABILITY,
 * EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL. CARNEGIE
 * MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.

 * This material has been approved for public release and unlimited
 * distribution.

 * DM-0002494
**/

#ifndef DMPL_PROACTIVE_HPP
#define DMPL_PROACTIVE_HPP

#include <utility>
#include <memory>
#include <string>
#include <vector>
#include <climits>
#include <cassert>
#include <sstream>
#include <typeinfo>
#include <exception>
#include <madara/knowledge/ThreadSafeContext.h>
#include <madara/knowledge/ThreadSafeContext.h>
#include <madara/knowledge/KnowledgeUpdateSettings.h>
#include "knowledge_cast.hpp"
#include "Reference.hpp"
#include "StorageManager.hpp"

#if __cplusplus >= 201103L
#include <array>

#define USE_RVAL_REF
#define USE_VAR_TMPL
#define USE_STD_ARRAY
#define USE_UNIQUE_PTR
#define USE_EMPLACE
#define USE_USING_TYPE
#define USE_STATIC_ASSERT
#endif

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
}

template <typename T, template<typename X> class S = Reference>
struct Proactive
{
  typedef Proactive<T, S> this_type;
  typedef T data_type;
  typedef S<T> storage_type;

  template<typename A>
  class BaseMixin
  {
  public:
#ifdef USE_UNIQUE_PTR
    typedef std::unique_ptr<storage_type> ptr_type;
#else
    typedef storage_type *ptr_type;
#endif
    typedef std::vector<storage_type> vector_type;
    typedef std::vector<size_t> dim_sizes_t;
    dim_sizes_t dim_sizes;
    vector_type stored_data;

    template <typename X>
    friend class detail::IndexedArrayReference;

    BaseMixin(A &a) { }

    BaseMixin(const BaseMixin &o) : dim_sizes(o.dim_sizes)
    {
      for(typename vector_type::iterator it = stored_data.begin();
          it != stored_data.end(); ++it)
      {
        stored_data.push_back(*it);
      }
    }

    bool inc_index(std::vector<size_t> &index)
    {
      for(int i = 0; i < index.size(); ++i)
      {
        if(index[i] < dim_sizes[i] - 1)
        {
          ++(index[i]);
          return true;
        }
        else
        {
          index[i] = 0;
        }
      }
      return false;
    }

    const std::string &get_array_name() const
    {
      return static_cast<const A&>(*this).A::get_name();
    }

    /**
     * Clears any existing storage, and recreates references to all array
     * elements.
     */
    void init_storage()
    {
      stored_data.clear();
      size_t total_size = 1;
      for(int i = dim_sizes.size() - 1; i >= 0; --i)
      {
        total_size *= dim_sizes[i];
      }
      stored_data.reserve(total_size);
      std::vector<size_t> cur_index(dim_sizes.size());
      A &base = static_cast<A&>(*this);
      do
      {
        std::ostringstream str;
        str << get_array_name();
        for(int i = cur_index.size() - 1; i >= 0; --i)
        {
          str << "." << cur_index[i];
        }
        //std::cerr << "Making reference to " << str.str() << std::endl;
#ifdef USE_EMPLACE
        stored_data.emplace_back(base.get_context(),
                                 base.get_settings(),
                                 str.str());
#else
        stored_data.push_back(storage_type(base.get_context(),
                                           base.get_settings(),
                                           str.str()));
#endif
      }
      while(inc_index(cur_index));
    }

#ifdef USE_RVAL_REF
    BaseMixin(BaseMixin &&o)
      : dim_sizes(std::move(o.dim_sizes)),
        stored_data(std::move(o.stored_data)) {}
#endif

    constexpr size_t size() const
    {
      return 1;
    }

    constexpr size_t rank() const
    {
      return 0;
    }

    constexpr bool resizable() const
    {
      return false;
    }
  };

  template<typename A, size_t Size, size_t Rank>
  class DimensionMixin
  {
  public:
    typedef A array_type;

    static const size_t static_size = Size;
    static const size_t static_rank = Rank;

    typedef typename detail::ArrayReference_0<this_type>::type base_type;
    typedef BaseMixin<base_type> base_mixin;

    template <typename X>
    friend class detail::IndexedArrayReference;

    base_mixin &get_base_mixin()
    {
      return static_cast<base_mixin &>(
        static_cast<base_type &>(static_cast<A &>(*this)));
    }

    constexpr const base_mixin &get_base_mixin() const
    {
      return static_cast<const base_mixin &>(
        static_cast<const base_type &>(static_cast<const A &>(*this)));
    }

  private:
    void size_sanity(size_t newSize)
    {
      if(static_size != VAR_LEN && (newSize != 0 && newSize != static_size))
      {
        std::ostringstream err;
        err << "Tried to resize dimension with static size " << static_size <<
               " to size " << newSize << std::endl;
        throw std::range_error(err.str());
      }
    }

  public:
    void resize(size_t i)
    {
      if(i != size())
      {
        size_sanity(i);
        get_base_mixin().dim_sizes[static_rank - 1] = i;

        // TODO: instead of throwing out all existing storage and
        //       re-initializing everything, keep existing storage,
        //       only initialize new ones.
        get_base_mixin().init_storage();
      }
    }

    size_t size() const
    {
      return static_size == VAR_LEN ?
        get_base_mixin().dim_sizes[static_rank - 1] : static_size;
    }

    constexpr bool check_bounds(size_t i) const
    {
      return i >= 0 && i < size();
    }

    constexpr size_t rank() const
    {
      return static_rank;
    }

    constexpr bool resizable() const
    {
      return static_size == VAR_LEN;
    }

  public:
    DimensionMixin(A &a, size_t i0 = 0)
    {
      size_sanity(i0);
      size_t s = (i0 == 0 ? static_size : i0);
      a.dim_sizes.push_back(s);
    }
  };

  template<typename A>
  class RefDimensionMixin
  {
  public:
    typedef A array_type;
    static const size_t static_size = A::static_size;
    static const size_t static_rank = A::static_rank;
    typedef typename array_type::base_type array_base_type;
    typedef typename array_type::reference_type reference_type;
    typedef typename array_type::base_reference_type base_reference_type;
    typedef typename array_type::value_type value_type;
    typedef BaseMixin<array_base_type> base_mixin;

    template <typename X>
    friend class detail::IndexedArrayReference;

    reference_type &get_reference()
    {
      return static_cast<reference_type&>(*this);
    }

    constexpr const reference_type &get_reference() const
    {
      return static_cast<const reference_type&>(*this);
    }

    base_reference_type &get_base_reference()
    {
      return static_cast<base_reference_type&>(get_reference());
    }

    constexpr const base_reference_type &get_base_reference() const
    {
      return static_cast<const base_reference_type&>(get_reference());
    }

    base_mixin &get_base_mixin()
    {
      return get_base_reference().base_mixin;
    }

    constexpr const base_mixin &get_base_mixin() const
    {
      return get_base_reference().base_mixin;
    }

    size_t size() const
    {
      return static_size == VAR_LEN ?
        get_base_mixin().dim_sizes[static_rank - 1] : static_size;
    }

    void append_index(size_t i)
    {
      size_t mult = this->get_reference().get_multiplier();
      if(mult == VAR_LEN)
        throw std::range_error("Proactive storage manager does not support" \
                               "unbounded VAR_LEN dimensions.");
      this->get_reference().offset += i * mult;
    }

    constexpr size_t rank() const
    {
      return static_rank;
    }

    constexpr bool resizable() const
    {
      return static_size == VAR_LEN;
    }

    bool check_bounds(size_t i) const
    {
      return i >= 0 && i < size();
    }

    void resize(size_t new_size)
    {
      get_reference().get_array().resize>(new_size);
    }

    RefDimensionMixin(A& a) {}
  };

  template<typename A>
  class RefBaseMixin
  {
  public:
    typedef storage_type  &element_reference_type;
#ifdef USE_RVAL_REF
    typedef storage_type  &element_rvalue_type;
#endif

    typedef typename A::storage_specifier storage_specifier;
    typedef typename
      detail::ArrayReference_0<storage_specifier>::type base_array_type;
    typedef detail::IndexedArrayReference<base_array_type> base_ref_type;

    typedef typename BaseMixin<A>::ptr_type ptr_type;

    BaseMixin<A> &base_mixin;
    size_t offset;

    template <typename X>
    friend class detail::IndexedArrayReference;

    RefBaseMixin(A &a)
      : base_mixin(static_cast<BaseMixin<A> &>(a)), offset(0)
    { }

    RefBaseMixin(const RefBaseMixin<A> &o)
      : base_mixin(o.base_mixin), offset(o.offset)
    { }

#ifdef USE_RVAL_REF
    RefBaseMixin(RefBaseMixin<A> &&o)
      : base_mixin(o.base_mixin), offset(o.offset) { }
#endif

  protected:
    base_ref_type &get_base_ref()
    {
      return static_cast<base_ref_type &>(*this);
    }

    base_array_type &get_base_array()
    {
      return static_cast<base_array_type &>(base_mixin);
    }

    element_reference_type dereference()
    {
      if(base_mixin.stored_data.size() == 0)
        base_mixin.init_storage();
      return base_mixin.stored_data[offset];
    }

  public:
    std::string get_name() const
    {
      std::ostringstream ret;
      ret << base_mixin.get_array_name();
      size_t o = offset;
      for(typename BaseMixin<A>::dim_sizes_t::const_reverse_iterator
            it = base_mixin.dim_sizes.rbegin();
          it != base_mixin.dim_sizes.rend(); ++it)
      {
        size_t mult = 1;
        typename BaseMixin<A>::dim_sizes_t::const_reverse_iterator it2 = it;
        ++it2;
        for(; it2 != base_mixin.dim_sizes.rend(); ++it2)
        {
          if(*it == VAR_LEN)
            throw std::runtime_error("Proactive storage manager does not " \
                                     "support unbound VAR_LEN dimensions, " \
                                     "other than the first dimension.");
          mult *= *it2;
        }
        ret << "." << o / mult;
        o %= mult;
      }
      return ret.str();
    }

    void append_index(size_t i)
    {
    }
  };
};

namespace detail
{

  template <typename T, template<typename X> class S>
  struct get_sm_info<Proactive<T,S> >
  {
    typedef Proactive<T,S> sm_type;
    typedef T data_type;
    typedef S<T> storage_type;
  };

}

}
}
}
}
#endif
