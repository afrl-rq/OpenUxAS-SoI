// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   IndexedArrayReference.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_INDEXED_ARRAY_REFERENCE_HPP
#define DMPL_INDEXED_ARRAY_REFERENCE_HPP

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
#include "utility.hpp"
#include "knowledge_cast.hpp"
#include "StorageManager.hpp"
#include "ArrayReferenceFwd.hpp"

namespace madara
{

namespace knowledge
{

namespace containers
{

namespace detail
{

template<typename T>
class IndexedArrayReference
  : protected IndexedArrayReference<typename T::subarray_type>,
    public T::sm_type::template RefDimensionMixin<T>
{
public:
  typedef T array_type;
  typedef typename T::subarray_type subarray_type;
protected:
  typedef typename array_type::sm_info sm_info;
  typedef typename array_type::sm_type sm_type;
  typedef typename sm_info::storage_type storage_type;
  typedef typename sm_type::template RefDimensionMixin<array_type>storage_mixin;

  static const size_t static_size = array_type::static_size;
  static const size_t static_rank = array_type::static_rank;

  storage_mixin &get_storage_mixin()
  {
    return static_cast<storage_mixin &>(*this);
  }

  constexpr const storage_mixin &get_storage_mixin() const
  {
    return static_cast<const storage_mixin &>(*this);
  }
public:
  typedef typename array_type::value_type value_type;

  typedef IndexedArrayReference<array_type> index_as_type;
  typedef IndexedArrayReference<typename array_type::subarray_type> sub_type;
  typedef typename sub_type::index_as_type indexed_type;
#ifdef USE_RVAL_REF
  typedef IndexedArrayReference<array_type> &&rvalue_index_as_type;
  typedef typename sub_type::rvalue_index_as_type rvalue_indexed_type;
#endif
  typedef typename array_type::base_index_type base_index_type;

protected:
  constexpr array_type &get_array() const
  {
    return static_cast<array_type &>(sub_type::get_array());
  }

public:

  friend class ArrayReferenceBase;
  friend class identity<array_type>::type;
  friend class identity<sm_type>::type;

  template<typename A>
  friend class sm_type::BaseMixin;

  template<typename A>
  friend class sm_type::RefBaseMixin;

  template<typename A, size_t Size, size_t Dims>
  friend class sm_type::DimensionMixin;

  template<typename A>
  friend class sm_type::RefDimensionMixin;

  template<typename A>
  friend class IndexedArrayReference;

#ifdef USE_VAR_TMPL
  template<typename X, size_t x0, size_t... xN>
  friend class ArrayReference;
#else
  template <typename X, DMPL_DECL_DIMS>
  friend class ArrayReference;
#endif

protected:
  sub_type &get_sub_type()
  {
    return static_cast<sub_type &>(*this);
  }

  constexpr const sub_type &get_sub_type() const
  {
    return static_cast<const sub_type &>(*this);
  }

  size_t get_multiplier() const
  {
    const size_t num_rank = rank();
    if(num_rank <= 1)
      return 1;
    size_t s = get_sub_type().size();
    if(num_rank == 2)
      return s;
    if(s == VAR_LEN)
      return VAR_LEN;
    return s * get_sub_type().get_multiplier();
  }
#ifdef USE_TYPE_TRAITS
protected:
  typedef typename array_type::variadic_barrier variadic_barrier;
public:
  typedef typename std::remove_reference<base_index_type>::type &&for_each_type;

  template<typename Op, typename ...Args>
  auto for_each(Op op, Args&& ...args)
    -> decltype(op(std::declval<base_index_type>(),
                   std::forward<Args>(args)...))
  {
    return get_array().for_each(op, *this, variadic_barrier(),
                                std::forward<Args>(args)...);
  }
#endif

public:
  /**
   * C++11 support is highly recommended for multi-dimensional arrays;
   * without it, each index operation creates pointless copies of
   * IndexedArrayReference object
   */
#ifdef USE_RVAL_REF
  indexed_type operator[](size_t i) &;

  rvalue_indexed_type operator[](size_t i) &&;
#else
  indexed_type operator[](size_t i);
#endif

  /*
  operator array_type() const
  {
    array_type ret(this->get_context(), this->get_settings(), this->get_name());
    return ret;
  }*/

protected:
  constexpr IndexedArrayReference(array_type &v)
    : IndexedArrayReference<typename array_type::subarray_type>(v),
      storage_mixin(v) {}

  index_as_type dereference() LVAL_REF
  {
    return *this;
  }

#ifdef USE_RVAL_REF
  rvalue_index_as_type dereference() &&
  {
    return std::move(*this);
  }
#endif

  void append_index(size_t i)
  {
    get_storage_mixin().append_index(i);
  }

public:
  bool check_bounds(size_t i) const
  {
    return get_storage_mixin().check_bounds(i);
  }

  constexpr size_t size() const
  {
    return get_storage_mixin().size();
  }

  constexpr size_t rank() const
  {
    return get_storage_mixin().rank();
  }

  constexpr bool resizable() const
  {
    return get_storage_mixin().resizable();
  }

  void resize(size_t new_size)
  {
    get_array().resize(new_size);
  }
};

template<typename R>
#ifdef USE_VAR_TMPL
class IndexedArrayReference<ArrayReference<R>>
#else
class IndexedArrayReference<ArrayReference<R, DMPL_ZERO_DIMS> >
#endif
  : public ArrayReference_0<R>::type::sm_type::template
             RefBaseMixin<typename ArrayReference_0<R>::type>
{
public:
  typedef typename ArrayReference_0<R>::type array_type;
protected:
  array_type &array;

  typedef R storage_specifier;
  typedef StorageManager::detail::get_sm_info<R> sm_info;
  typedef typename sm_info::sm_type sm_type;
  typedef typename sm_info::data_type value_type;
  typedef typename sm_type::template RefBaseMixin<array_type> storage_mixin;

  storage_mixin &get_storage_mixin()
  {
    return static_cast<storage_mixin &>(*this);
  }

  constexpr const storage_mixin &get_storage_mixin() const
  {
    return static_cast<const storage_mixin &>(*this);
  }

  constexpr array_type &get_array() const
  {
    return array;
  }

public:
  using storage_mixin::operator=;

  IndexedArrayReference &operator=(const IndexedArrayReference &o)
  {
    storage_mixin::operator=(o);
    return *this;
  }

  IndexedArrayReference(array_type &v)
    : storage_mixin(v), array(v) {}

  IndexedArrayReference(const IndexedArrayReference<array_type> &o)
    : storage_mixin(o.get_storage_mixin()), array(o.array) {}

#ifdef USE_RVAL_REF
  IndexedArrayReference(IndexedArrayReference &&o)
    : storage_mixin(std::move(o.get_storage_mixin())), array(o.array) {}
#endif

  typedef typename storage_mixin::element_reference_type index_as_type;
#ifdef USE_RVAL_REF
  typedef typename storage_mixin::element_rvalue_type rvalue_index_as_type;
#endif

  constexpr std::string get_name() const
  {
    return get_storage_mixin().get_name();
  }

  constexpr size_t get_multiplier() const
  {
    return 1;
  }

  bool check_bounds(size_t i) const
  {
    static_assert_false(R, "check_bounds called on element reference");

    // Shouldn't actually happen, but just in case
    throw std::runtime_error("check_bounds called on element reference");
  }

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

  void resize(size_t)
  {
    static_assert_false(R, "resize called on element reference");
  }

  void append_index(size_t i)
  {
    get_storage_mixin().append_index(i);
  }

  friend class ArrayReferenceBase;

  template<typename A>
  friend class IndexedArrayReference;

  friend class identity<sm_type>::type;

  template<typename A>
  friend class sm_type::BaseMixin;

  template<typename A>
  friend class sm_type::RefBaseMixin;

  template<typename A, size_t Size, size_t Dims>
  friend class sm_type::DimensionMixin;

  template<typename A>
  friend class sm_type::RefDimensionMixin;

#ifdef USE_VAR_TMPL
  template<typename X, size_t x0, size_t... xN>
  friend class ArrayReference;
#else
  template <typename X, DMPL_DECL_DIMS_x>
  friend class ArrayReference;
#endif
};


void throw_range_error(std::string name, int i, int max)
{
  std::ostringstream err;
  err << "Index " << i << " of " << name <<
         " out of bounds (required: 0 <= index < " << max << ")";
  throw std::range_error(err.str());
}

template<typename T>
inline typename IndexedArrayReference<T>::indexed_type
IndexedArrayReference<T>::operator[](size_t i) LVAL_REF
{
  if(!this->check_bounds(i))
    throw_range_error(this->get_name(), i, this->size());
  //std::cerr << "index op lvalue: " << this->get_name() << std::endl;
  IndexedArrayReference<T> ret(*this);
  ret.append_index(i);
  //std::cerr << "index lvalue: " << ret.get_name() << std::endl;
  return static_cast<sub_type&>(ret).dereference();
}

#ifdef USE_RVAL_REF
template<typename T>
inline typename IndexedArrayReference<T>::rvalue_indexed_type
IndexedArrayReference<T>::operator[](size_t i) &&
{
  typedef typename IndexedArrayReference<T>::rvalue_indexed_type itype;
  if(!this->check_bounds(i))
    throw_range_error(this->get_name(), i, this->size());
  this->append_index(i);
  //return std::forward<itype>(std::forward<itype>(static_cast<sub_type&&>(*this)).dereference());
  return std::forward<itype>(std::move(static_cast<sub_type&&>(*this)).dereference());
}
#endif

}
}
}
}

#endif
