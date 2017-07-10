// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   StatelessStorage.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_STATELESS_HPP
#define DMPL_STATELESS_HPP

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
#include "ReferenceBase.hpp"
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

/**
 * For internal use.
 *
 * For efficient storage of dimension sizes, staticly sized dimensions
 * do not store any data at run-time
 **/
template <size_t Size, size_t Rank>
class SizeManager
{
protected:
  static const size_t rank_ = Rank;
  static const size_t size_ = Size;
  SizeManager() {}
  SizeManager(size_t s) { resize(s); }
  void throw_error(size_t newSize)
  {
    std::ostringstream err;
    err << "Tried to resize dimension with static size " << size() <<
           " to size " << newSize << std::endl;
    throw std::range_error(err.str());
  }

public:
  constexpr size_t size() const { return size_; }

  constexpr size_t rank() const { return rank_; }

  constexpr bool resizable() const { return false; }

  void resize(size_t newSize) {
    if(newSize != 0 && newSize != size())
      throw_error(newSize);
  }

  constexpr bool check_bounds(size_t i) const
  {
    return i >= 0 && i < size();
  }
};

/**
 * For internal use.
 *
 * Specialization for VAR_LEN dimensions, that stores the actual run-time size
 * of the array.
 **/
template <size_t Rank>
struct SizeManager<VAR_LEN, Rank>
{
protected:
  static const size_t rank_ = Rank;
#ifdef USE_ATOMIC
  std::atomic<size_t> size_;
#else
  size_t size_;
#endif
  SizeManager() : size_(VAR_LEN) {}
  SizeManager(size_t s) : size_(s > 0 ? s : VAR_LEN) {}
#ifdef USE_ATOMIC
  /* No copy constructor for std::atomic<T>; must define these manually */
  SizeManager(const SizeManager &o) : size_(o.size()) {}
  SizeManager *operator=(const SizeManager &o)
  {
    resize(o.size());
  }
#endif

public:
  constexpr size_t rank() const { return rank_; }

  constexpr bool resizable() const { return true; }

  constexpr bool check_bounds(size_t i) const
  {
    return i >= 0 && i < size();
  }

#ifdef USE_ATOMIC
  constexpr size_t size() const
  {
    return size_.load(std::memory_order_acquire);
  }

  void resize(size_t new_size) {
    if(new_size > 0)
      size_.store(new_size, std::memory_order_release);
  }
#else
  constexpr size_t size() const { return size_; }

  void resize(size_t new_size) {
    if(new_size > 0)
      size_ = new_size;
  }
#endif
};

/**
 * For internal use.
 *
 * For staticly sized arrays, we don't actually need to store any information
 * in the IndexedArrayReference.
 **/
template <size_t Size, size_t Rank>
struct IndexSizeManager : protected SizeManager<Size, Rank>
{
public:
  SizeManager<Size, Rank> &size_manager()
  {
    return static_cast<SizeManager<Size, Rank>&>(*this);
  }
  constexpr const SizeManager<Size, Rank> &size_manager() const
  {
    return static_cast<const SizeManager<Size, Rank>&>(*this);
  }

protected:
  IndexSizeManager(SizeManager<Size, Rank> &sm) {}
};

/**
 * For internal use.
 *
 * Specialization for VAR_LEN dimensions, which stores a reference to the
 * corresponding SizeManager stored for this dimension in the ArrayReference
 **/
template<size_t Rank>
struct IndexSizeManager<VAR_LEN, Rank>
{
public:
  SizeManager<VAR_LEN, Rank> &size_manager() { return size_manager_; }

  constexpr const SizeManager<VAR_LEN, Rank> &size_manager() const
  {
    return size_manager_;
  }

protected:
  IndexSizeManager(SizeManager<VAR_LEN, Rank> &sm) : size_manager_(sm) {}

  SizeManager<VAR_LEN, Rank> &size_manager_;
};

/**
 * Default storage manager for ArrayReference, used when Lazy or Proactive
 * aren't specified.
 *
 * For internal use, do not use directly. E.g., this type:
 *
 * ArrayReference<detail::Stateless<int>, 3, 4, 5>
 *
 * is distinct from:
 *
 * ArrayReference<int, 3, 4, 5>
 *
 * in certain confusing and unnecessary ways. Do not use the former.
 *
 * For semantics of this storage manager, see ArrayReference documentation
 **/
template <typename T>
struct Stateless
{
  typedef Stateless<T> this_type;
  typedef T data_type;

  template <typename X>
  class RefDimensionMixin;

  template <typename X>
  class RefBaseMixin;

  template<typename A, size_t Size, size_t Rank>
  class DimensionMixin : protected SizeManager<Size, Rank>
  {
  protected:
    typedef SizeManager<Size, Rank> size_mgr_;

    size_mgr_ &size_mgr()
    {
      return static_cast<size_mgr_ &>(*this);
    }

    constexpr const size_mgr_ &size_mgr() const
    {
      return static_cast<const size_mgr_ &>(*this);
    }
  public:
    typedef A array_type;
    typedef T data_type;

    template <typename X>
    friend class IndexedArrayReference;

    friend class identity<A>::type;

    template <typename X>
    friend class ArrayReference_0;

    template <typename X>
    friend class RefDimensionMixin;

    template <typename X>
    friend class RefBaseMixin;

    DimensionMixin(A &a, size_t i0 = 0)
      : size_mgr_(i0) { }

    constexpr bool check_bounds(size_t i) const
    {
      return this->size_mgr().check_bounds(i);
    }

    constexpr size_t size() const
    {
      return this->size_mgr().size();
    }

    constexpr size_t rank() const
    {
      return this->size_mgr().rank();
    }

    constexpr bool resizable() const
    {
      return this->size_mgr().resizable();
    }

    void resize(size_t i)
    {
      return this->size_mgr().resize(i);
    }
  };

  template<typename A>
  class BaseMixin :
      protected SizeManager<1, 0>
  {
  protected:
    typedef SizeManager<1, 0> size_mgr_;

    size_mgr_ &size_mgr()
    {
      return static_cast<size_mgr_ &>(*this);
    }

    constexpr const size_mgr_ &size_mgr() const
    {
      return static_cast<const size_mgr_ &>(*this);
    }

  public:
    template <typename X>
    friend class IndexedArrayReference;

    friend class identity<A>::type;

    template <typename X>
    friend class ArrayReference_0;

    template <typename X>
    friend class RefDimensionMixin;

    template <typename X>
    friend class RefBaseMixin;

    BaseMixin(A &a)
    {
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
  };

  template<typename A>
  class RefDimensionMixin
    : public IndexSizeManager<A::static_size, A::static_rank>
  {
  protected:
    typedef IndexSizeManager<A::static_size, A::static_rank> size_mgr_ref;
    typedef SizeManager<A::static_size, A::static_rank> size_mgr_;

    size_mgr_ &size_mgr()
    {
      return static_cast<size_mgr_ref &>(*this).size_manager();
    }

    const size_mgr_ &size_mgr() const
    {
      return static_cast<const size_mgr_ref &>(*this).size_manager();
    }
  public:
    typedef A array_type;
    typedef typename array_type::reference_type reference_type;
    typedef typename array_type::value_type value_type;

    template <typename X>
    friend class IndexedArrayReference;

    friend class identity<A>::type;

    reference_type &get_reference()
    {
      return static_cast<reference_type&>(*this);
    }

    constexpr const reference_type &get_reference() const
    {
      return static_cast<reference_type&>(*this);
    }

    void append_index(size_t i)
    {
      this->get_reference().get_sub_type().append_index(i);
    }

    constexpr bool check_bounds(size_t i) const
    {
      return this->size_mgr().check_bounds(i);
    }

    constexpr size_t size() const
    {
      return this->size_mgr().size();
    }

    constexpr size_t rank() const
    {
      return this->size_mgr().rank();
    }

    constexpr bool resizable() const
    {
      return this->size_mgr().resizable();
    }

    void resize(size_t new_size)
    {
      this->size_mgr().resize(new_size);
    }

    RefDimensionMixin(A& a)
      : size_mgr_ref(a.template get_storage_mixin<0>().template size_mgr())
      {}
  };

  template<typename A>
  class RefBaseMixin
    : public ReferenceBase<T, RefBaseMixin<A> >,
      public SizeManager<1, 0>
  {
  protected:
    typedef ReferenceBase<T, RefBaseMixin<A> > container_type;
    typedef SizeManager<1, 0> size_mgr_;

    size_mgr_ &size_mgr()
    {
      return static_cast<size_mgr_ &>(*this);
    }

    constexpr const size_mgr_ &size_mgr() const
    {
      return static_cast<const size_mgr_ &>(*this);
    }
  public:
    typedef typename A::storage_specifier storage_specifier;
    typedef typename ArrayReference_0<storage_specifier>::type base_array_type;
    typedef IndexedArrayReference<base_array_type> element_reference_type;
#ifdef USE_RVAL_REF
    typedef element_reference_type &&element_rvalue_type;
#endif
  protected:
    element_reference_type &get_parent()
    {
      return static_cast<element_reference_type &>(*this);
    }

    constexpr const element_reference_type &get_parent() const
    {
      return static_cast<const element_reference_type &>(*this);
    }

    constexpr base_array_type &get_array() const
    {
      return get_parent().array;
    }
  public:
    using container_type::operator=;

    template <typename X>
    friend class IndexedArrayReference;

    friend class identity<A>::type;

    friend class identity<typename ArrayReference_0<this_type>::type >::type;

  protected:
    element_reference_type dereference() LVAL_REF
    {
      return static_cast<element_reference_type &>(*this);
    }

#ifdef USE_RVAL_REF
    element_rvalue_type dereference() &&
    {
      return std::move(static_cast<element_reference_type &>(*this));
    }
#endif

  public:
    RefBaseMixin &operator=(const RefBaseMixin &o)
    {
      this->set(o.get());
      return *this;
    }

#ifdef USE_RVAL_REF
    std::unique_ptr<std::ostringstream> name_str;

    RefBaseMixin(const A &a)
      : size_mgr_(a.template get_storage_mixin().size_mgr()),
        name_str(new std::ostringstream())
    {
      *name_str << a.get_name();
    }

    RefBaseMixin(const RefBaseMixin<A> &o)
      : size_mgr_(o.size_mgr()),
        name_str(new std::ostringstream())
    {
      *name_str << o.name_str->str();
    }

    RefBaseMixin(RefBaseMixin<A> &&o)
      : size_mgr_(o.size_mgr()),
        name_str(std::move(o.name_str)) { }

  protected:
    std::string do_get_name() const
    {
      return name_str->str();
    }

    void append_index(size_t i)
    {
      *name_str << "." << i;
    }
#else
    std::ostringstream name_str;

    RefBaseMixin(const A &a)
      : size_mgr_(a.template get_storage_mixin<0>().size_mgr()),
        name_str()
    {
      name_str << a.get_name();
    }

    RefBaseMixin(const RefBaseMixin<A> &o)
      : size_mgr_(o.size_mgr()),
        name_str()
    {
      name_str << o.name_str.str();
    }

  protected:
    std::string do_get_name() const
    {
      return name_str.str();
    }

    void append_index(size_t i)
    {
      name_str << "." << i;
    }
#endif

    ThreadSafeContext &do_get_context() const
    {
      return get_array().get_context();
    }

    KnowledgeUpdateSettings *do_get_settings() const
    {
      return get_array().get_settings();
    }

    const KnowledgeUpdateSettings &do_get_settings_cref() const
    {
      return get_array().get_settings_cref();
    }

    friend class detail::identity<container_type>::type;
  };
};

template <typename T>
struct get_sm_info<detail::Stateless<T> >
{
  typedef detail::Stateless<T> sm_type;
  typedef T data_type;
  typedef T storage_type;
};

} // End detail namespace

}

}
}
}
#endif
