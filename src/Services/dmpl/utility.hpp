// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   utility.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_UTILITY_HPP
#define DMPL_UTILITY_HPP

#include <utility>
#include <memory>

#ifdef __GNUC__
  #define ATTR_UNUSED __attribute__((unused))
#else
  #define ATTR_UNUSED
#endif

#if __cplusplus >= 201103L || (MSC_VER >= 1600)
#include <type_traits>
#include <atomic>

#define USE_CPP11
#define USE_ATOMIC
#define USE_RVAL_REF
#define USE_VAR_TMPL
#define USE_STD_ARRAY
#define USE_UNIQUE_PTR
#define USE_EMPLACE
#define USE_USING_TYPE
#define USE_STATIC_ASSERT
#define USE_TYPE_TRAITS
#define USE_DECLTYPE

#define LVAL_REF &
#define DEFAULT_0 =0

#define DMPL_BASE_TYPE(e) \
  typename std::remove_pointer< \
    typename std::remove_reference<decltype(e)>::type>::type

template<typename C>
using EnableIf = typename std::enable_if<C::value, void*>::type;

template<typename C>
using DisableIf = typename std::enable_if<!C::value, void*>::type;

#if __cplusplus >= 201402L

#define USE_CPP14

#endif

#else
#define nullptr NULL

// constexpr simply ignored if not supported
#define constexpr
#define LVAL_REF
#define DEFAULT_0
#define noexcept throw()
// approximate static_assert as best as possible
#define DMPL_STATIC_ASSERT_NAME static_assert_checker_##__LINE__

#define DMPL_STATIC_ASSERT(pred) \
  typedef int DMPL_STATIC_ASSERT_NAME [(pred) ? 1 : -1] ATTR_UNUSED

#define static_assert(p, message) \
DMPL_STATIC_ASSERT(p) /* ** error: static_assert failure, see reason below ** */
#endif

#ifndef USE_VAR_TMPL

/* Macros that hardcode the maximum number of dimensions allowed to an
 * ArrayReference in pre-C++11 mode. To raise limit, edit all macros below.
 */

#define DMPL_ARRAY_REFERENCE_MAX_DIMS 10

#define DMPL_DECL_DIMS size_t d0, size_t d1, size_t d2, size_t d3, size_t d4, \
                       size_t d5, size_t d6, size_t d7, size_t d8, size_t d9

#define DMPL_DECL_DIMS_DEFAULT \
     size_t d0, size_t d1 = 0, size_t d2 = 0, size_t d3 = 0, size_t d4 = 0, \
     size_t d5 = 0, size_t d6 = 0, size_t d7 = 0, size_t d8 = 0, size_t d9 = 0

#define DMPL_DECL_DIMS_x size_t x0, size_t x1, size_t x2, size_t x3, size_t x4,\
                         size_t x5, size_t x6, size_t x7, size_t x8, size_t x9

#define DMPL_ALL_DIMS d0, d1, d2, d3, d4, d5, d6, d7, d8, d9
#define DMPL_SHIFT_DIMS d1, d2, d3, d4, d5, d6, d7, d8, d9, 0

#define DMPL_DECL_ARGS \
    size_t i0 = 0, size_t i1 = 0, size_t i2 = 0, size_t i3 = 0, size_t i4 = 0, \
    size_t i5 = 0, size_t i6 = 0, size_t i7 = 0, size_t i8 = 0, size_t i9 = 0

#define DMPL_ALL_PARAMS i0, i1, i2, i3, i4, i5, i6, i7, i8, i9
#define DMPL_SHIFT_PARAMS i1, i2, i3, i4, i5, i6, i7, i8, i9, 0

#define DMPL_ZERO_DIMS 0, 0, 0, 0, 0, 0, 0, 0, 0, 0

#else
//C++ standard for maximum template arguments (minus 1 for array type)
#define DMPL_ARRAY_REFERENCE_MAX_DIMS 1023
#endif

#define static_assert_false(var, message) \
  static_assert(sizeof(var) == -1, message);

namespace madara
{

#ifdef USE_UNIQUE_PTR
template<typename T, typename ...Args>
std::unique_ptr<T> make_unique(Args&& ...args)
{
  return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}
#endif

#ifdef USE_CPP14
using std::integer_sequence;
using std::index_sequence;
using std::make_index_sequence;
using std::index_sequence_for;
#else
#ifdef USE_VAR_TMPL
template<typename T, T ...>
struct integer_sequence { };

template<size_t ...S>
using index_sequence = integer_sequence<size_t, S...>;

namespace detail
{

template<size_t N, size_t ...S>
struct make_index_sequence_ : make_index_sequence_<N-1, N-1, S...> { };

template<size_t ...S>
struct make_index_sequence_<0, S...> {
  typedef index_sequence<S...> type;
};

}

template<size_t N>
using make_index_sequence=typename detail::make_index_sequence_<N>::type;

template<class ...T>
using index_sequence_for = make_index_sequence<sizeof...(T)>;
#endif
#endif

namespace knowledge
{

namespace containers
{

namespace detail
{

  template<typename T>
  struct identity
  {
    typedef T type;
  };

#ifdef USE_TYPE_TRAITS
  /**
   * If T is an rvalue (or not a reference), use move semantics
   **/
  template <typename T, bool = std::is_lvalue_reference<T>::value >
  struct handle_index_type
  {
    template <typename B>
    static T do_index(B &&base, size_t i)
    {
      return std::move(std::move(base)[i]);
    }
  };

  /**
   * If T is an lvalue reference, simply return that reference
   **/
  template <typename T>
  struct handle_index_type<T, true>
  {
    template <typename B>
    static T do_index(B &base, size_t i)
    {
      return base[i];
    }
  };

  template<typename ...Args>
  struct resolve_overload
  {
    template<typename R, typename T>
    constexpr auto operator()(R (T::*f)(Args...))
      -> R (T::*)(Args...)
    {
      return f;
    }

    template<typename R, typename T>
    constexpr auto operator()(R (T::*f)(Args...) const)
      -> R (T::*)(Args...) const
    {
      return f;
    }
  };
#endif


}
}
}
}


#endif
