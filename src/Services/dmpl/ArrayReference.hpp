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

#ifndef DMPL_ARRAY_HPP
#define DMPL_ARRAY_HPP

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
#include "ReferenceBase.hpp"
#include "ContextHost.hpp"
#include "StorageManager.hpp"
#include "ArrayReferenceFwd.hpp"
#include "IndexedArrayReference.hpp"

namespace madara
{

namespace knowledge
{

namespace containers
{


/*******************************************************************************
 *
 * ArrayReference provides a multidimensional array interface for interacting
 * with a MADARA knowledge base. The most basic usage is as follows:
 *
 * ArrayReference<int, 3, 4, 5> array(kbase, "array");
 *
 * Where kbase is an existing knowledge base, and "array" is the name that will
 * be used to prefix the names generated within the MADARA knowledge base.
 *
 * To access this array:
 *
 * array[x][y][z] = v;
 * v = array[x][y][z];
 *
 * This translates to storing v to and then loading v from the MADARA variable
 * "array.x.y.z", where x, y, and z are the actual values of x, y, and z
 *
 * The return value of indexing "array" acts essentially like a Reference<T>.
 * The only differences are implementation details, optimizing for one-time-use,
 * instead of repeated reuse of the same reference. Thus, for built-in
 * types, the reference value can be used as though it directly referenced a
 * value of that type. For class types, you must use get() to access any of its
 * methods; e.g.: array[x][y][z].get().deep_copy(), if the underlying type were
 * a KnowledgeRecord.
 *
 * In addition to the static sizes shown above, ArrayReference can support
 * variable length arrays, for all dimensions. To specify such an array, use
 * VAR_LEN in place of the integer for the dimensions meant to be variable
 * length. The constructor additionally can take integer arguments to set the
 * initial dynamic size of those dimensions. For static dimensions, and 
 * dimensions to be left unbounded, use zero. For example:
 *
 * ArrayReference<int, 3, VAR_LEN, VAR_LEN> vararr(kbase, "array", 0, 0, 5);
 *
 * vararr has a statically sized first dimension, a dynamic but currently
 * unbounded second dimension, and a dynamically sized third dimensions
 * initially bounded to 5. See also the resize method.
 *
 *******************************************************************************
 *
 * To use an ArrayReference object, simply index it like a native multi-
 * dimensional array. See the operator[] for details. E.g.,
 *
 * array[0][1][2] = 32;
 * cout << array[0][1][2] << endl;
 *
 * In addition, if compiled using C++11, several free functions within the
 * madara::knowledge::containers namespace become available which can manipulate
 * the entire array: mark_modified, and set. With Lazy and Proactive mode arrays
 * using CachedReference<T> storage (see below), push, pull, and
 * pull_keep_local become available as well. E.g.,
 *
 * set(array, 42); // sets all elements to 42
 * mark_modified(array); // marks all elements as modified
 *
 *******************************************************************************
 *
 * By default, the ArrayReference is essentially "stateless". It has no memory,
 * itself, of any accesses, and thus any accesses are O(log n), where n is the
 * size of the knowledge base. ArrayReference provides two other modes:
 *
 * Lazy Mode: in this mode, ArrayReference keeps "cache" of previous accessed
 * locations (using a VariableReference), so that re-accessing a location has
 * O(1) lookup time. To use this mode, wrap the type in the Lazy<> template:
 *
 * ArrayReference<Lazy<int>, 3, 4, 5> lazy(kbase, "array");
 *
 * Note that this accesses the same underlying MADARA variables as the
 * above "stateless" array. The same access methods as above work here.
 *
 * By default, Lazy<T> creates and saves a Reference<T> for each accessed
 * element. Re-accessing a saved element returns a reference to the Reference<T>
 * created on first access. Note that Reference<T> automatically
 * updates whenever the underlying knowledge base variable changes.
 *
 * You can specify a different scalar reference type to use as storage, such
 * as CachedReference<T>. To do so, pass the template name (without any <class>)
 * as a second argument to Lazy<>:
 *
 * ArrayReference<Lazy<int, CachedReference>, 3, 4, 5> clazy(kbase, "array");
 *
 * Now, the first time any given element is accessed, the current value will be
 * "pulled" into the storage space of clazy. Future accesses will access this
 * same cached element; the element must be "pulled" for it to update.
 *
 * Proactive Mode: this works like Lazy mode, except that upon the first time
 * an element in the ArrayReference is accessed, the entire array is cached
 * as though all elements were being accessed.
 *
 *******************************************************************************
 *
 * Performance note: C++11 is not required to use this class, but it helps
 * greatly with efficiency. In particular, indexing multi-dimensional arrays
 * without C++11 will result in superflous copying. For example, with a default
 * stateless array, each indexing beyond the first dimension copies a
 * std::ostringstream object and its buffer. With C++11, only one
 * std::ostringstream is allocated and deallocated per access, with no copying,
 * no matter how many dimensions are to be indexed.
 *
 * With Lazy and Proactive mode, the copying without C++11 support is much less
 * significant; only a pointer, and an size_t get copied each time.
 *
 *******************************************************************************
 *
 * Thread safety: ArrayReference in stateless mode with all statically sized
 * dimensions is almost entirely immutable, and thus thread safe, so long as
 * the set_settings method isn't used. With C++11, set_settings as well as
 * VAR_LEN dimensions are also thread safe.
 *
 * In Lazy and Proactive mode, no thread safety is guaranteed.
 *
 *******************************************************************************
 **/
#ifdef USE_VAR_TMPL
template <typename T, size_t d0, size_t ...dN>
class ArrayReference
  : protected ArrayReference<T, dN...>,
    public StorageManager::detail::get_sm_info<T>::sm_type::template
        DimensionMixin<ArrayReference<T, d0, dN...>, d0,
                       ArrayReference<T, dN...>::static_rank + 1 >
#else
template <typename T, DMPL_DECL_DIMS>
class ArrayReference
  : protected ArrayReference<T, DMPL_SHIFT_DIMS>,
    public StorageManager::detail::get_sm_info<T>::sm_type::template
      DimensionMixin<ArrayReference<T, DMPL_ALL_DIMS>,
      d0, ArrayReference<T, DMPL_SHIFT_DIMS>::static_rank + 1 >
#endif
{
protected:
#ifdef USE_VAR_TMPL
  typedef ArrayReference<T, dN...> raw_subarray_type;
#else
  typedef ArrayReference<T, DMPL_SHIFT_DIMS> raw_subarray_type;
#endif
public:
  typedef T storage_specifier;
  typedef StorageManager::detail::get_sm_info<T> sm_info;
  typedef typename sm_info::sm_type sm_type;
  typedef typename sm_info::data_type value_type;
  typedef typename sm_info::storage_type storage_type;
  typedef raw_subarray_type subarray_type;

  typedef ArrayReference this_type;

  typedef typename detail::ArrayReference_0<storage_specifier>::type base_type;
  typedef detail::IndexedArrayReference<this_type> reference_type;
  typedef detail::IndexedArrayReference<subarray_type> sub_reference_type;
  typedef detail::IndexedArrayReference<base_type> base_reference_type;

  typedef typename sub_reference_type::index_as_type index_type;
  typedef typename base_reference_type::index_as_type base_index_type;

  const static size_t static_size = d0;
  const static size_t static_rank = raw_subarray_type::static_rank + 1;

  typedef typename sm_type::template DimensionMixin<this_type, d0, static_rank>
          storage_mixin;

  typedef typename sm_type::template BaseMixin<base_type> base_storage_mixin;

  template<size_t dimension, bool dummy = true>
  struct get_dimension_type
  {
    static_assert(dimension < static_rank, "dimension exceeds rank of array");
    typedef typename raw_subarray_type::template
      get_dimension_type<dimension - 1, dummy>::type type;
  };

  template<bool dummy>
  struct get_dimension_type<0, dummy>
  {
    typedef this_type type;
  };

protected:
  template<size_t dimension DEFAULT_0>
  typename get_dimension_type<dimension>::type &get_dimension()
  {
    return static_cast<typename get_dimension_type<dimension>::type &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  constexpr const typename get_dimension_type<dimension>::type &
  get_dimension() const
  {
    return static_cast<const typename get_dimension_type<dimension>::type &>
      (*this);
  }

  template<size_t dimension, bool dummy = true>
  struct get_next_dimension_type
  {
    typedef typename raw_subarray_type::template
      get_dimension_type<dimension - 1, dummy>::type type;
  };

  template<bool dummy>
  struct get_next_dimension_type<0, dummy>
  {
    typedef raw_subarray_type type;
  };

  template<size_t dimension DEFAULT_0>
  typename get_next_dimension_type<dimension>::type &get_next_dimension()
  {
    return static_cast<
      typename get_next_dimension_type<dimension>::type &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  constexpr const typename get_next_dimension_type<dimension>::type
  &get_next_dimension() const
  {
    return static_cast<
      const typename get_next_dimension_type<dimension>::type &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  constexpr const typename get_dimension_type<dimension>::type::storage_mixin &
  get_storage_mixin() const
  {
    return static_cast<const typename
      get_dimension_type<dimension>::type::storage_mixin &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  typename get_dimension_type<dimension>::type::storage_mixin &
  get_storage_mixin()
  {
    return static_cast<
      typename get_dimension_type<dimension>::type::storage_mixin &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  constexpr const typename
  get_dimension_type<dimension>::type::base_storage_mixin &
  get_base_storage_mixin() const
  {
    return static_cast<const typename
      get_dimension_type<dimension>::type::base_storage_mixin &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  typename get_dimension_type<dimension>::type::base_storage_mixin &
  base_get_storage_mixin()
  {
    return static_cast<typename
      get_dimension_type<dimension>::type::base_storage_mixin &>(*this);
  }

public:
  using raw_subarray_type::set_settings;
  using raw_subarray_type::get_settings;
  using raw_subarray_type::get_settings_cref;

  template<size_t dimension DEFAULT_0>
  constexpr size_t size() const
  {
    return get_storage_mixin<dimension>().size();
  }

#ifndef USE_VAR_TMPL
  size_t size() const
  {
    return size<0>();
  }
#endif

  template<size_t dimension DEFAULT_0>
  constexpr size_t rank() const
  {
    return get_storage_mixin<dimension>().rank();
  }

#ifndef USE_VAR_TMPL
  size_t rank() const
  {
    return rank<0>();
  }
#endif

  template<size_t dimension DEFAULT_0>
  constexpr bool resizable() const
  {
    return get_storage_mixin<dimension>().resizable();
  }

#ifndef USE_VAR_TMPL
  bool resizable() const
  {
    return resizable<0>();
  }
#endif

  template<size_t dimension DEFAULT_0>
  void resize(size_t new_size)
  {
    get_storage_mixin<dimension>().resize(new_size);
  }

#ifdef USE_VAR_TMPL
  template<typename ...tN>
  void resize(size_t i0, size_t i1, tN ...iN)
  {
    resize(i0);
    get_dimension<1>().resize(i1, iN...);
  }
#else
  void resize(DMPL_DECL_ARGS)
  {
    resize<0>(i0);
    if(static_rank > 1)
      get_next_dimension<0>().resize(DMPL_SHIFT_PARAMS);
  }
#endif

  template<size_t dimension DEFAULT_0>
  bool check_bounds(size_t i) const
  {
    return get_storage_mixin<dimension>().check_bounds(i);
  }

#ifndef USE_VAR_TMPL
  bool check_bounds(size_t i) const
  {
    return check_bounds<0>(i);
  }
#endif

protected:
  template<size_t dimension DEFAULT_0>
  size_t get_multiplier() const
  {
    const size_t num_rank = get_dimension<dimension>().static_rank;
    if(num_rank <= 1)
      return 1;
    size_t s = get_next_dimension<dimension>().size<dimension>();
    if(num_rank == 2)
      return s;
    if(s == VAR_LEN)
      return VAR_LEN;
    return s * static_cast<const typename
      get_next_dimension_type<dimension>::type*>(this)->
        get_multiplier<dimension>();
  }

#ifdef USE_TYPE_TRAITS
private:
  void check_var_len(const char *fname)
  {
    if(static_size == VAR_LEN && size() == VAR_LEN)
      throw std::range_error(std::string(fname) +
        "() called on ArrayReference with unbounded VAR_LEN dimension");
  }

protected:
  using typename raw_subarray_type::variadic_barrier;
public:
  typedef typename std::remove_reference<base_index_type>::type &&for_each_type;

  /**
   * Calls op, which must be of callable type Op (e.g., function pointer, or
   * type which overloads operator() ) on every element in the array.
   * The first parameter passed to op will be a reference to a Reference-type
   * object (as if by fullying indexing the array to some element). Any
   * parameters beyond op passed to for_each will be passed through to op for
   * each element.
   *
   * May be called on the array itself, or on a partially indexed array, e.g.:
   *
   * ArrayReference<int, 3, 4, 5> a(kbase, "a");
   * a.for_each(someFunc, 1, 2); // Calls SomeFunc(x, 1, 2) on every element x
   * a[0][0].for_each(someFunc, 1, 2); // Calls SomeFunc(x, 1, 2) on the all
   *                                  // elements x of index [0][0][*]
   * @return the return value of the last time op gets called; i.e.:
   *         op((*this)[size<0>() - 1][size<1>() - 2]...[size<rank()>() - 1])
   **/
  template<typename Op, typename ...Args>
  auto for_each(Op op, Args&& ...args)
    -> decltype(op(std::declval<for_each_type>(), std::forward<Args>(args)...))
  {
    check_var_len("for_each");
    for(int i = 0; i < size() - 1; i++)
    {
      raw_subarray_type::for_each(op, (*this)[i], variadic_barrier(),
                                  std::forward<Args>(args)...);
    }
    return raw_subarray_type::for_each(op, (*this)[size() - 1],
                                       variadic_barrier(),
                                       std::forward<Args>(args)...);
  }

protected:
  template<typename Op, typename ...Args>
  auto for_each(Op op, reference_type &ref, variadic_barrier, Args&& ...args)
    -> decltype(op(std::declval<for_each_type>(), std::forward<Args>(args)...))
  {
    check_var_len("for_each");
    for(int i = 0; i < size() - 1; i++)
    {
      raw_subarray_type::for_each(op, ref[i], variadic_barrier(),
                                  std::forward<Args>(args)...);
    }
    return raw_subarray_type::for_each(op, ref[size() - 1],
                                       variadic_barrier(),
                                       std::forward<Args>(args)...);
  }

  template<typename Op, typename ...Args>
  auto for_each(Op op, reference_type &&ref, variadic_barrier, Args&& ...args)
    -> decltype(op(std::declval<for_each_type>(),
                  std::forward<Args>(args)...))
  {
    check_var_len("for_each");
    for(int i = 0; i < size() - 1; i++)
    {
      raw_subarray_type::for_each(op, ref[i],
                                  variadic_barrier(),
                                  std::forward<Args>(args)...);
    }
    return raw_subarray_type::for_each(op, std::move(ref)[size() - 1],
                                       variadic_barrier(),
                                       std::forward<Args>(args)...);
  }
#endif

public:
#ifdef USE_VAR_TMPL
  constexpr ArrayReference(ThreadSafeContext &con, const std::string &varName)
    : raw_subarray_type(con, nullptr, varName), storage_mixin(*this) {}

  constexpr ArrayReference(ThreadSafeContext &con,
      KnowledgeUpdateSettings *settings, const std::string &varName)
    : raw_subarray_type(con, settings, varName), storage_mixin(*this) {}

  /**
   * The settings passed into this constructor must be managed by the caller.
   * Destruction of the settings object passed to this constructor prior to
   * the desctruction of this object results in undefined behavior.
   **/
  template<typename... Args>
  constexpr ArrayReference(ThreadSafeContext &con,
        KnowledgeUpdateSettings *settings, const std::string &varName,
        size_t default_dim, Args... args)
    : raw_subarray_type(con, settings, varName, args...),
      storage_mixin(*this, default_dim) { }

  template<typename... Args>
  constexpr ArrayReference(ThreadSafeContext &con, const std::string &varName,
        size_t default_dim, Args... args)
    : ArrayReference(con, nullptr, varName, default_dim, args...) {}

  template<typename... Args>
  constexpr ArrayReference(KnowledgeBase &kbase, Args... args)
    : ArrayReference(kbase.get_context(), args...) {}

#else
  ArrayReference(ThreadSafeContext &con,
                 const std::string &varName, DMPL_DECL_ARGS)
    : raw_subarray_type(con, nullptr, varName, DMPL_SHIFT_PARAMS),
      storage_mixin(*this, i0) { }

  /**
   * The settings passed into this constructor must be managed by the caller.
   * Destruction of the settings object passed to this constructor prior to
   * the desctruction of this object results in undefined behavior.
   **/
  ArrayReference(ThreadSafeContext &con,
                 KnowledgeUpdateSettings *settings,
                 const std::string &varName, DMPL_DECL_ARGS)
    : raw_subarray_type(con, settings, varName, DMPL_SHIFT_PARAMS),
      storage_mixin(*this, i0) { }

  ArrayReference(KnowledgeBase &kbase,
                 const std::string &varName, DMPL_DECL_ARGS)
    : raw_subarray_type(kbase.get_context(), nullptr,
                        varName, DMPL_SHIFT_PARAMS),
      storage_mixin(*this, i0) { }

  /**
   * The settings passed into this constructor must be managed by the caller.
   * Destruction of the settings object passed to this constructor prior to
   * the desctruction of this object results in undefined behavior.
   **/
  ArrayReference(KnowledgeBase &kbase,
                 KnowledgeUpdateSettings *settings,
                 const std::string &varName, DMPL_DECL_ARGS)
    : raw_subarray_type(kbase.get_context(), settings,
                        varName, DMPL_SHIFT_PARAMS),
      storage_mixin(*this, i0) { }
#endif

#ifdef USE_VAR_TMPL
  template<typename U, size_t dNew0, size_t... dNewN>
  ArrayReference(const ArrayReference<U, dNew0, dNewN...> &o)
    : raw_subarray_type(static_cast<
          const DMPL_BASE_TYPE(o)::raw_subarray_type &
        >(o)),
      storage_mixin(*this) {}

  template<typename U>
  using as_type = ArrayReference<U, d0, dN...>;
  template<size_t ...dNewN>
  using as_size = ArrayReference<T, dNewN...>;
#endif

  /**
   * Constructs a new ArrayReference which refers to the same portion of
   * another array that is referred to by the reference r. E.g.,
   *
   * ArrayReference<int, 3, 4, 5> arr(kbase, "arr");
   * ArrayReference<int, 5> subarr(arr[0][2]);
   *
   * results in subarr referring to the 5-length subarray at indices [0][2].
   *
   * In other words, given this:
   *
   * ArrayReference<int, 5> subarr2(kbase, "arr.0.2);
   *
   * subarr and subarr2 are equivalent, and indexing one gives the same element
   * as the same index in the other.
   *
   * For Lazy and Proactive modes, the kept references in the original are NOT
   * copied over (possible in principle, but not implemented).
   **/
  explicit ArrayReference(const reference_type &r)
    : raw_subarray_type(r.get_sub_type(), r.get_name()),
      storage_mixin(*this, r.size()) {}

protected:
  ArrayReference(const reference_type &r, const std::string &name)
    : raw_subarray_type(r.get_sub_type(), name),
      storage_mixin(*this, r.size()) {}

public:
  /**
   * Indexes the array. In a one-dimensional array, the i'th element is
   * returned. For stateless arrays, the return value is like a
   * Reference<T>, but access through it is always O(log n), since it is not
   * meant to be kept and reused. To keep a reference to the return value, store
   * it in a Reference<T>; e.g.:
   *
   * ArrayReference<int, 3, 4, 5> arr(kbase, "arr");
   * Reference<int> ref(arr[0][1][2]);
   *
   * Now, accessing ref will have O(1) execution time.
   *
   * Avoid using "auto" to keep a ref; e.g.:
   *
   * auto slow_ref(arr[0][1][2]);
   *
   * With slow_ref, the type will be inferred to be something other than
   * Reference<int>. While this type will work correctly used this way, it will
   * have O(log n) access time instead of O(1). Additionally, slow_ref remains
   * bound to arr, and will only be valid so long as arr exists, and changing
   * the update settings of arr also changes the settings for slow_ref. On the
   * other hand, ref is entirely independant of arr once created.
   *
   * Otherwise, the reference type returned acts like a Reference<T> in all
   * functional respects. E.g.:
   *
   * arr[1][2][3] = 42; // stores 42 in madara variable "arr.1.2.3"
   * cout << arr[1][2][3] << end; // prints 42
   * ++arr[1][2][3]; // increments madara variable "arr.1.2.3" to 43
   *
   *
   * For multidimensional arrays, this operator returns a reference to the next
   * sub-dimension, which can in turn be indexed to get the next sub-dimension;
   * once a one-dimension sub-dimension is reached, it acts as described above.
   *
   * Sub-dimension references can be safely stored using "auto"; e.g.:
   *
   * auto sub_dim_ref(arr[0][1]);
   * sub_dim_ref[2]; // accesses arr[0][1][2]
   *
   * This sub_dim_ref is bound to the original arr, and is only valid so long as
   * arr is valid. It also uses the original arr's update settings.
   *
   * Alternatively, you can construct a new ArrayReference from a sub-dimension
   * reference:
   *
   * ArrayReference<int, 5> subarr(arr[0][1]);
   * subarr[2]; // accesses MADARA variable "arr.0.1.2", just like arr[0][1][2]
   *
   * You can use sub-dimension references to query information about the array:
   *
   * arr[0][1].size(); // returns 5, size of the third dimension
   * arr[1].rank(); // returns 2, for the two sub rank of arr[0]
   * arr[2].resizable(); // returns false, since the first dimension is static
   * arr[1].check_bounds(3); // returns true
   *
   * Additionally, the free functions available to manipulate entire arrays
   * (e.g., set, mark_modifed, push, pull) can also operate on sub-dimension
   * references returned by this operator; e.g.,
   *
   * set(arr[0][0], 88); // sets arr[0][0][0], arr[0][0][1], ... arr[0][0][4]
   *                     // to 88
   **/
  index_type operator[](size_t i)
  {
    reference_type ret(*this);
#ifdef USE_RVAL_REF
    return detail::handle_index_type<index_type>::do_index(ret, i);
#else
    return ret[i];
#endif
  }

  template<typename A>
  friend class detail::IndexedArrayReference;

  friend class detail::identity<sm_type>::type;

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

#ifdef USE_VAR_TMPL
  static constexpr const auto static_sizes = {d0, dN...};

  using static_sizes_seq = index_sequence<d0, dN...>;
  using indexes_seq = make_index_sequence<static_rank>;

  template<size_t ...N>
  using static_sizes_subseq = index_sequence<
    get_dimension_type<N>::type::static_size ... >;

  template<size_t ...N>
  static constexpr std::array<size_t, sizeof...(N)> get_static_sizes()
  {
    return std::array<size_t, sizeof...(N)>{
      get_dimension_type<N>::type::static_size ...
    };
  }

  template<size_t ...N>
  static constexpr std::array<size_t, sizeof...(N)>
  get_static_sizes(index_sequence<N...>)
  {
    return get_sizes<N...>();
  }

  static constexpr std::array<size_t, static_rank> get_static_sizes()
  {
    return std::array<size_t, static_rank>{d0, dN...};
  }

  template<size_t ...N>
  std::array<size_t, sizeof...(N)> get_sizes()
  {
    return std::array<size_t, sizeof...(N)>{size<N>()...};
  }

  template<size_t ...N>
  std::array<size_t, sizeof...(N)> get_sizes(index_sequence<N...>)
  {
    return get_sizes<N...>();
  }

  std::array<size_t, static_rank> get_sizes()
  {
    return get_sizes(indexes_seq());
  }
#else
  static std::vector<size_t> get_static_sizes()
  {
    std::vector<size_t> ret;
    get_static_sizes(ret);
    return ret;
  }

  std::vector<size_t> get_sizes() const
  {
    std::vector<size_t> ret;
    get_sizes(ret);
    return ret;
  }
#endif

protected:
#ifndef USE_VAR_TMPL
  static void get_static_sizes(std::vector<size_t> &out)
  {
    out.push_back((size_t)static_size); // cast to prevent reference
    subarray_type::get_static_sizes(out);
  }

  void get_sizes(std::vector<size_t> &out) const
  {
    out.push_back(size());
    subarray_type::get_sizes(out);
  }
#endif
};

namespace detail
{

  /**
   * For internal use only.
   *
   * Base class for all ArrayReference.objects. Note that ArrayReference is not
   * a polymorphic type. Do not directly use thie base class, or store
   * references to it.
   **/
  class ArrayReferenceBase : public ContextHost
  {
  public:
    const static size_t rank = 0;

    template<typename T>
    friend class IndexedArrayReference;

    const static size_t static_size = 1;
    const static size_t dim0 = 0;
    typedef ArrayReferenceBase subarray_type;
    typedef ArrayReferenceBase sub0;

    const std::string &get_name() const { return name; }

  protected:
    std::string name;

    ArrayReferenceBase(ThreadSafeContext &con,
        KnowledgeUpdateSettings *settings = nullptr,
        const std::string &varName = "") :
      ContextHost(con, settings), name(varName) {}

  #ifndef USE_STD_ARRAY
    static void get_static_sizes(std::vector<size_t> &out) {}
    void get_sizes(std::vector<size_t> &out) const {}
  #endif
  };

} // end detail namespace

/**
 * For internal use only.
 *
 * An ArrayReference of a given rank inherits from an ArrayReference of rank
 * one less, and so on. This is the "base-case" for this inheritence recursion.
 **/
#ifdef USE_VAR_TMPL
template <class T>
class ArrayReference<T>
  : public detail::ArrayReferenceBase,
    public StorageManager::detail::get_sm_info<T>::sm_type::template
      BaseMixin<ArrayReference<T> >
#else
template <class T>
class ArrayReference<T, DMPL_ZERO_DIMS>
  : public detail::ArrayReferenceBase,
    public StorageManager::detail::get_sm_info<T>::sm_type::template
      BaseMixin<typename detail::ArrayReference_0<T>::type >
#endif
{
public:
  typedef ArrayReference this_type;
  typedef this_type subarray_type;
  const static size_t static_rank = 0;
  const static size_t static_size = 1;

  typedef T storage_specifier;

  typedef StorageManager::detail::get_sm_info<T> sm_info;
  typedef typename sm_info::sm_type sm_type;
  typedef typename sm_info::data_type value_type;
  typedef typename sm_info::storage_type storage_type;

  typedef typename sm_type::template BaseMixin<this_type> storage_mixin;

  typedef detail::IndexedArrayReference<this_type> reference_type;

  typedef typename reference_type::index_as_type base_index_type;

  friend class detail::identity<sm_type>::type;

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

  template<size_t dimension, bool dummy = true>
  struct get_dimension_type
  {
    static_assert_false(dimension, "invalid dimension")
    typedef void type;
  };

  template<size_t dimension DEFAULT_0>
  constexpr const storage_mixin &get_storage_mixin() const
  {
    return static_cast<const storage_mixin &>(*this);
  }

  template<size_t dimension DEFAULT_0>
  storage_mixin &get_storage_mixin()
  {
    return static_cast<storage_mixin &>(*this);
  }

  template<size_t i DEFAULT_0>
  this_type &get_dimension()
  {
    return *this;
  }

  template<size_t i DEFAULT_0>
  constexpr const this_type &get_dimension() const
  {
    return *this;
  }

  template<size_t i DEFAULT_0>
  constexpr size_t size() const
  {
    return 1;
  }

protected:
  template<size_t i>
  constexpr size_t get_multiplier() const
  {
    return 1;
  }

#ifndef USE_VAR_TMPL
  void resize(DMPL_DECL_ARGS) { }
#endif

public:
#ifdef USE_TYPE_TRAITS
  typedef typename std::remove_reference<base_index_type>::type &&for_each_type;

protected:
  struct variadic_barrier {};

public:
  template<typename Op, typename E, typename ...Args>
  auto for_each(Op op, E &&in, variadic_barrier, Args&& ...args)
    -> decltype(op(std::forward<E>(in), std::forward<Args>(args)...))
  {
    return op(std::forward<E>(in), std::forward<Args>(args)...);
  }
#endif

  template<typename X>
  base_index_type operator[](X)
  {
    static_assert_false(X, "Error: Indexing 0-dimensional array");
  }

protected:
  constexpr ArrayReference
    (ThreadSafeContext &con,
      KnowledgeUpdateSettings *settings = nullptr,
      const std::string &varName = ""
#ifndef USE_VAR_TMPL
    , DMPL_DECL_ARGS
#endif
    ) : ArrayReferenceBase(con, settings, varName), storage_mixin(*this) {}

  explicit ArrayReference(const reference_type &r, const std::string &name)
    : ArrayReferenceBase(r.get_context(), r.get_settings(), name),
      storage_mixin(*this) {}

#ifdef USE_VAR_TMPL
  template<typename U>
  explicit ArrayReference(const ArrayReference<U> &o)
    : ArrayReferenceBase(o.get_context(), o.get_settings(), o.get_name()),
      storage_mixin(*this) {}
#endif
};

#ifdef USE_VAR_TMPL
template<typename U, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayReference<T, dN...> &o)
  -> DMPL_BASE_TYPE(o)::template as_type<U>
{
  using from_type = DMPL_BASE_TYPE(o);
  using to_type = typename from_type::template as_type<U>;
  return to_type(o);
}

template<size_t ...xN, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayReference<T, dN...> &o)
  -> DMPL_BASE_TYPE(o)::template as_size<xN...>
{
  using from_type = DMPL_BASE_TYPE(o);
  using to_type = typename from_type::template as_size<xN...>;
  static_assert(sizeof...(xN) == sizeof...(dN),
    "array_reference_cast cannot change rank");
  return to_type(o);
}

template<typename U, size_t x0, size_t ...xN, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayReference<T, dN...> &o)
  -> ArrayReference<U, x0, xN...>
{
  static_assert(sizeof...(xN) + 1 == sizeof...(dN),
    "array_reference_cast cannot change rank");
  return ArrayReference<U, x0, xN...>(o);
}

namespace detail
{
  template<typename to_type, typename via_type, typename from_type>
  struct staged_caster
  {
    static to_type staged_cast(const from_type &o)
    {
      return to_type(via_type(o));
    }
  };

  template<typename to_type, typename from_type>
  struct staged_caster<to_type, to_type, from_type>
  {
    static to_type staged_cast(const from_type &o)
    {
      return to_type(o);
    }
  };

  template<typename to_type, typename via_type, typename from_type>
  to_type staged_cast(const from_type &o)
  {
    return staged_caster<to_type,via_type,from_type>::staged_cast(o);
  }

}

template<typename T, size_t ...dN>
using ArrayIndexType = detail::IndexedArrayReference<ArrayReference<T, dN...>>;

template<typename U, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayIndexType<T, dN...> &o)
  -> DMPL_BASE_TYPE(o)::array_type::template as_type<U>
{
  using from_type = DMPL_BASE_TYPE(o)::array_type;;
  using to_type = typename from_type::template as_type<U>;
  return detail::staged_cast<to_type, from_type>(o);
}

template<size_t ...xN, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayIndexType<T, dN...> &o)
  -> DMPL_BASE_TYPE(o)::array_type::template as_size<xN...>
{
  using from_type = DMPL_BASE_TYPE(o)::array_type;;
  using to_type = typename from_type::template as_size<xN...>;
  static_assert(sizeof...(xN) == sizeof...(dN),
    "array_reference_cast cannot change rank");
  return detail::staged_cast<to_type, from_type>(o);
}

template<typename U, size_t x0, size_t ...xN, typename T, size_t ...dN>
inline auto array_reference_cast(const ArrayIndexType<T, dN...> &o)
  -> ArrayReference<U, x0, xN...>
{
  static_assert(sizeof...(xN) + 1 == sizeof...(dN),
    "array_reference_cast cannot change rank");
  return ArrayReference<U, x0, xN...>(ArrayReference<T, dN...>(o));
}
#endif

}
}
}

#include "StatelessStorage.hpp"

#endif
