// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   ReferenceBase.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_REFERENCE_BASE_HPP
#define DMPL_REFERENCE_BASE_HPP

#include <utility>
#include <memory>
#include <string>
#include <vector>
#include <climits>
#include <sstream>
#include <typeinfo>
#include <exception>
#include <madara/knowledge/ThreadSafeContext.h>
#include <madara/knowledge/ThreadSafeContext.h>
#include <madara/knowledge/KnowledgeUpdateSettings.h>
#include "utility.hpp"
#include "knowledge_cast.hpp"

namespace madara
{

namespace knowledge
{

namespace containers
{

namespace detail
{

#ifdef USE_CPP11
template<typename T, typename Impl>
struct get_cast_operator
{
  explicit operator bool() const
  {
    return static_cast<const Impl*>(this)->is_true();
  }

  operator T() const {
    return static_cast<const Impl*>(this)->get();
  }
};

template<typename Impl>
struct get_cast_operator<bool, Impl>
{
  operator bool() const
  {
    return static_cast<const Impl*>(this)->is_true();
  }
};

struct is_a_reference_tag {};

#endif

template<typename T, typename Impl>
class ReferenceBase
#ifdef USE_CPP11
  : public get_cast_operator<T, Impl>, public is_a_reference_tag
#endif
{
protected:
  ReferenceBase() {}
  Impl* get_impl()
  {
    return static_cast<Impl*>(this);
  }

  const Impl* get_impl() const
  {
    return static_cast<const Impl*>(this);
  }
public:

  std::string get_name() const
  {
    return get_impl()->do_get_name();
  }

  ThreadSafeContext &get_context() const
  {
    return get_impl()->do_get_context();
  }

  /// Returns previous settings
  KnowledgeUpdateSettings *set_settings(
    KnowledgeUpdateSettings *new_settings)
  {
    return get_impl()->do_set_settings(new_settings);;
  }

  KnowledgeUpdateSettings *get_settings() const
  {
    return get_impl()->do_get_settings();;
  }

  const KnowledgeUpdateSettings &get_settings_cref() const
  {
    return get_impl()->do_get_settings_cref();
  }

  KnowledgeRecord get_knowledge_record() const {
    return get_impl()->do_get_knowledge_record();
  }

  void mark_modified()
  {
    get_impl()->do_mark_modified();
  }

  T get() const
  {
    return get_impl()->do_get();
  }

#ifndef USE_CPP11
  operator T() const {
    return get();
  }
#endif

  bool exists() const
  {
    return get_impl()->do_exists();
  }

  void set(const T& in)
  {
    set(in, get_settings_cref());
  }

  void set(const T& in, const KnowledgeUpdateSettings &settings)
  {
    get_impl()->do_set(in, settings);
  }

  void set_knowledge_record(const KnowledgeRecord &in)
  {
    set_knowledge_record(in, get_settings_cref());
  }

  void set_knowledge_record(
    const KnowledgeRecord &in,
    const KnowledgeUpdateSettings &settings)
  {
    get_impl()->do_set_knowledge_record(in, settings);
  }

protected:
  void do_mark_modified()
  {
    const KnowledgeUpdateSettings &settings = this->get_settings_cref();
    VariableReference ref = this->get_context().get_ref(this->get_name(),
                                                         settings);
    this->get_context().set(ref, this->get_context().get(ref,settings));
  }

  KnowledgeRecord do_get_knowledge_record() const {
    return this->get_context().get(this->get_name(),
                                   this->get_settings_cref());
  }

  bool do_exists() const
  {
    return get_context().exists(get_name(), get_settings_cref());
  }

  T do_get() const
  {
    return knowledge_cast<T>(get_knowledge_record());
  }

  void do_set_knowledge_record(
    const KnowledgeRecord &in,
    const KnowledgeUpdateSettings &settings)
  {
    this->get_context().set(this->get_name(), in, settings);
  }

  void do_set(const T& in, const KnowledgeUpdateSettings &settings)
  {
    set_knowledge_record(knowledge_cast(in), settings);
  }

public:
  KnowledgeRecord::Integer get_integer() const
  {
    return this->get_impl()->do_get_integer();
  }

  double get_double() const
  {
    return this->get_impl()->do_get_double();
  }

  std::string get_string() const
  {
    return this->get_impl()->do_get_string();
  }

protected:
  KnowledgeRecord::Integer do_get_integer() const
  {
    return get_knowledge_record().to_integer();
  }

  double do_get_double() const
  {
    return get_knowledge_record().to_double();
  }

  std::string do_get_string() const
  {
    return get_knowledge_record().get_string();
  }

public:
  template<typename R>
  R get_as() const
  {
    return knowledge_cast<R>(get_knowledge_record());
  }

  Impl &operator=(const ReferenceBase &in)
  {
    set(in.get());
    return *get_impl();
  }

  template<class E>
  Impl &operator=(const ReferenceBase<T, E> &in)
  {
    this->set(in.get());
    return *get_impl();
  }

  Impl &operator=(const T& in)
  {
    set(in);
    return *get_impl();
  }

  bool is_true() const
  {
    return this->get_impl()->do_is_true();
  }

protected:
  bool do_is_true() const
  {
    return exists() && (bool)get();
  }

public:
  bool is_false() const
  {
    return this->get_impl()->do_is_false();
  }

protected:
  bool do_is_false() const
  {
    return !is_true();
  }

public:
  bool operator!() const
  {
    return is_false();
  }

private:
  template <bool dummy = false>
  struct get_lock_context
  {
    enum { value = Impl::lock_for_get_set };
  };
  enum { lock_for_get_set = true };

  template <bool cond = true, bool = true>
  class ConditionalGuard
  {
  public:
    ConditionalGuard(ReferenceBase &ref) : context_(ref.get_context())
    {
      context_.lock();
    }

    ~ConditionalGuard()
    {
      context_.unlock();
    }

  private:
    ThreadSafeContext &context_;
  };

  template <bool dummy>
  class ConditionalGuard<false, dummy>
  {
  public:
    ConditionalGuard(ReferenceBase &ref) {}
  };

public:

#define DMPL_CREATE_MEMBER_COMPOUND_OP(op,name) \
public: \
  Impl &operator op##= (const T& in) \
  { \
    return this->get_impl()->operator##name(in); \
  } \
protected: \
  Impl &operator##name (const T& in) \
  { \
    ConditionalGuard<get_lock_context<>::value> lock(*this); \
    set(get() op in); \
    return *get_impl(); \
  } \
public: \
  enum{}

  DMPL_CREATE_MEMBER_COMPOUND_OP(+,plus);
  DMPL_CREATE_MEMBER_COMPOUND_OP(-,minus);
  DMPL_CREATE_MEMBER_COMPOUND_OP(*,times);
  DMPL_CREATE_MEMBER_COMPOUND_OP(/,divide);
  DMPL_CREATE_MEMBER_COMPOUND_OP(%,mod);
  DMPL_CREATE_MEMBER_COMPOUND_OP(^,xor);
  DMPL_CREATE_MEMBER_COMPOUND_OP(&,and);
  DMPL_CREATE_MEMBER_COMPOUND_OP(|,or);
  DMPL_CREATE_MEMBER_COMPOUND_OP(<<,lshift);
  DMPL_CREATE_MEMBER_COMPOUND_OP(>>,rshift);

  Impl &operator++()
  {
    *this += 1;
    return *get_impl();
  }

  Impl &operator--()
  {
    *this -= 1;
    return *get_impl();
  }

  T operator++(int)
  {
    ConditionalGuard<get_lock_context<>::value> lock(*this);
    T ret(get());
    set(ret + 1);
    return ret;
  }

  T operator--(int)
  {
    ConditionalGuard<get_lock_context<>::value> lock(*this);
    T ret(get());
    set(ret - 1);
    return ret;
  }

#ifdef USE_VAR_TMPL
  template<typename ...Args>
  auto operator()(Args&&... args)
    -> decltype(this->get()(std::forward<Args>(args)...))
  {
    return get()(std::forward<Args>(args)...);
  }

  template<typename U>
  auto operator[](U &&i) const
    -> decltype(this->get()[std::forward<U>(i)])
  {
    return this->get()[std::forward<U>(i)];
  }

  template<typename U>
  auto operator[](U &&i)
    -> decltype(this->get()[std::forward<U>(i)])
  {
    return this->get()[std::forward<U>(i)];
  }
#endif
};

}

#ifdef USE_DECLTYPE
#define DMPL_CREATE_FREE_UNARY_OP(op) \
  template<typename T, typename Impl, typename R> \
  inline auto operator op(const detail::ReferenceBase<T, Impl> &arg) \
    -> decltype(op(arg.get())) \
  { \
    return op(arg.get()); \
  } \
  enum {}
#else
#define DMPL_CREATE_FREE_UNARY_OP(op) \
  template<typename T, typename Impl, typename R> \
  inline T operator op(const detail::ReferenceBase<T, Impl> &arg) \
  { \
    return op(arg.get()); \
  } \
  enum {}
#endif

DMPL_CREATE_FREE_UNARY_OP(+);
DMPL_CREATE_FREE_UNARY_OP(-);
DMPL_CREATE_FREE_UNARY_OP(~);

#ifdef USE_DECLTYPE
namespace detail
{
  template<typename T>
  struct has_get
  {
    typedef char Yes;
    typedef struct{ Yes x[2]; } No;

    template<typename R>
    static auto test(void *) -> decltype(std::declval<R>().get(), Yes{});

    template<typename R>
    static auto test(...) -> No;

    static const bool value = (sizeof(test<T>(nullptr)) == sizeof(Yes));
  };
}

#define DMPL_CREATE_FREE_BINARY_OP(op) \
  template<typename L, typename R> \
  inline auto operator op(L &&lhs, R &&rhs) \
    -> decltype(std::forward<L>(lhs).get() op std::forward<R>(rhs).get()) \
  { \
    return std::forward<L>(lhs).get() op std::forward<R>(rhs).get(); \
  } \
  template<typename L, typename R, \
           DisableIf<detail::has_get<L>> = nullptr> \
  inline auto operator op(L &&lhs, R &&rhs) \
    -> decltype(std::forward<L>(lhs) op std::forward<R>(rhs).get()) \
  { \
    return std::forward<L>(lhs) op std::forward<R>(rhs).get(); \
  } \
  template<typename L, typename R, \
           DisableIf<detail::has_get<R>> = nullptr> \
  inline auto operator op(L &&lhs, R &&rhs) \
    -> decltype(std::forward<L>(lhs).get() op std::forward<R>(rhs)) \
  { \
    return std::forward<L>(lhs).get() op std::forward<R>(rhs); \
  } \
  enum {}
#else
#define DMPL_CREATE_FREE_BINARY_OP(op) \
  template<typename T, typename Impl, typename R> \
  inline T operator op(const detail::ReferenceBase<T, Impl> &lhs, const R&rhs) \
  { \
    return lhs.get() op rhs; \
  } \
  enum {}
#endif

DMPL_CREATE_FREE_BINARY_OP(+);
DMPL_CREATE_FREE_BINARY_OP(-);
DMPL_CREATE_FREE_BINARY_OP(*);
DMPL_CREATE_FREE_BINARY_OP(/);
DMPL_CREATE_FREE_BINARY_OP(%);
DMPL_CREATE_FREE_BINARY_OP(^);
DMPL_CREATE_FREE_BINARY_OP(&);
DMPL_CREATE_FREE_BINARY_OP(|);
DMPL_CREATE_FREE_BINARY_OP(<<);
DMPL_CREATE_FREE_BINARY_OP(>>);

DMPL_CREATE_FREE_BINARY_OP(==);
DMPL_CREATE_FREE_BINARY_OP(!=);
DMPL_CREATE_FREE_BINARY_OP(<);
DMPL_CREATE_FREE_BINARY_OP(<=);
DMPL_CREATE_FREE_BINARY_OP(>);
DMPL_CREATE_FREE_BINARY_OP(>=);

template<typename T, typename Impl>
std::ostream &operator<<(std::ostream &o,
                         const detail::ReferenceBase<T, Impl> &r)
{
  o << r.get();
  return o;
}

template<typename T, typename Impl>
std::istream &operator>>(std::istream &i, detail::ReferenceBase<T, Impl> &r)
{
  T temp;
  i >> temp;
  r.set(temp);
  return i;
}

#ifdef USE_TYPE_TRAITS

namespace detail
{
  /* Based on public code from http://ideone.com/AmaBrN
   * License is fully free, see http://ideone.com/terms
   *        (https://web.archive.org/web/20150905100212/http://ideone.com/terms)
   * Relevent section (5):
   *  When submitting on ideone.com service pastes to which everyone has access,
   *  the user irrevocably grants all other users of the ideone.com service the
   *  right to view, download, fork and re-run the code
   */
  template <typename T, typename ...Args>
  class has_for_each {
  public:
    typedef char Yes;
    typedef Yes No[2];

    template<typename C> static auto Test(void*) ->
      decltype((void)std::declval<C>().for_each(std::declval<Args>()...),Yes{});

    template<typename> static No& Test(...);

  public:
    static bool const value = sizeof(Test<T>(0)) == sizeof(Yes);
  };
}

#define DMPL_CHECK_HAS_FOR_EACH(R,...) \
    detail::has_for_each<typename std::remove_reference<R>::type, void(*)(...), __VA_ARGS__>

#define DMPL_DISABLE_IF_HAS_FOR_EACH(R,...) \
  DisableIf<DMPL_CHECK_HAS_FOR_EACH(R,__VA_ARGS__)>

#define DMPL_ENABLE_IF_HAS_FOR_EACH(R,...) \
  EnableIf<DMPL_CHECK_HAS_FOR_EACH(R,__VA_ARGS__)>

#define COMMA ,

#define DMPL_CREATE_FREE_FROM_MEMBER(free_name, mfn_name) \
  namespace detail \
  { \
    template<typename R, typename ...Args> \
    using result_of_##mfn_name = decltype( \
      std::forward<R>(std::declval<R>()).mfn_name( \
           std::forward<Args>(std::declval<Args>())...)); \
  } \
\
  template<typename R, typename ...Args, \
    DMPL_DISABLE_IF_HAS_FOR_EACH(R, Args...) = nullptr> \
  inline auto free_name(R &&r, Args&&... args) \
    -> detail::result_of_##mfn_name<R, Args...> \
  { \
    return std::forward<R>(r).mfn_name(std::forward<Args>(args)...); \
  } \
  enum {}

#define DMPL_CREATE_AGGREGATE_FN(name,fn_name) \
  namespace detail { \
    struct lambda_##name \
    { \
      template<typename R, typename ...Args> \
      void operator()(R &&r, Args&& ...args) \
      { \
        fn_name(std::forward<R>(r), std::forward<Args>(args)...); \
      } \
    }; \
  } \
  template<typename A, typename ...Args, \
    DMPL_ENABLE_IF_HAS_FOR_EACH(A, Args...) = nullptr> \
  inline void name(A &&a, Args&&... args) \
  { \
    std::forward<A>(a).for_each(detail::lambda_##name(), \
                                std::forward<Args>(args)...); \
  } \
enum {}

#define DMPL_CREATE_AGGREGATE_MFN2(name, mfn_name) \
  DMPL_CREATE_FREE_FROM_MEMBER(name, mfn_name); \
  DMPL_CREATE_AGGREGATE_FN(name,name);\
  enum {}

#define DMPL_CREATE_AGGREGATE_MFN(name) DMPL_CREATE_AGGREGATE_MFN2(name, name)

template<typename R, DMPL_DISABLE_IF_HAS_FOR_EACH(R, std::ostream&) = nullptr>
inline std::ostream& print_lines(R &&r, std::ostream &s = std::cerr)
{
  return s << std::forward<R>(r).get() << std::endl;
}

DMPL_CREATE_FREE_FROM_MEMBER(get,get);

DMPL_CREATE_AGGREGATE_FN(print_lines,print_lines);

DMPL_CREATE_AGGREGATE_MFN(mark_modified);
DMPL_CREATE_AGGREGATE_MFN(set);

#endif

}
}
}

#endif
