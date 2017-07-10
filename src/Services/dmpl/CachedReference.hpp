// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   CachedReference.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_CACHED_REFERENCE_HPP
#define DMPL_CACHED_REFERENCE_HPP

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
#include "ReferenceBase.hpp"
#include "ContextHost.hpp"

namespace madara
{

namespace knowledge
{

namespace containers
{

/**
 * MADARA container that provides reference-like semantics for accessing values
 * in the knowledge base, with a cache that allows for keeping and updating a
 * local copy of the value. Changes to the underlying knowledge base can be
 * received using the pull() method; to save changes made to the cached value
 * back to the knowledge base, use the push() method.
 *
 * Whenever a CachedReference is copied, the new copy will refer to the same
 * cached value as the original, and both will be affected by the same
 * assignments, pushes, and pulls. To "split" off a new independant copy, use
 * the clone() method.
 *
 * Thread safety: CachedReference<T> makes no thread safety guarantees
 **/
template<typename T>
class CachedReference : public detail::ReferenceBase<T, CachedReference<T> >,
                        protected detail::ContextHost
{
protected:
  typedef detail::ReferenceBase<T, CachedReference<T> > Base;
  typedef detail::ContextHost ContextStorage;

  enum { lock_for_get_set = false };

  struct data_t
  {
    const std::string name;
    bool exist:1;
    bool dirty:1;
    bool assigned:1;
    bool create:1;
    VariableReference var_ref;
    T data;
    mutable unsigned int ref_count;

    data_t(ThreadSafeContext &con, const std::string &name) : name(name),
      exist(con.exists(name)), dirty(false), assigned(false), create(false),
      var_ref(exist ? con.get_ref(name) : VariableReference()),
      data(exist ? knowledge_cast<T>(con.get(name)) : T()),
      ref_count(1) {}

    VariableReference &get_ref(ThreadSafeContext &con)
    {
      if(exist)
      {
        return var_ref;
      }
      else
      {
        var_ref = con.get_ref(name);
        exist = true;
        return var_ref;
      }
    }

    data_t *new_ref() noexcept
    {
      ++ref_count;
      return this;
    }

    const data_t *new_ref() const noexcept
    {
      ++ref_count;
      return this;
    }

    bool del_ref() const noexcept
    {
      return ((--ref_count) == 0);
    }

  private:
    data_t(const std::string &name, bool exist, bool dirty, bool assigned,
           bool create, VariableReference var_ref, const T &data)
      : name(name), exist(exist), dirty(dirty), assigned(assigned),
        create(create), var_ref(var_ref), data(data), ref_count(1) {}

  public:
#ifdef USE_UNIQUE_PTR
    std::unique_ptr<data_t> clone() const
    {
      return make_unique<data_t>(name, exist, dirty, assigned,
                                 create, var_ref, data);
    }
#else
    data_t *clone() const
    {
      return new data_t(name, exist, dirty, assigned,
                        create, var_ref, data);
    }
#endif
  };

  data_t *data;
public:

  CachedReference(ThreadSafeContext &con, const std::string &name)
    : ContextStorage(con), data(new data_t(con, name)) {}

  CachedReference(KnowledgeBase &kbase, const std::string &name)
    : ContextStorage(kbase), data(new data_t(kbase.get_context(), name)) {}

  CachedReference(ThreadSafeContext &con,
                  KnowledgeUpdateSettings *settings,
                  const std::string &name)
    : ContextStorage(con, settings), data(new data_t(con, name)) {}

  CachedReference(KnowledgeBase &kbase,
                  KnowledgeUpdateSettings *settings,
                  const std::string &name)
    : ContextStorage(kbase, settings),
      data(new data_t(kbase.get_context(), name)) {}

  CachedReference(const CachedReference &o) noexcept
    : ContextStorage(o), data(o.data->new_ref()) {}

#ifdef USE_RVAL_REF
  CachedReference(CachedReference &&o) noexcept
    : ContextStorage(std::move(o)), data(nullptr)
  {
    std::swap(data, o.data);
  }
#endif

  template<typename Impl>
  CachedReference(const detail::ReferenceBase<T, Impl> &o)
    : ContextStorage(o.get_context(), o.get_settings()),
      data(new data_t(o.get_context(), o.get_name())) {}

  ~CachedReference()
  {
    if(data && data->del_ref())
      delete data;
  }

  CachedReference &operator=(const CachedReference &in)
  {
    this->set(in.get());
    return *this;
  }
public:
  bool is_dirty() const
  {
    return data->dirty;
  }

  bool is_assigned() const
  {
    return data->assigned;
  }

  using Base::get_context;
  using Base::set_settings;
  using Base::get_settings;
  using Base::get_settings_cref;
  using Base::operator=;
protected:
  ThreadSafeContext &do_get_context() const
  {
    return ContextStorage::get_context();
  }

  /// Returns previous settings
  KnowledgeUpdateSettings *do_set_settings(
    KnowledgeUpdateSettings *new_settings)
  {
    return ContextStorage::set_settings(new_settings);
  }

  KnowledgeUpdateSettings *do_get_settings() const
  {
    return ContextStorage::get_settings();
  }

  const KnowledgeUpdateSettings &do_get_settings_cref() const
  {
    return ContextStorage::get_settings_cref();
  }

  std::string do_get_name() const
  {
    return data->name;
  }

  T do_get() const
  {
    return data->data;
  }

  KnowledgeRecord do_get_knowledge_record() const {
    return knowledge_cast(data->data);
  }

  void do_set_knowledge_record(
    const KnowledgeRecord &in,
    const KnowledgeUpdateSettings &settings)
  {
    set(knowledge_cast<T>(in), settings);
  }

  void do_set(const T& in, const KnowledgeUpdateSettings &settings)
  {
    if(!data->exist)
    {
      data->exist = true;
      data->create = true;
    }
    data->dirty = true;
    if(data->data != in)
    {
      data->assigned = true;
      data->data = in;
    }
  }

  void do_mark_modified()
  {
    data->dirty = true;
  }

  bool do_exists() const
  {
    return data->exist;
  }

  void ensure_exists()
  {
    if(data->create)
    {
      data->get_ref(this->get_context()) =
        this->get_context().get_ref(data->name, this->get_settings_cref());

      data->create = false;
    }
  }

public:
  void push()
  {
    if(is_dirty())
    {
      ensure_exists();
      if(is_assigned())
      {
        this->get_context().set(data->get_ref(this->get_context()),
                                knowledge_cast(data->data),
                                this->get_settings_cref());
      }
      else
      {
        this->get_context().mark_modified(
          data->get_ref(this->get_context()),
          this->get_settings_cref());
      }

      data->assigned = data->dirty = false;
    }
  }

  void pull()
  {
    ensure_exists();
    data->data = knowledge_cast<T>(this->get_context().get(
                     data->get_ref(this->get_context()),
                     this->get_settings_cref()));

    data->assigned = data->dirty = false;
  }

  void pull_keep_local()
  {
    if(!is_assigned())
      pull();
  }

private:
#ifdef USE_UNIQUE_PTR
  CachedReference(std::unique_ptr<data_t> data)
    : ContextStorage(static_cast<const ContextStorage &>(*this)),
      data(data.release()) {}
#else
  CachedReference(data_t *data)
    : ContextStorage(static_cast<const ContextStorage &>(*this)),
      data(data) {}
#endif

public:
  CachedReference clone() const
  {
    return CachedReference(data->clone());
  }

  friend class detail::identity<Base>::type;
};

#ifdef DMPL_CREATE_AGGREGATE_FN

DMPL_CREATE_AGGREGATE_MFN(push);
DMPL_CREATE_AGGREGATE_MFN(pull);
DMPL_CREATE_AGGREGATE_MFN(pull_keep_local);

#endif

}
}
}

#endif
