// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   ContextHost.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

#ifndef DMPL_CONTEXT_HOST_HPP
#define DMPL_CONTEXT_HOST_HPP

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

namespace madara
{

namespace knowledge
{

namespace containers
{

namespace detail
{

namespace
{
  /**
   * All defaults, except don't expand variable names (siginificant
   * performance penalty)
   **/
  const KnowledgeUpdateSettings default_knowledge_settings(false, true,
                                                             false, false,
                                                             false, 1);
}

class ContextHost
{
protected:
  ThreadSafeContext &context;
#ifdef USE_ATOMIC
  std::atomic<KnowledgeUpdateSettings *> settings;
#else
  KnowledgeUpdateSettings *settings;
#endif

  ContextHost(KnowledgeBase &kbase)
    : context(kbase.get_context()), settings() {}

  constexpr ContextHost(ThreadSafeContext &con)
    : context(con), settings() {}

  constexpr ContextHost(ThreadSafeContext &con,
                        KnowledgeUpdateSettings *settings)
    : context(con), settings(settings) {}

  ContextHost(KnowledgeBase &kbase, KnowledgeUpdateSettings *settings)
    : context(kbase.get_context()), settings(settings) {}

  ContextHost(const ContextHost &o) noexcept
    : context(o.get_context()), settings(o.get_settings()) {}

public:
  constexpr ThreadSafeContext &get_context() const
  {
    return context;
  }

  /**
   * The settings passed into this method must be managed by the caller.
   * Destruction of the settings object passed to this method prior to
   * the desctruction of this object results in undefined behavior.
   *
   * Thread safety: safe with C++11, unsafe without.
   *
   * @return the previous settings
   **/
  KnowledgeUpdateSettings *
  set_settings(KnowledgeUpdateSettings *new_settings)
  {
    KnowledgeUpdateSettings *old_settings =
#ifdef USE_ATOMIC
      settings.exchange(new_settings, std::memory_order_acq_rel);
#else
      settings;

    settings = new_settings;
#endif
    return old_settings;
  }

  /**
   * Thread safety: safe with C++11, unsafe without.
   *
   * Use get_settings_cref instead wherever possible.
   *
   * @return the current settings (will be NULL if default)
   **/
  KnowledgeUpdateSettings *get_settings() const
  {
#ifdef USE_ATOMIC
    return settings.load(std::memory_order_acquire);
#else
    return settings;
#endif
  }

  /**
   * Thread safety: safe with C++11, unsafe without.
   *
   * Use this method over get_settings wherever possible.
   *
   * @return the current settings (will be a reference to the default
   * KnowledgeUpdateSettings this->get_settings() is null)
   **/
  const KnowledgeUpdateSettings &get_settings_cref() const
  {
#ifdef USE_ATOMIC
    const KnowledgeUpdateSettings *s =
      settings.load(std::memory_order_acquire);
    return s ? *s : default_knowledge_settings;
#else
    return settings ? *settings : default_knowledge_settings;
#endif
  }
};

}
}
}
}

#endif
