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
