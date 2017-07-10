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

#ifndef DMPL_REFERENCE_HPP
#define DMPL_REFERENCE_HPP

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
 * in the knowledge base.
 *
 * Thread safety: Reference<T> is immutable, and therefore thread safe, except
 *    for usage of set_settings. With C++11, set_settings is also thread safe.
 **/
template<typename T>
class Reference : public detail::ReferenceBase<T, Reference<T> >,
                  protected detail::ContextHost
{
protected:
  typedef detail::ReferenceBase<T, Reference<T> > Base;
  typedef detail::ContextHost ContextStorage;

#ifdef USE_CPP11
  const VariableReference var_ref;
#else
  // to support putting Reference in a vector, pre-C++11, must be assignable
  VariableReference var_ref;
#endif

public:
  Reference(const Reference &o) noexcept
    : ContextStorage(o), var_ref(o.var_ref) { }

#ifdef USE_RVAL_REF
  Reference(Reference &&o) noexcept
    : ContextStorage(std::move(o)), var_ref(std::move(o.var_ref)) {}
#endif

  Reference(ThreadSafeContext &con, const std::string &name)
    : ContextStorage(con), var_ref(con.get_ref(name)) {}

  Reference(KnowledgeBase &kbase, const std::string &name)
    : ContextStorage(kbase), var_ref(this->get_context().get_ref(name)) {}

  Reference(ThreadSafeContext &con,
            KnowledgeUpdateSettings *settings,
            const std::string &name)
    : ContextStorage(con, settings), var_ref(con.get_ref(name, settings)) {}

  Reference(KnowledgeBase &kbase,
            KnowledgeUpdateSettings *settings,
            const std::string &name)
    : ContextStorage(kbase, settings),
      var_ref(this->get_context().get_ref(name, settings)) {}

  template<typename Impl>
  Reference(const detail::ReferenceBase<T, Impl> &o)
    : ContextStorage(o.get_context(), o.get_settings()),
      var_ref(o.get_context().get_ref(o.get_name())) {}

  Reference &operator=(const Reference &in)
  {
    this->set(in.template get(), this->get_settings_cref());
    return *this;
  }

  using Base::operator=;
  using Base::get_context;
  using Base::set_settings;
  using Base::get_settings;
  using Base::get_settings_cref;


protected:
  std::string do_get_name() const
  {
    // const_cast required to workaround missing const decorator;
    // current implementation is actually const
    return std::string(
      const_cast<VariableReference&>(this->var_ref).get_name());
  }

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

  void do_mark_modified()
  {
    this->get_context().mark_modified(var_ref);
  }

  KnowledgeRecord do_get_knowledge_record() const {
    return this->get_context().get(var_ref, this->get_settings_cref());
  }

  const KnowledgeRecord &do_set_knowledge_record(
    const KnowledgeRecord &in,
    const KnowledgeUpdateSettings &settings)
  {
    this->get_context().set(var_ref, in, settings);
    return in;
  }

  friend class detail::identity<Base>::type;
};

}
}
}

#endif
