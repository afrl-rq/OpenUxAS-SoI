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

#ifndef DMPL_KNOWLEDGE_CAST_HPP
#define DMPL_KNOWLEDGE_CAST_HPP

#include <string>
#include <stdbool.h>
#include <madara/knowledge/KnowledgeRecord.h>

namespace madara
{

namespace knowledge
{

/// By default, call constructor of target class;
/// for other semantics, define specializations
template<class O>
O knowledge_cast(const KnowledgeRecord &in)
{
  return O(in);
}

template<>
float knowledge_cast<float>(const KnowledgeRecord &in)
{
  return static_cast<float>(in.to_double());
}

template<>
double knowledge_cast<double>(const KnowledgeRecord &in)
{
  return static_cast<double>(in.to_double());
}

template<>
long double knowledge_cast<long double>(const KnowledgeRecord &in)
{
  return static_cast<long double>(in.to_double());
}

template<>
bool knowledge_cast<bool>(const KnowledgeRecord &in)
{
  return in.to_integer() ? true : false;
}

template<>
char knowledge_cast<char>(const KnowledgeRecord &in)
{
  return static_cast<char>(in.to_integer());
}

template<>
unsigned char knowledge_cast<unsigned char>(const KnowledgeRecord &in)
{
  return static_cast<unsigned char>(in.to_integer());
}

template<>
short knowledge_cast<short>(const KnowledgeRecord &in)
{
  return static_cast<short>(in.to_integer());
}

template<>
unsigned short knowledge_cast<unsigned short>(const KnowledgeRecord &in)
{
  return static_cast<unsigned short>(in.to_integer());
}

template<>
int knowledge_cast<int>(const KnowledgeRecord &in)
{
  return static_cast<int>(in.to_integer());
}

template<>
unsigned int knowledge_cast<unsigned int>(const KnowledgeRecord &in)
{
  return static_cast<unsigned int>(in.to_integer());
}

template<>
long int knowledge_cast<long int>(const KnowledgeRecord &in)
{
  return static_cast<long int>(in.to_integer());
}

template<>
unsigned long int knowledge_cast<unsigned long int>(const KnowledgeRecord &in)
{
  return static_cast<unsigned long int>(in.to_integer());
}

#if __STDC_VERSION__ >= 199901L

template<>
long long int knowledge_cast<long long int>(const KnowledgeRecord &in)
{
  return static_cast<long long int>(in.to_integer());
}

template<>
unsigned long long int knowledge_cast<unsigned long long int>(const KnowledgeRecord &in)
{
  return static_cast<unsigned long long int>(in.to_integer());
}

#endif

template<>
std::string knowledge_cast<std::string>(const KnowledgeRecord &in)
{
  return in.to_string();
}

template<>
KnowledgeRecord knowledge_cast<KnowledgeRecord>(const KnowledgeRecord &in)
{
  return in;
}

KnowledgeRecord knowledge_cast(const int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const unsigned int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const long int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const unsigned long int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

#if __STDC_VERSION__ >= 199901L

KnowledgeRecord knowledge_cast(const long long int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const unsigned long long int &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

#endif

KnowledgeRecord knowledge_cast(const short &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const unsigned short &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const char &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const unsigned char &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in));
}

KnowledgeRecord knowledge_cast(const bool &in)
{
  return KnowledgeRecord(KnowledgeRecord::Integer(in ? 1 : 0));
}

KnowledgeRecord knowledge_cast(const float &in)
{
  return KnowledgeRecord(static_cast<double>(in));
}

KnowledgeRecord knowledge_cast(const double &in)
{
  return KnowledgeRecord(in);
}

KnowledgeRecord knowledge_cast(const long double &in)
{
  return KnowledgeRecord(static_cast<double>(in));
}

KnowledgeRecord &knowledge_cast(KnowledgeRecord &in)
{
  return in;
}

const KnowledgeRecord &knowledge_cast(const KnowledgeRecord &in)
{
  return in;
}

}

}

#endif
