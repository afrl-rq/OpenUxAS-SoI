// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   knowledge_cast.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 10, 2017, 10:20 AM
 *
 */

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
