// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "AlgebraBase.h"

#ifndef ALGEBRA_H
#define ALGEBRA_H

namespace uxas
{
namespace common
{
namespace utilities
{  

// TYPE DEFINITIONS
typedef int64_t action_t;
typedef std::vector <int64_t> v_action_t;


// Algebra class
class CAlgebra:public CAlgebraBase
{
public:
    CAlgebra(void);
    bool initAtomicObjectives(const v_action_t &atomicObjectiveIDs);
    bool initAlgebraString(const std::string stringIn);
    void searchNext(const v_action_t &executedAtomicObjectives, v_action_t& nextAtomicObjectives);
    v_action_t searchPred(const v_action_t &executedAtomicObjectives, int atomicObjectiveIn);
};

}; //namespace log
}; //namespace common
}; //namespace uxas


#endif  //#define ALGEBRA_H
