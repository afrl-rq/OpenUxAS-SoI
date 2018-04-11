// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// DRand.cpp : Various random number generators
// Contributed by Derek Kingston

#include <cmath>
#include <ctime> 
#include "DRand.h"

// generates a value in [0,1] distributed uniformly
double randu() { return (rand() + 0.0)/RAND_MAX; }

// return a zero-mean normally distributed random value with variance 1
// algorithm from "A Fast Normal Random Number Generator" by J. L. Leva,
// ACM Transactions on Mathematical Software, Vol. 18, No. 4, December 1992
double randn()
{
    static double s =  0.449871;
    static double t = -0.386595;
    static double a =  0.19600;
    static double b =  0.25472;
    static double c = 2.0*sqrt(2.0/exp(1.0));
    double u, v, x, y, Q;

    do
    {
        u = randu();
        v = c*(randu() - 0.5);
        x = u - s;
        y = fabs(v) - t;
        Q = x*x + y*(a*y - b*x);
    } while(Q > 0.27846 || u == 0.0 || v*v > -4*u*u*log(u));

    return v/u;
}

// returns mean 1 exponentially distributed random variable
double rande()
{
    return -log(randu());
}
