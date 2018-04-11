// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "DpssDataTypes.h"

void xyPoint::Rotate(double th)
{
    xyPoint t(x,y);
    x = cos(th)*t.x - sin(th)*t.y;
    y = sin(th)*t.x + cos(th)*t.y;
}

xyPoint xyPoint::Bisector(xyPoint& a, xyPoint& b, xyPoint& c)
{
    xyPoint q1,q2,q3,p;
    double beta;

    // normalize, remove if necessary
    q1 = b - a;
    q2 = c - b;

    if( q1.len() < 1e-6 )
    {
        p = q2;
        p.Rotate(dPi/2.0);
        return p;
    }

    if( q2.len() < 1e-6 )
    {
        p = q1;
        p.Rotate(dPi/2.0);
        return p;
    }

    beta = atan2(q1.y,q1.x) - atan2(q2.y,q2.x);
    p = q1;
    p.Rotate(beta/2.0);
    return p;
}

double Segment::distToPoint(const xyPoint& t)
{
    xyPoint p(t);
    xyPoint q = p - a;
    xyPoint r = b - a;
    double ql = q.len();
    double rl = r.len();
    if( ql < 1e-10 ) return ql;
    if( rl < 1e-10 ) return ql;
    return( (r.x*q.y - q.x*r.y)/(ql*rl) ); 
}

double Segment::distToClosestPoint(const xyPoint& t)
{
    xyPoint p = closestPoint(t);
    p -= t;
    return p.len();
}

int Segment::side(const xyPoint& t)
{
    xyPoint p(t);
    xyPoint q = p - a;
    xyPoint r = b - a;
    double d = r.x*q.y - q.x*r.y;
    if(fabs(d) < 1e-10) return 0;
    if(d > 0) return 1;
    return -1;
}

int Segment::swathSide(const xyPoint& p)
{
    xyPoint v = b - a;
    Segment aPerp(a,a + xyPoint(-v.y,v.x) );
    Segment bPerp(b,b + xyPoint(-v.y,v.x) );

    if(aPerp.side(p) <= 0 && bPerp.side(p) >= 0) return 0;
    if(aPerp.side(p) > 0) return 1;
    return -1;
}

bool Segment::intersect(const Segment& s)
{
    int aside = side(s.a);
    int bside = side(s.b);
    
    if(aside == 0) return true;
    if(bside == 0) return true;
    if(aside == bside) return false;
    return true;
}

xyPoint Segment::intersectPoint(const Segment& s)
{
    // line 1 formed as a1 x + b1 y + c1 = 0
    double a1 = b.y - a.y;
    double b1 = a.x - b.x;
    double c1 = b.x*a.y - a.x*b.y;

    // line 2 formed as a2 x + b2 y + c2 = 0
    double a2 = s.b.y - s.a.y;
    double b2 = s.a.x - s.b.x;
    double c2 = s.b.x*s.a.y - s.a.x*s.b.y;

    double denom = a1*b2 - a2*b1;
    if( fabs(denom) < 1e-10 ) return xyPoint(0.0,0.0,-1.0);

    return xyPoint( (b1*c2-b2*c1)/denom, (a2*c1-a1*c2)/denom );
}

xyPoint Segment::closestPoint(const xyPoint& t)
{
    xyPoint p(t);
    xyPoint v = b - a;
    Segment pline(p,p + xyPoint(-v.y,v.x) );
    v = intersectPoint(pline);

    if(v.z < 0.0) return a;

    int ss = swathSide(v);
    if(ss ==  1) return a;
    if(ss == -1) return b;
    return v;
}

double Segment::len()
{
    xyPoint v(b-a);
    return v.len();
}

double Segment::angle()
{
    xyPoint q1(b - a);
    
    if( q1.len() < 1e-6 )
        return 0.0;

    return atan2(q1.y,q1.x);
}