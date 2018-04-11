// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#pragma once
#include <math.h>

const double dPi = 3.14159265358979323846;
const double dDeg2Rad = 3.14159265358979323846/180.0;
const double dRad2Deg = 180.0/3.14159265358979323846;


namespace Dpss_Data_n
{

class xyPoint
{
public:
    enum PointAttributes {
        None = 0x00,
        Station = 0x01,
        Loiter = 0x02
    };

    xyPoint():x(0.0),y(0.0),z(0.0),attributes(None),id(0){};
    xyPoint(double dX,double dY,double dZ):x(dX),y(dY),z(dZ),attributes(None),id(0){};
    xyPoint(double dX,double dY):x(dX),y(dY),z(0.0),attributes(None),id(0){};
    xyPoint(const xyPoint& rhs):x(rhs.x),y(rhs.y),z(rhs.z),attributes(rhs.attributes),id(rhs.id){};
    void operator =(const xyPoint& rhs){x = rhs.x;y = rhs.y;z = rhs.z;attributes=rhs.attributes;id=rhs.id;};

    xyPoint operator +(const xyPoint& rhs){ return xyPoint(x + rhs.x, y + rhs.y, z + rhs.z); };
    xyPoint operator -(const xyPoint& rhs){ return xyPoint(x - rhs.x, y - rhs.y, z - rhs.z); };
    xyPoint operator *(const double& s){ return xyPoint(x*s, y*s, z*s); };
    xyPoint operator /(const double& s){ return xyPoint(x/s, y/s, z/s); };

    void operator +=(const xyPoint& rhs){ x += rhs.x; y += rhs.y; z += rhs.z; };
    void operator -=(const xyPoint& rhs){ x -= rhs.x; y -= rhs.y; z -= rhs.z; };
    void operator *=(const double& s){ x *= s; y *= s; z *= s; };
    void operator /=(const double& s){ x /= s; y /= s; z /= s; };

    double dist(const xyPoint& a) { return sqrt( pow(a.x - x,2.0) + pow(a.y - y,2.0) ); };
    double len() { return sqrt( x*x + y*y ); };
    double angle2d(const xyPoint& a) { return atan2(a.y,a.x) - atan2(y,x); };
    double heading2d(const xyPoint& a) { return atan2((a.y-y),(a.x-x)); }; // assumes x-north, y-east
    void Rotate(double th);

    static xyPoint Bisector(xyPoint& a, xyPoint& b, xyPoint& c);

    double x;
    double y;
    double z;
    PointAttributes attributes;
    unsigned int id;
};

class Segment
{
public:
    Segment():a(0.0,0.0,0.0),b(0.0,0.0,0.0){};
    Segment(const xyPoint& p):a(0.0,0.0,0.0),b(p){};
    Segment(const xyPoint& p, const xyPoint& q):a(p),b(q){};
    void operator =(const Segment& rhs){ a = rhs.a; b = rhs.b; };

    Segment operator +(const Segment& rhs){ return Segment(a+rhs.a, b+rhs.b); };
    Segment operator -(const Segment& rhs){ return Segment(a-rhs.a, b-rhs.b); };
    Segment operator *(const double& s){ return Segment(a*s, b*s); };
    Segment operator /(const double& s){ return Segment(a/s, b/s); };

    void operator +=(const Segment& rhs){ a += rhs.a; b += rhs.b; };
    void operator -=(const Segment& rhs){ a -= rhs.a; b -= rhs.b; };
    void operator *=(const double& s){ a *= s; b *= s; };
    void operator /=(const double& s){ a /= s; b /= s; };

    double distToPoint(const xyPoint& t);
    int side(const xyPoint& t);
    int swathSide(const xyPoint& p);
    bool intersect(const Segment& s);
    xyPoint intersectPoint(const Segment& s);
    xyPoint closestPoint(const xyPoint& t);
    double distToClosestPoint(const xyPoint& t);
    double len();
    double angle();

    xyPoint a;
    xyPoint b;
};

class cBalanceStatus
{
public:
    cBalanceStatus():position(-1.0),destination(-1.0),direction(0),followOnWp(0xffff),id(0),inManuever(false){};
    cBalanceStatus( const double pos, const int vehicleID, int dir):position(pos),destination(-1.0),direction(dir),followOnWp(0xffff),id(vehicleID),inManuever(false){};
    void operator =(const cBalanceStatus& rhs){ position = rhs.position; destination = rhs.destination; direction = rhs.direction; followOnWp = rhs.followOnWp; id = rhs.id; inManuever = rhs.inManuever; };

    double position;
    double destination;
    int direction;
    unsigned short followOnWp;
    int id;
    bool inManuever;
};



};    //namespace Dpss_Data

using namespace Dpss_Data_n;