#include "RouteExtension.h"
#include "Constants/Convert.h"

namespace uxas
{
namespace common
{
namespace utilities
{

bool RouteExtension::ExtendPath(std::vector<afrl::cmasi::Waypoint*>& wplist, int64_t extendTime_ms, double R, double d)
{
    // must have at least one segment in path
    if(wplist.size() < 2)
        return false;

    size_t index = 0;
    double vel = wplist[index]->getSpeed();
    if(vel < 1e-4) return false;
    double extendlen = (extendTime_ms+0.0)/1000.0*vel;
    double minlen = RequiredSegmentLength(extendlen, R);

    FlatEarth flatEarth;
    double north, east;
    flatEarth.ConvertLatLong_degToNorthEast_m(wplist[index]->getLatitude(), wplist[index]->getLongitude(), north, east);
    DubinsWaypoint startwp(east, north, 0.0, 0.0, 0.0, 0);
    index++;

    size_t maxLengthClearSegment{0};
    double clearedLength{0.0};
    double extendlen_max{0.0};
    double minNeeded_max{0.0};

    // assume *ordered* waypoint list
    while(index < wplist.size())
    {
        flatEarth.ConvertLatLong_degToNorthEast_m(wplist[index]->getLatitude(), wplist[index]->getLongitude(), north, east);
        DubinsWaypoint endwp(east, north, 0.0, 0.0, 0.0, 0);

        // update extension length if speed change
        if( fabs(vel - wplist[index]->getSpeed()) > 1e-4 && wplist[index]->getSpeed() > 1e-4 )
        {
            // update extend length based on changing speed
            vel = wplist[index]->getSpeed();
            extendlen = (extendTime_ms+0.0)/1000.0*vel;
            minlen = RequiredSegmentLength(extendlen, R);
        }

        // TODO: check segment for clearance of 2*R

        // find longest segment that allows extension
        double seglen = sqrt( (endwp.x-startwp.x)*(endwp.x-startwp.x) + (endwp.y-startwp.y)*(endwp.y-startwp.y) );
        if(seglen >= minlen && seglen > clearedLength)
        {
            clearedLength = seglen;
            maxLengthClearSegment = index-1;
            extendlen_max = extendlen;
            minNeeded_max = minlen;
        }

        startwp = endwp;
        index++;
    }

    if(clearedLength > 1e-4)
    {
        flatEarth.ConvertLatLong_degToNorthEast_m(wplist[maxLengthClearSegment]->getLatitude(),
                                    wplist[maxLengthClearSegment]->getLongitude(), north, east);
        DubinsWaypoint start_wp(east, north, 0.0, 0.0, 0.0, 0);
        flatEarth.ConvertLatLong_degToNorthEast_m(wplist[maxLengthClearSegment+1]->getLatitude(),
                                    wplist[maxLengthClearSegment+1]->getLongitude(), north, east);
        DubinsWaypoint end_wp(east, north, 0.0, 0.0, 0.0, 0);
        index = maxLengthClearSegment+1;

        // move start up to center the extension
        double forwardPercent = ( (clearedLength - minNeeded_max)/2.0 )/clearedLength;
        start_wp.x += (end_wp.x - start_wp.x)*forwardPercent;
        start_wp.y += (end_wp.y - start_wp.y)*forwardPercent;
        afrl::cmasi::Waypoint* startManeuver = wplist[index]->clone();
        double lat, lon;
        flatEarth.ConvertNorthEast_mToLatLong_deg(start_wp.y, start_wp.x, lat, lon);
        startManeuver->setLatitude(lat);
        startManeuver->setLongitude(lon);

        // saving ID of next original point after extension
        int64_t wp_id = wplist[index]->getNumber();
        wplist.insert(wplist.begin()+index, startManeuver);

        // build extension waypoints
        std::vector<DubinsWaypoint> dubins_extension = ExtendSegment(start_wp, end_wp, extendlen_max, R);
        std::vector<afrl::cmasi::Waypoint*> extension = DiscretizeExtension(dubins_extension, d, flatEarth, wplist[index]);
        wplist.insert(wplist.begin()+index+1, extension.begin(), extension.end());

        // re-number and re-build 'next' fields (linked list)
        while(index < wplist.size())
        {
            wplist[index]->setNumber(wp_id);
            wplist[index++]->setNextWaypoint(++wp_id);
        }
        wplist.back()->setNextWaypoint(wplist.back()->getNumber());
        return true;
    }

    return false;
}

std::vector<afrl::cmasi::Waypoint*> RouteExtension::DiscretizeExtension(std::vector<DubinsWaypoint>& dubins_extension, double d, FlatEarth& flatEarth, afrl::cmasi::Waypoint* baseWp)
{
    // convert to standard cmasi waypoints with appropriate discretization
    std::vector<afrl::cmasi::Waypoint*> extension;
    double lat, lon;
    int64_t index = 1;
    for(auto dwp : dubins_extension)
    {
        if(dwp.turndir != 0)
        {
            double R = sqrt( (dwp.x - dwp.tx)*(dwp.x - dwp.tx) + (dwp.y - dwp.ty)*(dwp.y - dwp.ty) );
            double dx = dwp.x - dwp.tx;
            double dy = dwp.y - dwp.ty;
            double th = dwp.turndir*dwp.len/R;
            double cth = cos(th);
            double sth = sin(th);
            double vx =  cth*dx + sth*dy;
            double vy = -sth*dx + cth*dy;
            int32_t M = static_cast<int32_t> (floor(dwp.len/d)) - 1;
            if(M > 0)
            {
                double gam = -dwp.turndir*dwp.len/R/(M+1.0);
                double cgam = cos(gam);
                double sgam = sin(gam);
                for(auto m=0; m<M; m++)
                {
                    double x =  cgam*vx + sgam*vy;
                    double y = -sgam*vx + cgam*vy;
                    vx = x;
                    vy = y;
                    flatEarth.ConvertNorthEast_mToLatLong_deg(y+dwp.ty, x+dwp.tx, lat, lon);
                    auto cwp = baseWp->clone();
                    cwp->setLatitude(lat);
                    cwp->setLongitude(lon);
                    cwp->setNumber(index);
                    cwp->setNextWaypoint(++index);
                    extension.push_back(cwp);
                }
            }
        }

        // add final waypoint
        auto fwp = baseWp->clone();
        flatEarth.ConvertNorthEast_mToLatLong_deg(dwp.y, dwp.x, lat, lon);
        fwp->setLatitude(lat);
        fwp->setLongitude(lon);
        fwp->setNumber(index);
        fwp->setNextWaypoint(++index);
        extension.push_back(fwp);
    }

    return extension;
}

std::vector<DubinsWaypoint> RouteExtension::ExtendSegment(DubinsWaypoint& startwp, DubinsWaypoint& endwp, double extendlen, double R)
{
    const double pi = n_Const::c_Convert::dPi();
    if(extendlen < 2.0*R*(pi-2.0))
    {
        // single bubble
        double th = SingleBubbleBisectionSearch(extendlen, R);
        return BuildSingleBubble(th, R, startwp, endwp);
    }

    if(extendlen < 2.0*pi*R)
    {
        // slide back
        double th = SlideBisectionSearch(extendlen, R);
        return BuildSlideBack(th, R, startwp, endwp);
    }

    // racetrack
    int32_t N = static_cast<int32_t>(floor(extendlen/2.0/pi/R)) - 1; // how many times around minus the last racetrack
    if(N < 0) N = 0;
    double tracklen = fmod(extendlen, 2.0*pi*R)/2.0; // left over length, halved (once forward, once back)
    return BuildRaceTrack(N, tracklen, R, startwp, endwp);
}

double RouteExtension::RequiredSegmentLength(double extendlen, double R)
{
    const double pi = n_Const::c_Convert::dPi();
    if(extendlen < 2.0*R*(pi-2.0))
    {
        // single bubble
        double th = SingleBubbleBisectionSearch(extendlen, R);
        return SingleStraightLen(th, R);
    }

    if(extendlen < 2.0*pi*R)
    {
        // slide back
        double th = SlideBisectionSearch(extendlen, R);
        return SlideStraightLen(th, R);
    }

    // racetrack
    int32_t N = static_cast<int32_t>(floor(extendlen/2.0/pi/R)) - 1; // how many times around minus the last racetrack
    if(N < 0) N = 0;
    return fmod(extendlen, 2.0*pi*R)/2.0; // left over length, halved (once forward, once back)
}

double RouteExtension::SingleArcLen(double th, double R)
{
    return 4.0*R*th;
}

double RouteExtension::SingleStraightLen(double th, double R)
{
    return 4.0*R*sin(th);
}

double RouteExtension::SingleBubbleExtensionError(double th, double extendlen, double R)
{
    return extendlen + SingleStraightLen(th, R) - SingleArcLen(th, R);
}

// follows https://codereview.stackexchange.com/questions/179516/finding-the-root-of-a-function-by-bisection-method
// with min and max theta values set by design for the 'single bubble' root extension function
double RouteExtension::SingleBubbleBisectionSearch(double extendlen, double R)
{
    const double eps = 1e-8;
    double min_th = 0;
    double max_th = n_Const::c_Convert::dPi()/2.0;

    double f_min = SingleBubbleExtensionError(min_th, extendlen, R);
    while (min_th + eps < max_th)
    {
        double mid_th = 0.5 * min_th + 0.5 * max_th;
        double f_mid = SingleBubbleExtensionError(mid_th, extendlen, R);

        if ((f_min < 0) == (f_mid < 0))
        {
            min_th = mid_th;
            f_min = f_mid;
        }
        else
        {
            max_th = mid_th;
        }
    }

    return min_th;
}

double RouteExtension::SlideArcLen(double th, double R)
{
    const double pi = n_Const::c_Convert::dPi();

    // header arc
    double a_init = 3.0*pi/2.0*R;

    // from header to slide
    double a_onto = th*R;

    // around slide
    double gam = acos(1-sin(th));
    double del = pi/2.0 + gam + th;
    double a_slide = del*R;

    // off slide
    double a_off = gam*R;

    return a_init + a_onto + a_slide + a_off;
}

double RouteExtension::SlideStraightLen(double th, double R)
{
    // header arc
    double d_init = 2.0*R;

    // from header to slide
    double d_slide = 2.0*R*cos(th);

    // off of slide
    double d_off = 2.0*R*sqrt(1-(1-sin(th))*(1-sin(th)));

    return d_init + d_slide + d_off;
}

double RouteExtension::SlideExtensionError(double th, double extendlen, double R)
{
    return extendlen + SlideStraightLen(th, R) - SlideArcLen(th, R);
}

// follows https://codereview.stackexchange.com/questions/179516/finding-the-root-of-a-function-by-bisection-method
// with min and max theta values set by design for the 'slide back' root extension function
double RouteExtension::SlideBisectionSearch(double extendlen, double R)
{
    const double eps = 1e-8;
    double min_th = 0;
    double max_th = n_Const::c_Convert::dPi()/2.0;

    double f_min = SlideExtensionError(min_th, extendlen, R);
    while (min_th + eps < max_th)
    {
        double mid_th = 0.5 * min_th + 0.5 * max_th;
        double f_mid = SlideExtensionError(mid_th, extendlen, R);

        if ((f_min < 0) == (f_mid < 0))
        {
            min_th = mid_th;
            f_min = f_mid;
        }
        else
        {
            max_th = mid_th;
        }
    }

    return min_th;
}

std::vector<DubinsWaypoint> RouteExtension::BuildRaceTrack(int32_t N, double tracklen, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp)
{
    const double pi = n_Const::c_Convert::dPi();
    double psi = atan2(endwp.y - startwp.y, endwp.x - startwp.y);
    double x = startwp.x;
    double y = startwp.y;

    std::vector<DubinsWaypoint> w;

    double tx = x - R*sin(psi);
    double ty = y + R*cos(psi);

    // add N circles of radius R
    for(int n=0; n<N; n++)
    {
        for(int p=0; p<4; p++) // each circle has 4 segments
        {
            double nx = -y + ty + tx;
            y  =  x - tx + ty;
            x  = nx;
            psi = psi + pi/2.0;
            w.push_back(DubinsWaypoint(x,y,pi/2.0*R,tx,ty,1));
        }
    }

    // straight segment
    x = x + tracklen*cos(psi);
    y = y + tracklen*sin(psi);
    w.push_back(DubinsWaypoint(x,y,tracklen,0,0,0));

    // race track: backtrack
    tx = x - R*sin(psi);
    ty = y + R*cos(psi);
    for(int i=0; i<2; i++)
    {
        double nx = -y + ty + tx;
        y  =  x - tx + ty;
        x  = nx;
        psi = psi + pi/2.0;
        w.push_back(DubinsWaypoint(x,y,pi/2.0*R,tx,ty,1));
    }

    // back straight segment
    x = x + tracklen*cos(psi);
    y = y + tracklen*sin(psi);
    w.push_back(DubinsWaypoint(x,y,tracklen,0,0,0));

    // half circle to complete
    double txu = x - R*sin(psi);
    double tyu = y + R*cos(psi);
    for(int j=0; j<2; j++)
    {
        double nx = -y + tyu + txu;
        y  =  x - txu + tyu;
        x  = nx;
        psi = psi + pi/2.0;
        w.push_back(DubinsWaypoint(x,y,pi/2.0*R,txu,tyu,1));
    }

    return w;
}

std::vector<DubinsWaypoint> RouteExtension::BuildSingleBubble(double th, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp)
{
    const double pi = n_Const::c_Convert::dPi();
    double psi = atan2(endwp.y - startwp.y, endwp.x - startwp.y);
    double x = startwp.x;
    double y = startwp.y;

    std::vector<DubinsWaypoint> w;

    // counterclockwise first
    double tx = x - R*sin(psi);
    double ty = y + R*cos(psi);
    double angle = psi - pi/2.0 + th;
    x = x - R*sin(psi) + R*cos(angle);
    y = y + R*cos(psi) + R*sin(angle);
    psi = psi + th;
    w.push_back(DubinsWaypoint(x,y,th*R,tx,ty,1));

    // half clockwise turn
    tx = x + R*sin(psi);
    ty = y - R*cos(psi);
    angle = psi + pi/2.0 - th;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - th;
    w.push_back(DubinsWaypoint(x,y,th*R,tx,ty,-1));

    // second half clockwise turn
    angle = psi + pi/2.0 - th;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - th;
    w.push_back(DubinsWaypoint(x,y,th*R,tx,ty,-1));

    // final counterclockwise turn
    tx = x - R*sin(psi);
    ty = y + R*cos(psi);
    angle = psi - pi/2.0 + th;
    x = x - R*sin(psi) + R*cos(angle);
    y = y + R*cos(psi) + R*sin(angle);
    psi = psi + th;
    w.push_back(DubinsWaypoint(x,y,th*R,tx,ty,1));

    return w;
}

std::vector<DubinsWaypoint> RouteExtension::BuildSlideBack(double th, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp)
{
    const double pi = n_Const::c_Convert::dPi();
    double psi = atan2(endwp.y - startwp.y, endwp.x - startwp.y);
    double x = startwp.x;
    double y = startwp.y;

    std::vector<DubinsWaypoint> w;

    // header
    // counterclockwise first
    double gam = pi/2.0;
    double tx = x - R*sin(psi);
    double ty = y + R*cos(psi);
    double angle = psi - pi/2.0 + gam;
    x = x - R*sin(psi) + R*cos(angle);
    y = y + R*cos(psi) + R*sin(angle);
    psi = psi + gam;
    w.push_back(DubinsWaypoint(x,y,gam*R,tx,ty,1));

    // half clockwise turn
    tx = x + R*sin(psi);
    ty = y - R*cos(psi);
    angle = psi + pi/2.0 - gam;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - gam;
    w.push_back(DubinsWaypoint(x,y,gam*R,tx,ty,-1));

    // second half clockwise turn
    angle = psi + pi/2.0 - gam;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - gam;
    w.push_back(DubinsWaypoint(x,y,gam*R,tx,ty,-1));

    // slide back init
    // still clockwise
    angle = psi + pi/2.0 - th;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - th;
    w.push_back(DubinsWaypoint(x,y,th*R,tx,ty,-1));

    // slide back main
    // counterclockwise
    double del = acos(1-sin(th));
    gam = pi/2.0 + del + th;
    tx = x - R*sin(psi);
    ty = y + R*cos(psi);
    angle = psi - pi/2.0 + gam;
    x = x - R*sin(psi) + R*cos(angle);
    y = y + R*cos(psi) + R*sin(angle);
    psi = psi + gam;
    w.push_back(DubinsWaypoint(x,y,gam*R,tx,ty,1));

    // final turn off
    // clockwise again
    gam = acos(1-sin(th));
    tx = x + R*sin(psi);
    ty = y - R*cos(psi);
    angle = psi + pi/2.0 - gam;
    x = x + R*sin(psi) + R*cos(angle);
    y = y - R*cos(psi) + R*sin(angle);
    psi = psi - gam;
    w.push_back(DubinsWaypoint(x,y,gam*R,tx,ty,-1));

    return w;
}

}
}
}
