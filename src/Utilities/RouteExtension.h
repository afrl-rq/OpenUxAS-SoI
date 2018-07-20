#ifndef RouteExtension_H
#define RouteExtension_H

#include <vector>
#include "afrl/cmasi/Waypoint.h"
#include "afrl/cmasi/MissionCommand.h"
#include "FlatEarth.h"

namespace uxas
{
namespace common
{
namespace utilities
{

class DubinsWaypoint
{
public:
    DubinsWaypoint() {}
    DubinsWaypoint(double ix, double iy, double ilen, double itx, double ity, int iturndir)
    {
        x = ix; y = iy; len = ilen; tx = itx; ty = ity; turndir = iturndir;
    }

    double x{0.0};
    double y{0.0};
    double len{0.0};
    double tx{0.0};
    double ty{0.0};
    int turndir{0};
};

/*! \class RouteExtension
 *  \brief This class provides static functions to reason about and manipulate waypoint lists
 *
 */

class RouteExtension
{
public:
    RouteExtension() {}

    /**\brief Extends a list of waypoints by a prescribed amount of time. Path extension
     *        is done by adding turns with a specified radius to a long segment. Gauranteed
     *        to stay within 2*R of the original path. If no segment of sufficient length
     *        exists to which the extension manuever can be added, an error is returned.
     *        If the extension can be inserted, it is directly inserted to the input list.
     *
     * @param wplist: list of waypoints to be extended; directly updated with manuever waypoints in the list
     * @param extendTime_ms: time to extend the path (in ms)
     * @param R: turn radius of manuever to insert
     * @param d: discretization distance of segments around turns
     * @return true if extension succeeds; false if extension fails.
     */
    static bool ExtendPath(std::vector<afrl::cmasi::Waypoint*>& wplist, int64_t extendTime_ms, double R, double d);
    static double RequiredSegmentLength(double extendlen, double R);
    static std::vector<afrl::cmasi::Waypoint*> DiscretizeExtension(std::vector<DubinsWaypoint>& dubins_extension, double d, FlatEarth& flatEarth, afrl::cmasi::Waypoint* baseWp);

private:
    /**\brief Extends a single segment by a prescribed amount of time using the technique in [].
     *        Assumes that the initial heading of the vehicle matches the segment direction from
     *        'startwp' to 'endwp'. Note, assumes that there is a straight line between 'startwp'
     *        and 'endwp' and only the (x,y) values are used. The returned list includes both
     *        endpoints inclusively.
     *
     * @param startwp: start of segment in which the extension manuever should be added
     * @param endwp: end of segment in which the extension manuever should be added
     * @param extendlen: length to extend path (in meters)
     * @param R: turn radius of manuever to insert (in meters)
     * @return vector of dubins waypoints that replace the segment with an extended manuever
     */
    static std::vector<DubinsWaypoint> ExtendSegment(DubinsWaypoint& startwp, DubinsWaypoint& endwp, double extendlen, double R);
    static std::vector<DubinsWaypoint> BuildRaceTrack(int32_t N, double tracklen, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp);
    static std::vector<DubinsWaypoint> BuildSingleBubble(double th, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp);
    static std::vector<DubinsWaypoint> BuildSlideBack(double th, double R, DubinsWaypoint& startwp, DubinsWaypoint& endwp);

    static double SingleArcLen(double th, double R);
    static double SingleStraightLen(double th, double R);
    static double SingleBubbleExtensionError(double th, double extendlen, double R);
    static double SingleBubbleBisectionSearch(double extendlen, double R);
    static double SlideArcLen(double th, double R);
    static double SlideStraightLen(double th, double R);
    static double SlideExtensionError(double th, double extendlen, double R);
    static double SlideBisectionSearch(double extendlen, double R);
};

}
}
}

#endif // RouteExtension_H
