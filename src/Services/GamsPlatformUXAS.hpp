// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   GamsPlatformUXAS.hpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on July 11, 2017, 10:10 AM
 *
 */

#ifndef __DMPL_PLATFORM_GAMS_HPP__
#define __DMPL_PLATFORM_GAMS_HPP__

namespace dmpl
{

  /********************************************************************/
  //-- GAMS variables
  /********************************************************************/
  //gams::platforms::BasePlatform *platform = NULL;
  int grid_x = 0, grid_y = 0, grid_z = 0;
  double grid_leftX = NAN, grid_rightX = NAN;
  double grid_topY = NAN, grid_bottomY = NAN;
  double grid_topZ = NAN, grid_bottomZ = NAN;
  double grid_cellX = NAN, grid_cellY = NAN, grid_cellZ = NAN;

  /********************************************************************/
  //-- GAMS functions
  /********************************************************************/

  /**
   * Call before simulation start, and before calling GRID_PLACE, to initialize
   * needed globals.
   **/
  void GRID_INIT()
  {
    grid_x = X;
    grid_y = Y;
    grid_z = Z;
    grid_leftX = LeftX;
    grid_rightX = RightX;
    grid_topY = TopY;
    grid_bottomY = BottomY;
    grid_topZ = TopZ;
    grid_bottomZ = BottomZ;
    grid_cellX = (grid_rightX - grid_leftX) / (grid_x-1);
    grid_cellY = (grid_bottomY - grid_topY) / (grid_y-1);
    grid_cellZ = (grid_bottomZ - grid_topZ) / (grid_z-1);
  }

  /**
   * Call before simulation start to initialize where the platform should spawn
   *
   * @param x the x coordinate (left/right from default V-REP perspective)
   * @param y the y coordinate (up/down from default V-REP perspective)
   * @param z the altitude
   **/
  void GRID_PLACE(double x, double y, double z)
  {
    //std::cerr << "GRID_PLACE" << x << " " << y << " "  << y << std::endl;
    knowledge.set(".initial_x", grid_leftX + x * grid_cellX);
    knowledge.set(".initial_y", grid_topY + y * grid_cellY);
    knowledge.set(".initial_alt", grid_topZ + z * grid_cellZ);
  }

  /**
   * Call before simulation start to initialize where the platform should spawn
   *
   * @param x the x coordinate (left/right from default V-REP perspective)
   * @param y the y coordinate (up/down from default V-REP perspective)
   * @param z the altitude
   **/
  void GAMS_PLACE(double x, double y, double z)
  {
    //std::cerr << "GRID_PLACE" << x << " " << y << " "  << y << std::endl;
    knowledge.set(".initial_x", x);
    knowledge.set(".initial_y", y);
    knowledge.set(".initial_alt", z);
  }

  /**
   * Command platform to move to grid location X, Y, Z
   * 
   * @param x the x coordinate (left/right from default V-REP perspective)
   * @param y the y coordinate (up/down from default V-REP perspective)
   * @param z the altitude
   * @param epsilon distance in meters to consider "good enough" for ending movement
   *
   * @return true if the platform is still moving, false otherwise
   **/
  int GRID_MOVE(double x, double y, double z, double epsilon = 0.1)
  {
    //std::cerr << "GRID_MOVE" << x << " " << y << " " << z << std::endl;
    //int ret = platform->move(gams::utility::Position(grid_leftX + x * grid_cellX, grid_topY + y * grid_cellY, grid_topZ + z * grid_cellZ), epsilon);
    //return ret != 2;
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Command platform to move to continuous location X, Y, Z
   * 
   * @param x the x coordinate (left/right from default V-REP perspective)
   * @param y the y coordinate (up/down from default V-REP perspective)
   * @param z the altitude
   * @param epsilon distance in meters to consider "good enough" for ending movement
   *
   * @return true if the platform is still moving, false otherwise
   **/
  int GAMS_MOVE(double x, double y, double z, double epsilon = 0.1)
  {
    //int ret = platform->move(gams::utility::Position(x, y, z), epsilon);
    //return ret != 2;
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /** stop any ongoing movement */
  void STOP_MOVE()
  {
    //platform->stop_move();
  }
  
  //-- the following four variables and two functions provide an
  //-- alternate API for moving a node. you first call GRID_SETPOINT()
  //-- and then repeatedly call GRID_ARRIVED(). they are built on top of
  //-- GRID_MOVE(). the four variables are used to record the arguments
  //-- to be passed to GRID_MOVE().
  double GRID_MOVE_x = 0;
  double GRID_MOVE_y = 0;
  double GRID_MOVE_z = 0;
  double GRID_MOVE_epsilon = 0;

  void GRID_SETPOINT(double x, double y, double z, double epsilon = 0.1)
  {
    GRID_MOVE_x = x;
    GRID_MOVE_y = y;
    GRID_MOVE_z = z;
    GRID_MOVE_epsilon = epsilon;
    GRID_MOVE(GRID_MOVE_x,GRID_MOVE_y,GRID_MOVE_z,GRID_MOVE_epsilon);
  }

  int GRID_ARRIVED()
  {
    return !GRID_MOVE(GRID_MOVE_x,GRID_MOVE_y,GRID_MOVE_z,GRID_MOVE_epsilon);
  }

#if 0
  double GET_X()
  {
    return 0;
  }

  double GET_Y()
  {
    return 0;
  }

  double GET_Z()
  {
    return 0;
  }
#endif

  /// Returns the size of a grid cell in the X-dimension
  double GET_CELL_SIZE_X()
  {
    return grid_cellX;
  }

  /// Returns the size of a grid cell in the Y-dimension
  double GET_CELL_SIZE_Y()
  {
    return grid_cellY;
  }

  /// Returns the size of a grid cell in the Z-dimension
  double GET_CELL_SIZE_Z()
  {
    return grid_cellZ;
  }

  /// Returns latitude
  double GET_LAT()
  {
    //if(platform == NULL) return NAN;
    //return platform->get_location().lat();
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /// Returns longitude
  double GET_LNG()
  {
    //if(platform == NULL) return NAN;
    //return platform->get_location().lng();
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /// Returns vrep X coordinate
  double GET_X()
  {
    /*
    using gams::platforms::VREPBase;
    VREPBase *vplat = dynamic_cast<VREPBase*>(platform);

    if(vplat == NULL) return NAN;
    return vplat->get_location().transform_to(vplat->get_vrep_frame()).x();
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /// Returns vrep Y coordinate
  double GET_Y()
  {
    /*
    using gams::platforms::VREPBase;
    VREPBase *vplat = dynamic_cast<VREPBase*>(platform);

    if(vplat == NULL) return NAN;
    return vplat->get_location().transform_to(vplat->get_vrep_frame()).y();
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /// Returns altitude
  double GET_ALT()
  {
    //if(platform == NULL) return NAN;
    //return platform->get_location().alt();
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Rotate platform around Z axis, 
   * @param angle in degrees, where positive is counter-clockwise as viewed from
   *         above, and zero is along X-axis in positive direction
   * @param epsilon angle in degrees to accept as "close enough" to finish rotating
   * 
   * @return true if platform is still rotating, false if not.
   **/
  int ROTATE(double angle, double epsilon = 5)
  {
    /*
    //std::cout << "Rotate: " << angle << std::endl;
    int ret = platform->orient(gams::utility::Orientation(platform->get_frame(),
                                                          0, 0, angle, gams::utility::degrees));
    //std::cout << "Rotate ret: " << ret << std::endl;
    return ret != 2;
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

#ifdef CDRA
  /**
   * stop ongoing rotations, if any
   **/
  void STOP_ROTATION()
  {
    //platform->stop_rotation();
    throw std::runtime_error("Platform function unimplemented!!");
  }
#endif

  //using gams::platforms::HasRangeSensor;
  //using gams::platforms::HasAltitudeSensor;
  //using gams::platforms::HasColorSensor;
  //using gams::platforms::HasColor;

  /**
   * Detect whether the platform as a range finder sensor, such as a laser
   * range finder.
   *
   * @return true, if the platform has a range finder sensor, and thus GET_RANGE
   *         will work. Otherwise, return false.
   **/
  int HAS_RANGE()
  {
    //HasRangeSensor *s = dynamic_cast<HasRangeSensor *>(platform);
    //return !!s;
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Gets the distance read by the range finder sensor, if there is one.
   *
   * @return if there is no sensor, returns NAN. Else, if something is detected,
   *         returns the distance to it in meters. Else, returns the maximum
   *         possible detection distance (for this particular sensor) in meters,
   *         as a negative value.
   **/
  double GET_RANGE()
  {
    /*
    HasRangeSensor *s = dynamic_cast<HasRangeSensor *>(platform);
    //std::cout << "HasRangeSensor: " << reinterpret_cast<long>(s) << std::endl;
    if(s)
      {
        double ret = s->get_range();
        //std::cout << "RangeSensor: " << ret << std::endl;
        return ret;
      }
    else
      return NAN;
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Gets the angle the range finder sensor is at relative to front of the
   * platform.
   *
   * @return angle in degrees, where positive is counter-clockwise as viewed from
   *         above. Returns NAN if platform has no such sensor.
   **/
  double GET_RANGE_ANGLE()
  {
    return HAS_RANGE() ? 0 : NAN;
  }

  /**
   * Gets the altitude read by the altitude sensor, if there is one.
   *
   * @return if there is no sensor, returns NAN. Else, if something is detected,
   *         returns the distance to it in meters. Else, returns the maximum
   *         possible detection distance (for this particular sensor) in meters,
   *         as a negative value.
   **/
  double GET_SENSED_ALT()
  {
    /*
    HasAltitudeSensor *s = dynamic_cast<HasAltitudeSensor *>(platform);
    //std::cout << "HasRangeSensor: " << reinterpret_cast<long>(s) << std::endl;
    if(s)
      {
        double ret = s->get_altitude();
        //std::cout << "RangeSensor: " << ret << std::endl;
        return ret;
      }
    else
      return NAN;
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Gets the color read by the color sensor, if there is one.
   *
   * @return if there is no sensor, returns -1. Else, if something is
   *         detected, returns its color as RGB.
   **/
  unsigned int GET_COLOR()
  {
    /*
    HasColorSensor *s = dynamic_cast<HasColorSensor *>(platform);
    //std::cout << "HasRangeSensor: " << reinterpret_cast<long>(s) << std::endl;
    if(s)
      {
        uint32_t ret = s->get_color();
        //std::cout << "RangeSensor: " << ret << std::endl;
        return ret;
      }
    else
      return -1;
    */
    throw std::runtime_error("Platform function unimplemented!!");
    return 0;
  }

  /**
   * Sets the color of the agent, if possible
   *
   **/
  void SET_COLOR(unsigned int color)
  {
    /*
    HasColor *s = dynamic_cast<HasColor *>(platform);
    //std::cout << "HasRangeSensor: " << reinterpret_cast<long>(s) << std::endl;
    if(s)
      {
        s->set_color(color);
        //std::cout << "RangeSensor: " << ret << std::endl;
      }
    */
    throw std::runtime_error("Platform function unimplemented!!");
  }

} // namespace dmpl
  
#endif //__DMPL_PLATFORM_GAMS_HPP__

/********************************************************************/
//-- end of file
/********************************************************************/
