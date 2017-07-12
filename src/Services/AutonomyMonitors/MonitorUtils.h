/*--
  MonitorUtils: A bunch of simple utilities that support the
  monitor tasks including extraction of various fields from the
  messages.
  */

#ifndef D__MONITOR__UTILS__H__
#define D__MONITOR__UTILS__H__

#include "afrl/cmasi/EntityState.h"
#include "afrl/cmasi/Location3D.h"
#include "afrl/cmasi/CameraState.h"
#include <memory>      //int64_t
#include <vector>
namespace uxas {
    namespace service {
      namespace monitoring {
          std::vector<afrl::cmasi::Location3D*> getCameraFootprintFromEntityState(std::shared_ptr<afrl::cmasi::EntityState> ptr );
      }
    }
}



#endif
