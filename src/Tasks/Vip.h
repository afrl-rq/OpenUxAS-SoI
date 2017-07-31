#pragma once
#ifndef VIP_H
#define VIP_H

// NOTE: this uses C++11 features

#include <map>


class Vip {
  public:
    struct result {
      bool vTrack1;
      bool vTrack2;
      int vloc;
      int uloc1;
      int uloc2;
    };
    
    Vip();
    result &move(bool sp0, bool sp1, bool sp2, bool sp3, bool sp4,
                 int vlocs, int uloc1s, int uloc2s);
  private:
    int state;
};




#endif
