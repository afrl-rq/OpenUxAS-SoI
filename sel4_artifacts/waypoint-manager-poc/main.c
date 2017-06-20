#include "wpm.h"
#include <string.h>

mc_t mc, submc;

int main(void) {

  FILE * f;
  wp_t wp;
  
  memset(&mc,0,sizeof(mc_t));
  memset(&submc,0,sizeof(mc_t));
  
  f = fopen("missioncommand","r");
  if(true == deserialize_mc(f,&mc)) {
    output_mc(stderr,&mc);
    if(true == sub_mc(&mc, mc.full.startingwaypoint, 5, &submc)) {
      output_mc(stderr,&submc);
    }
  }

  
  
  return 0;

}
