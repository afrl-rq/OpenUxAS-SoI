#include <tb_Waypoint_Manager.h>

/* void alarm(const int64_t * periodic_100_m) {} */

void component_entry(const int64_t *n) {
    static int count = 0;
    if(tb_Waypoint_Manager_read_mission_write()){
        printf("Waypoint Received\n");
    }else if(count == 20){
        printf("I assure you that I'm running\n");
        count = 0;
    }else{
        count++;
    }

}

void component_init(const int64_t *n) { }
