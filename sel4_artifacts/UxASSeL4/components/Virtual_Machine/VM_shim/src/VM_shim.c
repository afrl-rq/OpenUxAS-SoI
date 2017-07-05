#include <tb_soi_tk1_types.h>
#include <string.h>
#include <camkes.h>

bool tb_out_mission_enqueue_dan_is_confused
(const MissionSoftware__mission_impl * tb_out_mission) {
    bool tb_result = true ; 

    tb_result &= tb_out_mission_enqueue((MissionSoftware__mission_impl *)tb_out_mission);

    return tb_result;
}
