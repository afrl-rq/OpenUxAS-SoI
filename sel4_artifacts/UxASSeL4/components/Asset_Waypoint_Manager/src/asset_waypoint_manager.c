#include <tb_Asset_Waypoint_Manager.h>
void in_uart_packet(const SMACCM_DATA__UART_Packet_i * packet) {
	printf("waypoint_manager:out_uart_packet -- Received UART packet with address: %x\n",packet);
}

/* void alarm(const int64_t * periodic_100_m) {} */

void component_entry(const int64_t *n) { }

void component_init(const int64_t *n) { }
