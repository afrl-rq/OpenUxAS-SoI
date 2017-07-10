#include <stdbool.h>
#include <stdio.h>
void component_entry(void) {

}

void component_init(void) {

}

void mission_write(bool * unused) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}

void waypoint_write(bool * unused) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}