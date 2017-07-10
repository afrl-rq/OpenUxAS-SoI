#include <stdbool.h>
#include <stdio.h>

void component_entry(void) {

}

void component_init(void) {

}

void mission_read_vm(bool * unused) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}

void mission_read_wm(bool * unused) {
	printf("%i:%s:%s",__LINE__,__FILE__,__FUNCTION__);
}