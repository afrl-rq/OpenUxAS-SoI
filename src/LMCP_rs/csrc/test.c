#include <stdio.h>

#include "clmcp.h"

int main() {
  Wedge w = {
    .azimuth_centerline = 0.0f,
    .vertical_centerline = 0.0f,
    .azimuth_extent = 0.0f,
    .vertical_centerline = 0.0f
  };
  printf("Wedge centerline: %f\n", w.azimuth_centerline);
  int64_t ees[] = {0, 1, 2};
  KeyValuePair ps[] = { { .key = "Bar", .value = "Baz" } };
  WavelengthBand dwbs[] = { WavelengthBand_AllAny };
  SearchTask st = {
    .base = {
      .task_id = 0,
      .label = "Foo",
      .eligible_entities = ees,
      .eligible_entities_len = 3,
      .revisit_rate = 0.0f,
      .parameters = ps,
      .parameters_len = 1,
      .priority = 0,
      .required = false
    },
    .desired_wavelength_bands = dwbs,
    .desired_wavelength_bands_len = 1,
    .dwell_time = 1000,
    .ground_sample_distance = 20.0f
  };
  printf("Search task ID: %ld\n", st.base.task_id);
  printf("Search task param value: %s\n", st.base.parameters[0].value);
  return 0;
}
