#include <stdio.h>
#include <inttypes.h>

struct triple_double_struct {
  double one;
  double two;
  double three;
};

typedef struct triple_double_struct triple_double_t;

int main(void) {


  triple_double_t scalar = {3.14,6.28,9.42};
  triple_double_t array[999];
  uint16_t i = 0;
  array[i] = scalar;

  printf("Byte swap field in scalar struct.\n");
  printf("original: %lf\n",scalar.two);
  printf("swap: %lf\n",__builtin_bswap64(scalar.two));
  printf("swap swap: %lf\n",__builtin_bswap64(__builtin_bswap64(scalar.two)));

  printf("\nByte swap field in array of structs.\n");
  printf("original: %lf\n",array[i].two);
  printf("swap: %lf\n",__builtin_bswap64(array[i].two));
  printf("swap swap: %lf\n",__builtin_bswap64(__builtin_bswap64(array[i].two)));

  printf("\nByte swap field in array of structs destructively.\n");
  printf("original: %lf\n",array[i].two);
  array[i].two = __builtin_bswap64(array[i].two);
  printf("swap: %lf\n",array[i].two);
  array[i].two = __builtin_bswap64(array[i].two);
  printf("swap: %lf\n",array[i].two);

  return 0;

}
