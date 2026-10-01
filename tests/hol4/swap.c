#include <stdint.h>
/*@ 
    requires \valid(x) && \valid(y);
    ensures *x == \old(*y) && *y == \old(*x);
*/
void swap(uint64_t * x, uint64_t * y) {
  uint64_t a, b;
  a = *x;
  b = *y;
  if (a == b)
    return;
  *x = b;
  *y = a;
}