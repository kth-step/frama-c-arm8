/* run.config */
#include <stdint.h>
/*@ 
  requires \true;
  ensures (\result == \old(x) || \result == \old(y))
    && \old(x) <= \result
    && \old(y) <= \result;
*/
int64_t max(int64_t x, int64_t y) {
  if (x > y) {
    return x;
  } else {
    return y;
  }
}
