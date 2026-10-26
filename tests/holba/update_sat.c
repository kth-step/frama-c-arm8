#include <stdint.h>
#include <limits.h>

/*@ requires INT_MIN < min < max && min <= timer <= max < INT_MAX;
    assigns \nothing;
    ensures
      ((cond == 0 && timer - 1 < min) ==> \result == min) &&
      ((cond == 0 && min <= timer - 1) ==> \result == timer - 1) &&
      ((cond != 0 && max < timer + 1) ==> \result == max) &&
      ((cond != 0 && timer + 1 <= max) ==> \result == timer + 1); */
int64_t update_sat(int64_t cond, int64_t timer, int64_t min, int64_t max) {
  int64_t res = timer;
  if (cond) {res += 1;} else {res -= 1;}
  if (res > max) res = max;
  if (res < min) res = min;
  return res;
}
