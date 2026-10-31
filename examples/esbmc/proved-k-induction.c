// esbmc: --k-induction
// An unbounded proof: k-induction shows the assertion holds in every iteration of a non-terminating loop.
#include <assert.h>
unsigned int nondet_uint(void);

int main(void) {
  unsigned int x = 0;
  while (nondet_uint()) {
    if (x < 100) x++;
    else x = 0;
    assert(x <= 100);
  }
  return 0;
}
