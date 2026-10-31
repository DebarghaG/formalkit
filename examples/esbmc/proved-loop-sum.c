#include <assert.h>
int nondet_int(void);

int main(void) {
  int n = nondet_int();
  __ESBMC_assume(0 <= n && n <= 10);
  int s = 0;
  for (int i = 0; i < n; i++) s += 2;
  assert(s == 2 * n);
  return 0;
}
