#include <assert.h>
int nondet_int(void);

int main(void) {
  int a[10];
  int n = nondet_int();
  __ESBMC_assume(0 <= n && n <= 10);
  for (int i = 0; i <= n; i++) a[i] = i;  /* bug: writes a[10] when n == 10 */
  return 0;
}
