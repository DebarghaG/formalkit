#include <assert.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  assert(x != 7);  /* plain C assert counts as the property, too */
  return 0;
}
