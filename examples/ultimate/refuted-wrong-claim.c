extern int __VERIFIER_nondet_int(void);

int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x < 0 || x > 100) return 0;
  int y = x * 2;
  __VERIFIER_assert(y != 50);
  return 0;
}
