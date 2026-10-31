// Unbounded proof: Automizer finds the loop invariant itself.
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 1000000) return 0;
  int i = 0, s = 0;
  while (i < n) {
    i++;
    s += 2;
  }
  __VERIFIER_assert(s == 2 * n);
  return 0;
}
