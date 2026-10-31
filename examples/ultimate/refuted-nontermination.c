// ultimate: --property termination
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int x = __VERIFIER_nondet_int();
  int steps = 0;
  while (x > 0) {
    steps = steps + 1;  /* bug: forgot to decrement x */
    if (steps > 100) steps = 0;
  }
  return 0;
}
