// SV-COMP style: the property is "reach_error() is never called". CBMC checks every call.
extern void abort(void);
void reach_error(void) {}
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
extern unsigned int __VERIFIER_nondet_uint(void);
int main(void) {
  unsigned int a = __VERIFIER_nondet_uint();
  unsigned int b = a + 1;          /* wraps around at UINT_MAX */
  if (a > 10) __VERIFIER_assert(b > a);
  return 0;
}
