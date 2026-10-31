// The loop invariant forgets to relate s to i, so the postcondition is unprovable.
/*@ requires 0 <= n <= 1000;
    ensures \result == 2 * n; */
int twice(int n) {
  int s = 0;
  /*@ loop invariant 0 <= i <= n;
      loop assigns i, s;
      loop variant n - i; */
  for (int i = 0; i < n; i++) s += 2;
  return s;
}
