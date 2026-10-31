// cbmc: --unwind 5
#include <assert.h>

int main(void) {
  int s = 0;
  for (int i = 0; i < 100; i++) s += i;
  assert(s == 4950);
  return 0;
}
