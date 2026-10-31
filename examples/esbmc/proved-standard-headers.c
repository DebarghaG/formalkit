#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(void) {
  char *s = malloc(4);
  if (s) {
    strcpy(s, "ab");
    printf("%s\n", s);
    free(s);
  }
  return 0;
}
