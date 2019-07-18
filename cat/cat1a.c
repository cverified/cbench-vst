#include <stdio.h>

int
main()
{
  int c;
  while ((c = getchar()) != EOF)
    if (putchar(c) == EOF) return 1;
  return 0;
}
