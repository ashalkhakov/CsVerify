/* Feeds the parser the tokens of a file: one per line, its code and its value; the total is the extra argument. */
#include <stdio.h>
#include <stdlib.h>
void *ParseAlloc(void *(*)(size_t));
void Parse(void *, int, int, int *);
void ParseFree(void *, void (*)(void *));
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  int code, value, total = 0;
  void *p = ParseAlloc(malloc);
  while (fscanf(f, "%d %d", &code, &value) == 2) Parse(p, code, value, &total);
  Parse(p, 0, 0, &total);
  ParseFree(p, free);
  return 0;
}
