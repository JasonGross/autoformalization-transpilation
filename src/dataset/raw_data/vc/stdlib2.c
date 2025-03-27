#include <stddef.h>
#include "stdlib.h"

struct cell {struct cell *a, *b, *c, *d;};

#define N 80000

struct cell pool[N];
int pool_index = 0;
struct cell *freelist=NULL;

void *malloc (size_t n) {
  struct cell *p;
  if (n>sizeof(struct cell)) return NULL;
  if (freelist) {
    p = freelist;
    freelist = p->a;
  } else if (pool_index < N) {
    p = pool+pool_index++;
  } else p=NULL;
  return (void*)p;
}

void free (void *p) {
  struct cell *pp = p;
  if (pp==NULL) return;
  pp->a = freelist;
  freelist=pp;
}

void exit (int n) {
  while (1) ;
}
