#include <stddef.h>
#include "stdlib.h"
#include "stack2.h"

struct cons {
  int value;
  struct cons *next;
};

struct stack {
  struct cons *top;
};

void *surely_malloc (size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

struct stack *newstack(void) {
  struct stack *p;
  p = (struct stack *) surely_malloc (sizeof (struct stack));
  p->top = NULL;
  return p;
}

void push (struct stack *p, int i) {
  struct cons *q;
  q = (struct cons *) surely_malloc (sizeof (struct cons));
  q->value = i;
  q->next = p->top;
  p->top = q;
}

int pop (struct stack *p) {
  struct cons *q;
  int i;
  q = p->top;
  p->top = q->next;
  i = q->value;
  free(q);
  return i;
}

