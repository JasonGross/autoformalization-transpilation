#include <stddef.h>
#include "stdlib.h"
#include "stack2.h"
#include "triang2.h"

void push_increasing (struct stack *st, int n) {
  int i;
  i=0;
  while (i<n) {
     i++;
     push(st,i);
  }
}

int pop_and_add (struct stack *st, int n) {
  int i=0;
  int t, s=0;
  while (i<n) {
    t=pop(st);
    s += t;
    i++;
  }
  return s;
}

int triang(int n) {
  struct stack *st;
  int i,t,s;
  st = newstack();
  push_increasing(st, n);
  s = pop_and_add(st, n);
  return s;
}  
    
