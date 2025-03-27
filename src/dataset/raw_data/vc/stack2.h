#include <stddef.h>
struct stack;
struct stack *newstack(void);
void push (struct stack *p, int i);
int pop (struct stack *p);
