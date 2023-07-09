change file for interval.w, shows the intervals of the graph being considered
to use it, say
  ctangle interval interval-verbose interval-verbose
  make interval-verbose
@x
@<Make |G| a copy of |F|, retaining only leftward arcs@>;
@y
@<Make |G| a copy of |F|, retaining only leftward arcs@>;
printf("The input graph:");
for (v=G->vertices+1;v<G->vertices+G->n;v++) for (a=v->arcs;a;a=a->next)
  printf(" [%s..%s)",a->tip->name,v->name);
printf("\n");
@z
@x
    gb_new_arc(v->clone,u->clone,-1);
@y
    gb_new_arc(v->clone,u->clone,-1);
    printf("reducing [%s..%s)\n",u->name,v->name);
@z
