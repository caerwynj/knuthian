% example for mini-index paper
% based on hastily written earlier version in ~/archive directory

@i gb_types.w

@*Hamiltonian circuits. This program finds all Hamiltonian circuits of
an undirected graph, using conventions of the Stanford GraphBase.

If the user says, for example, `\.{ham} \.{foo.gb}', the standard
output will list every Hamiltonian circuit of the graph \.{foo}, which
should be represented in file \.{foo.gb} using the Stanford GraphBase's
portable ASCII format. The total number of solutions is reported at the
end of the output.

An optional second parameter specifies an interval between outputs, so
that the list contains only a sample of the solutions. For example,
`\.{ham} \.{foo.gb} \.{1000}' will list only one of every 1000
Hamiltonian circuits. If the second parameter is zero, only the
total number of circuits will be output.

@c
#include <stdio.h> /* standard \CEE/ input/output functions */
#include "gb_graph.h" /* the GraphBase data structures */
#include "gb_save.h" /* the |restore_graph| routine */

@ We use a utility field |deg| to record vertex degrees.

@d deg u.I /* the current number of arcs to~and from this vertex */

@c @t\4@>int main(int argc, char *argv[])
{
  Graph *g; /* the user's graph */
  register Vertex *t,*u,*v; /* key vertices */
  Vertex *x,*y,*z; /* vertices used less often */
  register Arc *a,*aa; /* arcs used often */
  Arc *b,*bb; /* arcs used less often */
  int count=0; /* solutioons found so far */
  int interval=1; /* the reporting interval */
  @<Scan the command line arguments and input |g|@>;
  @<Prepare |g| for backtracking, and find a vertex |x| of minimum degree@>;
  @<Abort the run if |g| is malformed or |x->deg<2|@>;
  for (b=x->arcs;b->next;b=b->next) for (bb=b->next;bb;bb=bb->next) {
    v=b->tip;
    z=bb->tip;
    @<Find all simple paths of length |g->n-2| from |v| to |z|, avoiding |x|@>;
  }
  printf("Altogether %d solutions.\n",count);
  return 0; /* normal exit */
}

@ @<Scan...@>=
if (argc>2 && sscanf(argv[2],"%d",&interval)==1) {
  argc--;
  if (interval<0) interval=-interval;
  else if (interval==0) interval=-10000;
    /* suppress output when 0 is specified */
}
if (argc!=2) {
  printf("Usage: %s foo.gb [interval]\n", argv[0]);
  return -1;
}
g=restore_graph(argv[1]);

@ Vertices that have already appeared in the path are said to be ``taken,'' and
their |taken| field is nonzero. Initially we make all those fields zero.

@d taken v.I /* does this vertex appear in the current path? */
@d not_taken(vert) ((vert)->taken==0)

@<Prepare |g| for backtracking, and find a vertex |x| of minimum degree@>=
if (g) {@+int dmin=g->n;
  for (v=g->vertices;v<g->vertices+g->n;v++) {
    register int d=0; /* the degree of |v| */
    v->taken=0;
    for (a=v->arcs;a;a=a->next) d++;
    v->deg=d;
    if (d<dmin) dmin=d,x=v;
  }
}

@ A vertex with fewer than two neighbors cannot be part of
a Hamiltonian circuit, so we give such cases short shrift.

@<Abort...@>=
if (!g) {
  printf("Graph %s is malformed (error code %ld)!\n",argv[1],panic_code);
  return -2;
}
if (x->deg<2) {
  printf("No solutions (vertex %s has degree %ld).\n",x->name,x->deg);
  return -3;
}

@*The algorithm. Unproductive branches of the search tree are cut off by
using a simple rule: If one of the vertices we could move to next
is adjacent to only one other unused vertex, we must move to it now.

The moves will be recorded in the vertex array of~|g|. More precisely, the
|k|th vertex of the path will be |t->vert| when |t| is the |k|th vertex of
the graph. If the move was not forced, |t->ark| will point to the |Arc|
record representing the arc from |t->vert| to |(t+1)->vert|; otherwise
|t->ark| will be |NULL|.

@d vert w.V /* a vertex on the current path */
@d ark x.A /* the arc that leads to its current successor */

@ This program is a typical application of the backtrack method; in other
words, it essentially does a depth-first search in the tree of all solutions.
The author, being a member of the Old School, is most comfortable writing
such programs with labels and |goto| statements, rather than with |while|
loops. Perhaps some day he will learn his lesson; but backtrack programs
do need to be streamlined for speed.

A complication
arises because we may discover that a move is unproductive before we have
completely updated the data structures recording that move.

@<Find all simple paths of length |g->n-2|...@>=
{@+Vertex *tmax; /* the deepest level */
  t=g->vertices;@+tmax=t+g->n-1; /* |t| represents the current level */
  x->taken=1;@+t->vert=x;@+t->ark=NULL;
advance: @<Increase |t|, updating the data structures to show that
             vertex |v| is now taken, and set |y| to a forced move, if any;
             but |goto backtrack| if no further moves are possible@>;
  if (y) { /* move is forced */
    t->ark=NULL;@+ v=y;@+ goto advance;
  }
  a=v->arcs;
search: @<Look at arc |a| and its successors, advancing if~a valid move
      is found@>;
restore: aa=NULL;
restore_to_aa: @<Downdate the data structures to the state they were in when
      level |t| was entered, stopping at arc |aa|@>;
backtrack: @<Decrease |t|, if possible, and search for another possibility@>;
}

@ When a vertex becomes taken, we pretend that it has been removed
from the graph.

@<Increase |t|...@>=
t++;
t->vert=v;
v->taken=1;
if (v==z) {
  if (t==tmax) @<Record a solution@>;
  goto backtrack;
}
for (aa=v->arcs,y=NULL;aa;aa=aa->next) {@+register int d;
  u=aa->tip;
  d=u->deg-1;
  if (d==1 && not_taken(u)) { /* we must move next to |u| */
    if (y) goto restore_to_aa; /* two forced moves can't both be made */
    y=u;
  }
  u->deg=d; /* |u| can no longer move to |v| */
}

@ We didn't change the graph drastically at level |t|; all we did was
decrease the degrees of vertices reachable from |t->vert|.
Therefore we can easily undo previous changes when we are backing up.

@<Downdate...@>=
for (a=t->vert->arcs;a!=aa;a=a->next) a->tip->deg++;

@ @<Look...@>=
while (a) {
  v=a->tip;
  if (not_taken(v)) {
    t->ark=a;
    goto advance; /* move to |v| */
  }
  a=a->next;
}

@ @<Decrease...@>=
t->vert->taken=0;
t--;
if (t->ark) {
  a=t->ark->next;
  goto search;
}
if (t!=g->vertices) goto restore; /* the move was forced, so we bypass |search| */

@ We print a solution by simply listing the vertex names in the
current path.

@<Record a solution@>=
{
  count++;
  if (count%interval==0 && interval>0) {
    printf("%d: ",count);
    for (u=g->vertices;u<=tmax;u++) printf("%s ",u->vert->name);
    printf("\n");
  }
}

@*Index.
