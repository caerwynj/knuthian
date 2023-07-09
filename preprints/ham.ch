change file for better mini-indexes and line breaks
@x 2
@d deg u.I /* the current number of arcs to~and from this vertex */
@y
@-deg@>
@$deg {ham}2 =\|u.\|I@>
@d deg u.I /* the current number of arcs to~and from this vertex */
@%@$u {GB\_\,GRAPH}9 \&{util}@>@%
@z
@x 3
their |taken| field is nonzero. Initially we make all those fields zero.
@y
their |taken| field is nonzero.\kern-.7pt\null\
 Initially we make all those fields zero.
@z
@x 4
@d taken v.I /* does this vertex appear in the current path? */
@y
@-taken@>
@$taken {ham}4 =\|v.\|I@>
@d taken v.I /* does this vertex appear in the current path? */
@%@$v {GB\_\,GRAPH}9 \&{util}@>@%
@%@$v {ham}2 \&{register} \&{Vertex} ${}{*}{}$@>@%
@-vert@>
@z
@x 6
@*The algorithm. Unproductive branches of the search tree are cut off by
@y
@*The algorithm. \kern-1pt
Unproductive branches of the search tree are cut off by
@z
@x 6
@d vert w.V /* a vertex on the current path */
@d ark x.A /* the arc that leads to its current successor */
@y
@-k@>@-t@>
@-vert@>@-ark@>
@$vert {ham}6 =\|w.\|V@>
@$ark {ham}6 =\|x.\|A@>
@d vert w.V /* vertex on current path */
@d ark x.A /* arc to its current successor */
@%@$w {GB\_\,GRAPH}9 \&{util}@>@%
@%@$x {GB\_\,GRAPH}9 \&{util}@>@%
@z
