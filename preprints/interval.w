% This is the paper "Irredundant Intervals" by Don Knuth.
% To make hardcopy, run it through CWEAVE with the Stanford GraphBase installed
% (the command "make interval.dvi" should do that)
% To make a running program, "make interval", again with Stanford GraphBase

@i gb_types.w

\def\topofcontents{
 \null\vskip-35pt
 \line{\eightrm Journal of Experimental Algorithmics\hfill}
 \vfill
 \vfill
 \centerline{\bf Irredundant Intervals}
 \bigskip
 \centerline{Donald E. Knuth}
 \smallskip
 \centerline{Computer Science Department, Stanford University}
 \vskip 4\bigskipamount
 \centerline{\vtop{\hsize=.8\hsize
    \noindent{\bf Abstract.}\quad
    This expository note presents simplifications of a theorem
    due to Gy\H{o}ri and an algorithm due to Franzblau and Kleitman:
    Given a family $F$ of $m$ intervals on a linearly ordered set
    of $n$ elements, we can construct in $O(m+n)^2$ steps an
    irredundant subfamily having maximum cardinality, as well as
    a generating family having minimum cardinality. The algorithm
    is of special interest because it solves a problem analogous
    to finding a maximum independent set, but on a class of objects
    that is more general than a matroid.
    This note is also a complete, runnable computer program,
    which can be used for experiments in conjunction with the
    public-domain software of {\sl The Stanford GraphBase}.}}
 \vskip.7in
 \vfill} % this material will start the table of contents page

% the next lines patch cwebmac so that the contents page comes out first
\let\oldcon=\con
\let\con=\bye

\newread\tocfile \openin\tocfile=\contentsfile\relax
\ifeof\tocfile
 \message{Please run this file again thru TeX to get the table of contents!}
\else \pageno=0 \titletrue {\let\end=\relax \oldcon} \fi

\def\lheader{\mainfont\the\pageno\eightrm\qquad\grouptitle\hfill
  Journal of Experimental Algorithmics\hfill
  DONALD E. KNUTH\qquad
  \mainfont\topsecno} % top line on left-hand pages
\def\rheader{\mainfont\topsecno\eightrm\qquad IRREDUNDANT INTERVALS\hfill
  Journal of Experimental Algorithmics\hfill\grouptitle
  \qquad\mainfont\the\pageno} % top line on right-hand pages

\font\slttten=cmsltt10

% references

\def\CR{1} % Culberson and Reckhow in JoA
\def\FJ{2} % Frank and Jord\'an in JCTB 95
\def\FK{3} % Franzblau and Kleitman in Inf+Control
\def\Gy{4} % Gy\"ori in JCTB 84
\def\KB{5} % Knuth-Bendix algorithm
\def\vone{6} % Knuth, Fundamental Algorithms
\def\vthree{7} % Knuth, Sorting and Searching
\def\sgb{8} % Knuth, GraphBase book
\def\cweb{9} % Knuth and Levy, CWEB book
\def\Lu{10} % Lubiw in JCTB 91

% notations

\def\[#1,#2){[#1\,\mathpunct{\ldotp\ldotp}#2)} % half-open interval
  % the two-dots notation is due to Hoare and Ramshaw, cf Concrete Mathematics
\def\:{{\vert\mskip1mu}} % the restriction operator
\def\]{{\downarrow}\mskip1mu} % the reduction operator
\let\seq=\subseteq % why do Hungarian mathematicians use \subset for this?
\let\union=\bigcup
\def\(#1){^{\mskip1mu(#1)}}

\let\int=\[ % I have to use \int for index items, since cwebmac redefines \[
\def\proclaim #1. #2\par{{\bf #1.}\enspace{\sl#2}\par}
\def\Proof{\smallskip\noindent Proof:\enspace}
\def\callthis#1{\edef#1{\number\secno}}

% illustrations

\newdimen\unit \unit=1.5em
\def\intpic #1[#2..#3)#4\\{\hbox{\kern#2\unit\llap{$#1$\ \ }%
 \hbox to0pt{\hss$\bullet$\hss}%
 \dimen0=#3\unit \advance\dimen0-#2\unit
 \hbox to\dimen0{\cleaders\hbox{$\mkern-2mu\smash-\mkern-2mu$}\hfil
   $\mkern-7mu \smash- \mkern1.5mu$}%
 \hbox to0pt{\hss$\circ$\hss} \ $#4$}}

@*Introduction. Let's say that a family of sets is {\it irredundant\/} if
@^irredundant sets, definition@>
its members can be arranged in a sequence with the following property:
Each set contains a point that isn't in any of the preceding sets.

If $F$ is a family of sets, we write $F^\cup$ for the family of all nonempty
@^notation: $F^\cup$@>
unions of elements of $F$. When $F$ and $G$ are families with
$F\subseteq G^\cup$, we say that $G$ {\it generates\/} $F$. If $F$ is
@^generating family, definition@>
irredundant and $G$ generates $F$, we obviously have $\vert F\vert\le
\vert G\vert$, because each set in the sequence requires a new generator.

In the special case that the members of $F$ are intervals of the real line,
Andr\'as Frank
@^Frank, Andr\'as@>
conjectured that the largest irredundant subfamily of $F$ has the same
cardinality as $F$'s smallest generating family. This conjecture was
proved by Ervin Gy\H{o}ri~[\Gy], who noted that such a result was a minimax
@^Gy\H{o}ri, Ervin@>
theorem of a new type, apparently unrelated to any of the other well-known
minimax theorems of graph theory and combinatorics. A constructive proof
was found shortly afterwards by Franzblau and Kleitman~[\FK], who
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>
sketched an algorithm to find a generating family and irredundant subfamily of
equal cardinality.
(Gy\H{o}ri, Franzblau, and Kleitman were led to these results while studying
the more general problem of finding a minimum number of subrectangles that
cover a given polygon. Further information about polygon covers appears
in [\FK] and~[\CR].)

The purpose of this note is to describe the beautiful algorithm of
Franzblau and Kleitman in full detail.
Indeed, the \.{CWEB} source file that generated this document is a computer
program that can be used in connection with the Stanford GraphBase~[\sgb] to
find maximum irredundant subfamilies and minimum generating families of any
given collection of intervals. Perhaps this new exposition will
shed new light on the class of optimization problems
for which an efficient algorithm exists.
@^Stanford GraphBase@>

According to the conventions of \.{CWEB}~[\cweb], the sections of this
document are
sequentially numbered 1, 2, 3, etc. In this respect we are returning to a
style of exposition used by Euler and Gauss and their contemporaries.
A~\.{CWEB} program is also essentially a hypertext; therefore this document
may also be regarded as experimental in another sense, as an attempt
to find new forms of exposition appropriate to modern technology.

Note: Gy\H{o}ri used the term ``U-increasing'' for an irredundant
family; Franzblau and Kleitman called such intervals ``independent.''
Since a family of sets is a hypergraph, it seems unwise to deviate
from the standard meaning of independent edges, yet ``U-increasing'' is
not an especially appealing alternative. We will see momentarily that
the term ``irredundant'' is quite natural in theory and practice.

@ A far-reaching generalization of Gy\H{o}ri's theorem was proved recently by
Frank and Jord\'an~[\FJ], who introduced a large new family of minimax
@^Frank, Andr\'as@>
@^Jord\'an, Tibor@>
theorems related to linking systems. In particular, Frank and Jord\'an
extended Gy\H{o}ri's results to intervals on a circle instead of a line.
But no combinatorial algorithm is known as yet for the circular case.

\callthis\intro
Can any or all of the Franzblau/Kleitman methods be ``lifted'' to such more
general problems? We will return to this tantalizing question after becoming
familiar with Franzblau and Kleitman's remarkable algorithm.

@* Theory. It is wise to study the theory underlying the
Franzblau/Kleitman algorithm before getting into the program itself.

@ A family of sets is called {\it redundant\/} if it is not irredundant.
@^redundant sets, definition@>
Any family that contains a redundant subfamily is redundant, since any
family contained in an irredundant family is irredundant.

@ If $F$ is a family of sets and $s$ is an arbitrary set, let $F\:s$ denote the
sets of $F$ that are contained in~$s$. This operation is left-associative
by convention: $F\:s\:t=(F\:s)\:t=F\:(s\cap t)$.
@^notation: $F\:s$@>

We also write $\union F$ for $\union\{f\mid f\in F\}$; thus
$F\:\,{\union F}=F$.
@^notation: $\union F$@>

(An index to all the main notations and definitions that we will use
appears at the end of this note.)

@ \proclaim Lemma. A finite family $F$ is redundant if and only if there is
a nonempty set $s$ such that every point of~$s$ belongs to at least two members
of $F\:s$. {\rm(The set $s$ need not belong to~$F$.)}

\Proof If $F$ is irredundant there is no such $s$, because $F\:s$ is
irredundant and its last set in the assumed sequence contains a
point that isn't in any of the others. But if $F$ is redundant, it contains
a minimal redundant subfamily $F_0$; then we have
$$\textstyle f\seq \union\,(F_0\setminus\{f\})
                \qquad\hbox{for all $f\in F_0$}\,,$$
since $F_0\setminus\{f\}$ is irredundant. It follows that every point of
$s=\union F_0$ is contained in at least two members of $F_0$, hence in
at least two members of $F\:s$ (since $F_0\seq F\:s$).

@ \proclaim Corollary. A finite family $F$ of intervals on a line
is redundant if and
only if there is an interval $s$ such that every point of $s$ belongs to
at least two intervals of $F\:s$. {\rm(The set $s$ need not belong to~$F$.)}

\Proof Intervals are nonempty.
By the proof of the preceding lemma, it suffices to consider sets~$s$
that can be written $\union F_0$ for some minimal redundant subfamily~$F_0$.
In the special case of intervals, $\union F_0$ must be a single interval;
otherwise $F_0$ would not be minimal.

@ Henceforth we will restrict consideration to finite families $F$ of
intervals on a linearly ordered set.
It suffices, in fact, to deal with integer elements; we
will consider subintervals of the $n$-element set $\[0,n)$. (The
notation $\[a,b)$ stands here for the set of all integers $x$ such that
$a\le x<b$.)
@^notation: $\int a,b)$@>

If $F$ is a family of sets and $x$ is a point, we will write $N_x\,F$ for the
@^notation: $N\sb x\,F$@>
number of sets that contain $x$. The corollary just proved can therefore be
stated as follows: ``$F$ is irredundant if and only if
every interval $s\seq\union F$ contains a point $x$ with $N_x\,F\:s\le1$.''
This characterization provides a polynomial-time test for irredundancy.

@ \callthis\bst
Irredundant intervals have an interesting connection to the familiar
computer-science concept of {\it binary search trees\/} (see, for example,
@^binary search tree, definition@>
[\vthree, \S6.2.2]): A family of intervals is irredundant if and only if
we can associate its intervals with a binary tree whose
nodes are each labeled with an integer~$x$ and an interval containing~$x$.
All nodes in the left subtree of such a node correspond to intervals
that are strictly less than~$x$, in the sense that all elements of those
intervals are $<x$; all nodes in the right subtree correspond
to intervals that are strictly greater than~$x$. The root of the binary tree
corresponds to the interval that is last in the assumed irredundant
ordering. Its distinguished integer~$x$ is an element that appears in
no other interval.

Given such a tree, we obtain a suitable irredundant ordering by traversing it
recursively from the leaves to the root, in postorder [\vone, \S2.3.1].
Conversely, given an irredundant ordering, we can construct a binary tree
recursively, proceeding from the root to the leaves.

@ An example might be helpful at this point. Suppose $n=9$ and
$$f_1=\[0,8)\,,\quad f_2=\[0,7)\,,\quad f_3=\[1,6)\,,\quad
  f_4=\[1,5)\,,\quad f_5=\[3,9)\,,\quad f_6=\[2,9)\,.$$
Then $\{f_1,f_2,f_3,f_4,f_5\}$ and $\{f_1,f_3,f_5,f_6\}$ are irredundant.
(Indeed, a family of intervals is irredundant whenever its members have no
repeated left endpoints or no repeated right endpoints.) These subfamilies are
in fact {\it maximally\/} irredundant---they become redundant when any
other interval of the family is added. Therefore maximal irredundant
subfamilies need not have the same cardinality; irredundant subfamilies do not
form the independent sets of a matroid.

On the other hand, irredundant sets of intervals do have matroid-like
@^matroids@>
properties. For example, if $F$ is irredundant and $F\cup\{g\}$ is redundant,
there is an $f\ne g$ such that $F\cup \{g\}\setminus\{f\}$ is irredundant.
(The proof is by induction on $\vert F\vert$: There is
$x\in f\in F$ such that $F=F_l\cup\{f\}\cup F_r$, where $F_l$ and $F_r$
correspond to the left and right subtrees of the root in the binary tree
representation. If $x\in g$, the family $F_l\cup\{g\}\cup F_r$ is irredundant;
if $x<g$, there is $f'\in F_r$ with
$F_l\cup\{f\}\cup (F_r\cup\{g\}\setminus\{f'\})$
irredundant, by induction; if $x>g$ there is $f'\in F_l$ with
$(F_l\cup\{g\}\setminus\{f'\})\cup\{f\}\cup F_r$ irredundant.)
Such near-matroid behavior makes families of intervals especially instructive.

@ Let's say that an interval $s$ is {\it good\/} for $F$ if $N_x\,F\:s\le1$
@^good interval, definition@>
for some $x\in s$; otherwise $s$ is {\it bad}. Franzblau and Kleitman
@^bad interval, definition@>
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>
introduced a basic reduction procedure
for any family $F$ of intervals that possesses a bad interval~$s$. Their
procedure is analogous to modification along an augmenting path in other
combinatorial algorithms.

Let $\[a_1,b_1)$, \dots, $\[a_k,b_k)$ be the maximal intervals in~$F\:s$,
ordered so that $a_1<\cdots<a_k$ and $b_1<\cdots<b_k$. (Notice that
$s=\[a_1,b_k)$.) For example, we might have the following picture:
$$\vbox{
  \halign{\kern5\unit\hfil#\hfil\cr
  $s$\cr
  \noalign{\vskip-.4\baselineskip}
  \hbox to 20\unit{\downbracefill}\cr}
  \medskip
  \intpic a_1[5..9)b_1\\
  \intpic a_2[7..15)b_2\\
  \intpic a_3[9..19)b_3\\
  \intpic a_4[14..21)b_4\\
  \intpic a_k[17..25)b_k\\
  \intpic [5..8)\hbox to 12\unit{\hss
     (non-maximal intervals make $s$ bad)\ \ \ \ \hss}\\
  \vskip-\baselineskip \intpic [20..25)\\
  \hbox to 30\unit{\hfil}\vskip-\baselineskip % for centering
}$$
If $a_{j+1}<b_j$ for $1\le j<k$, the family $F$ {\it reduced in\/} $s$ is
defined to be
$$F\]s \;=\; F \,\setminus\, \{\[a_1,b_1),\ldots,\[a_k,b_k)\}
               \,\cup\,      \{\[a_2,b_1),\ldots,\[a_k,b_{k-1})\}\,.$$
@^notation: $F\]s$@>
In the simplest case we have $k=1$ and the
reduced family is simply $F\setminus\{\[a_1,b_1)\}$.

If $s$ is a {\it minimal\/} bad interval for $F$, we can prove that
$a_{j+1}<b_j$ for $1\le j<k$, hence $F\]s$ is well-defined. Indeed,
point~$a_{j+1}$ must be in some interval $\[c,d)$ other than
$\[a_{j+1},b_{j+1})$, since $s$ is bad. We can assume that $c<a_{j+1}$;
otherwise all intervals of $F\:s$ would be contained in $\[a_1,a_{j+1})$ or
$\[a_{j+1},a_k)$, and both of these subintervals would be bad, contradicting
the minimality of~$s$. But $c<a_{j+1}$ implies that $\[c,d)$ is contained in
some maximal $\[a_i,b_i)$ with $i\le j$. Hence $a_{j+1}<b_i\le b_j$.

The notation $F\]s$ is defined to be left-associative, like $F\:s$; that is,
$F\]s\]t=(F\]s)\]t$ and $F\]s\,\:t=(F\]s)\:t$.

@ \callthis\lemzero
\proclaim Lemma. If $s$ is a minimal bad interval for $F$, we have
$F\seq(F\]s)^\cup$.

\Proof We must show that $\[a_j,b_j)\in(F\]s)^\cup$ for $1\le j\le k$. Let
$G=F\]s\,\:\[a_j,b_j)$; we will prove that $\[a_j,b_j)=\union G$. If
$x\in\[a_j,b_j)$, the badness of~$s$ implies that $x\in t$ for some $t\in F\:s$
with $t\ne\[a_j,b_j)$; let $t$ be contained in the maximal interval
$\[a_i,b_i)$.
If $i=j$, we have $t\in G$;
if $i<j$, we have $x\in\[a_j,b_i)\seq\[a_j,b_{j-1})\in G$; and
if $i>j$, we have $x\in\[a_i,b_j)\seq\[a_{j+1},b_j)\in G$.

@ \callthis\lemone \proclaim Lemma.
Suppose $s$ is a minimal bad interval for $F$, while
$t$ is a good interval. Then $t$ is good also for $F\]s$.

\Proof Let $s=\[a,b)$, $t=\[c,d)$, $l=\min(a,c)$, $r=\max(b,d)$.
Suppose $N_x\,F\:\[l,d)\ge2$ and $N_x\,F\:\[c,r)\ge2$ for all
$x\in t$.  Then $l=a<c<d <b=r$, because $t$ is good for $F$. By the
minimality of $s$, there is some $x\in\[a,d)$ with $N_x\,F\:\[a,d)\cdot
x\le1$. Since $N_x\,F\:\[a,d)\ge2$ we have $x<c$. Furthermore,
$x$ is in some interval of $(F\:s)\setminus F\:\[a,d)$,
because $s$ is bad; so $x$ is in some maximal $\[a_j,b_j)$ with
$a\le a_j\le x<c<d<b_j\le b$. It follows that none of the intervals
$\[a_1,b_1)$, \dots, $\[a_k,b_k)$, $\[a_2,b_1)$, \dots, $\[a_k,b_{k-1})$
are contained in~$t$, hence $F\]s\,\:t=F\:t$.

On the other hand, suppose $N_x\,F\:\[l,d)\le1$ for some $x\in t$. We will show
that $N_x\,F\]s\,\:t\le1$. This assertion can fail only if $x$ lies in some
interval $\[a_{j+1},b_j)\seq t$ newly added to $F\]s$.
Then $x\in\[a_j,b_j)\seq\[l,d)$, and $x\in\[a_{j+1},b_{j+1})\notin\[l,d)$,
hence $b_j\le d<b_{j+1}$; it follows that $j$ is uniquely determined, and
the only interval containing $x$ in $F\]s\,\:t$ is $\[a_{j+1},b_j)$.
A similar argument applies if $N_x\,F\:\[c,r)\le1$.

@ \callthis\pretrick \proclaim Corollary.
If $s$ is a minimal bad interval for $F$, we have $N_x\,F\]s=N_x\,F-N_x\,s$.

\Proof The proof of the preceding lemma shows in particular that none of the
intervals $\[a_{j+1},b_j)$ are already present in~$F$ before the reduction.
And if $x\in s$, suppose $x$~lies in $\[a_i,b_i)$, $\[a_{i+1},b_{i+1})$, \dots,
$\[a_j,b_j)$; then it lies in $\[a_{i+1},b_i)$, \dots, $\[a_j,b_{j-1})$ after
reduction, a net change of~$-1$.

\goodbreak

@ The Franzblau/Kleitman algorithm has a very simple outline: We let
$G_0=F$ and repeatedly set $G_{k+1}=G_k\]s_k$, where $s_k$ is the leftmost
minimal bad interval for $G_k$, until we finally reach a family $G_r$ in which
no bad intervals remain. This must happen sooner or later, because $\vert
G_k\vert =\vert F\vert-k$. The final irredundant family $G=G_r$ generates~$F$,
because $F\seq G_k^\cup$ for all~$k$ by the lemma of \S\lemzero.
Franzblau and Kleitman proved the nontrivial
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>
fact that $\vert G\vert$ is the size of the maximum irredundant subfamily
of~$F$; hence $G$ is a minimum generating family. \callthis\outline

@ It is tempting to try to prove the optimality of $G$ by a simpler,
inductive approach in which we ``grow'' $F$ one interval at a time,
updating its maximum irredundant set and minimum generating set appropriately.
But experiments show that the maximum irredundant set can change drastically
when $F$ receives a single new interval, so this direct primal-dual approach
seems doomed to failure. The indirect approach is more difficult to prove,
but no more difficult to program. So we will proceed to develop further
properties of Franzblau and Kleitman's reduction procedure~[\FK]. The key fact
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>
is a remarkable theorem that we turn to~next.

@ \proclaim Theorem. The same final family $G=G_r$ is obtained when $s_k$ is
chosen to be an arbitrary (not necessarily leftmost) minimal bad interval
of~$G_k$ in the reduction algorithm. Moreover, the same multiset
$\{s_0,\ldots,s_{r-1}\}$ of minimal bad intervals arises, in some order,
regardless of the choices made at each step.

\Proof We use induction on $r$, the maximum number of steps to convergence
among all reduction procedures that begin with a family $F$.
If $r=0$, the result is trivial,
and if $F$ has only one minimal bad interval the result is immediate
by induction. Suppose therefore that $s$ and $t$ are distinct minimal
bad intervals of $F$. We will prove later that $t$ is a minimal bad interval
for $F\]s$, and that $F\]s\]t=F\]t\]s$. Let $r'$ be the maximum distance
to convergence from $F\]s$, and $r''$ the maximum from $F\]t$; then $r'$
and $r''$ are less than $r$, and induction proves that the final result
from $F\]s$ is the final result from $F\]s\]t=F\]t\]s$, which is the final
result from $F\]t$. (Readers familiar with other reduction algorithms, like
that of [\KB], will recognize this as a familiar ``diamond lemma'' argument.
@^diamond lemma@>
We construct a diamond-shaped diagram with four vertices: $F$, $F\]s$, $F\]t$,
and a common outcome of $F\]s$ and $F\]t$.)
% other examples: Church-Rosser, Gr\"obner, Bergman, etc
This completes the proof, except for two lemmas that will be demonstrated
below; their proofs have been deferred so that we could motivate them first.

@ This theorem and the lemma of \S\lemone\ have an important
corollary: {\sl Let $S=\{s_0,\ldots,s_{r-1}\}$ be the multiset of minimal
bad intervals determined by the algorithm from~$F$, and let $t$ be any
interval. Then $S\:t$ is the multiset of minimal bad intervals determined by
the algorithm from~$F\:t$.} This holds
because an interval $s\seq t$ is bad for $F$ if and only if it is bad for
$F\:t$. Minimal bad intervals within $t$ never appear again once they are
removed, and we can remove them first.

Reducing a minimal bad interval $s$ when $s$ is contained in a bad
interval~$t$ may make $t$ good, or leave it bad, or make it minimally bad.
If $s$ is minimally bad for~$F$, it might also be minimally bad for $F\]s$.

@ Now we are ready for the {\it coup de gr\^ace\/} and the {\it pi\`ece
de r\'esistance\/}:
@^metaphors, mixed@>
After the reduction algorithm has computed the irredundant generating
family~$G=G_r$ and the multiset $S$ of minimal bad intervals, we
can construct an irredundant subfamily $F'$ of $F$ with $\vert F'\vert=
\vert G\vert$ by constructing a binary search tree as described in \S\bst.
The procedure is recursive, starting with an initial interval $t=\[0,n)$
that contains~$F$: The tree defined for $F\:t$ is empty if
$F\:t$ is empty. Otherwise it has a root node labeled with $x$
and with any interval of $F\:t$ containing~$x$, where $x$ is an integer such
that $N_x\,G^{(t)}=1$;
here $G^{(t)}$ is the final generating set that is obtained
@^notation: $G^{(t)}$@>
when the reduction procedure is applied to $F\:t$. A suitable interval
containing~$x$ exists, because every element of $G^{(t)}$ is an intersection
of intervals in $F\:t$. The left subtree of the root node is
the binary search tree for $F\:\bigl(t\cap\[0,x)\bigr)$; the
right subtree is the binary search tree for $F\:\bigl(t\cap\[x+1,n)\bigr)$.

The number of nodes in this tree is $\vert G\vert$. For if $x$ is the integer
in the label of the root, $G$ has one interval containing $x$, and its
other intervals are $G\:\[0,x)$ and $G\:\[x+1,n)$. The family $G^{(t)}$ is not
the same as $G\:t$; but we do have $\vert G^{(t)}\vert=
\bigl\vert G\:t\bigr\vert$ when $t$ has the special form $\[0,x)$ or
$\[x+1,n)$, because in such cases
$F\]s\,\:t$ has the same cardinality as $F\:t$ when $s$ is a minimal bad
interval and $s\not\seq t$.
For example, if $t=\[0,x)$ and $b_j\le x<b_{j+1}$, we have $F\]s\,\:t=
F\:t\setminus\{\[a_1,b_1),\ldots,\[a_j,b_j)\}\cup\{\[a_2,b_1),\ldots,
\[a_{j+1},b_j)\}$.

@ It is not necessary to compute each $G^{(t)}$ from scratch by starting with
$F\:t$ and applying the reduction algorithm until it converges, because
the binary tree construction algorithm requires only a knowledge
of the incidence function $N_x\,G^{(t)}$. This function is easy to compute,
because $N_x\,F\]s=N_x\,F-N_x\,s$ by \S\pretrick; therefore
$$N_x\,G^{(t)}=N_x\,F\:t-N_x\,S\:t\,.$$ \callthis\trick

@ All the basic ideas of Franzblau and Kleitman's algorithm have now
been explained. But we must still carry out a careful analysis of some
fine points of reduction that were claimed in the proof of the main theorem.
If $s$ and $t$ are distinct minimal bad intervals, the lemma of \S\lemone\
implies that no bad subintervals of~$t$ appear in $F\]s$; we also need
to verify that $t$ itself remains bad.

\smallskip
\noindent\proclaim Lemma. If $s$ is a minimal bad interval for $F$ and
$t$ is a bad interval such that $s\not\seq t$, then $t$ is bad for $F\]s$.

\Proof Let $s=\[a,b)$ and $t=\[c,d)$. We can assume by left-right symmetry
that $a<c$. Then $b<d$, by minimality of~$s$.
Assume that $t$ isn't bad for $F\]s$. The subfamily $F\:t$ must contain
at least one of the maximal intervals $\[a_j,b_j)$ of $F\:s$ that are
deleted during the reduction; hence $c\le a_j<b_{j-1}\le b$.

Let $j$ be minimal with $a_j\ge c$. Then
$$F\]s\,\:t=F\:t\setminus \{\[a_j,b_j),\ldots,\[a_k,b_k)\}
                   \cup \{\[a_j,b_{j-1}),\ldots,\[a_k,b_{k-1})\}\,;$$
so the elements of $t$ that are covered once less often are the elements of
$\[b_{j-1},b_k)$. Suppose $y\in\[b_{i-1},b_i)$ for some $i\ge j$. Then
$y\in\[a_i,b_i)\seq s\cap t$, and $y$ is in some other interval $f\seq s$.
The maximal interval containing $f$ must be $\[a_l,b_l)$ for some $l\ge i$,
hence $f\seq s\cap t$. Thus $N_y\,F\:(s\cap t)\ge 2$ for all $y\in
\[b_{j-1},b_k)$. But $s\cap t$ is good, so there must be a point $x\in
\[c,b_{j-1})$ with $N_x\,F\:(s\cap t)\le1$. We also have $N_x\,F\:t\ge 2$,
since $t$ is bad, so there's an interval in $F\:t\setminus F\:(s\cap t)$
that contains~$x$. This interval contains
$\[x,b_k)$. Consequently $N_y\,F\:t\ge3$ for all $y\in\[b_{j-1},b_k)$.

@ \proclaim Lemma. If $s$ and $t$ are minimal bad intervals for $F$ and
$s\ne t$, we have $F\]s\]t=F\]t\]s$.

\Proof Let the maximal intervals in $F\:s$ and $F\:t$ be $\[a_1,b_1)$,
\dots, $\[a_k,b_k)$ and $\[c_1,d_1)$, \dots, $\[c_l,d_l)$, respectively,
where $a_1<c_1$. The lemma is obvious unless $F\:(s\cap t)$ is nonempty, so we
assume that $c_1<b_k<d_l$. Let $x\in s\cap t$ have $N_x\,F\:(s\cap t)=1$,
and let $f$ be the interval of $F\:(s\cap t)$ that contains~$x$. Let $p$
be maximal with $a_p<c_1$, and let $q$ be minimal with $d_q>b_k$. Since
$N_x\,F\:s>1$, there is an interval $\[a_j,b_j)$ containing~$x$
with $j\le p$; thus
$x\in\[a_p,b_p)$. Similarly $x\in\[c_q,d_q)$. Furthermore, if $p<k$ we
have $\[a_{p+1},b_{p+1})\seq s\cap t$; hence
either $\[a_{p+1},b_{p+1})=f$ or $a_{p+1}>x$. If $q>1$ we have either
$\[c_{q-1},d_{q-1})=f$ or $d_{q-1}\le x$.

If $p=k$ or
$f\ne\[a_{p+1},b_{p+1})$, any newly added intervals $\[a_{j+1},b_j)$ for
$p\le j<k$ in $F\]s$ are properly contained in $\[c_q,d_q)$, so they remain
in $F\]s\]t$. Thus we can easily describe the compound operation $F\]s\]t$ in
detail:
$$\displaylines{\hskip6em\hbox{Delete $\[a_1,b_1)$, \dots, $\[a_k,b_k)$;\quad
  insert $\[a_2,b_1)$, \dots, $\[a_k,b_{k-1})$;}\hfill\cr
  \hfill\hbox{delete $\[c_1,d_1)$, \dots, $\[c_l,d_l)$;\quad
  insert $\[c_2,d_1)$, \dots, $\[c_l,d_{l-1})$.}\hskip6em\cr}$$
No two of these intervals are identical, so $F\]t\]s$ gives the same result.
(If $f=\[c_{q-1},d_{q-1})$, the family $F\]t$ has $f$ replaced by
$\[c_q,d_{q-1})\seq f\seq\[a_i,b_i)$ for some $i\le p$,
so $\[c_q,d_{q-1})$ is not maximal in $F\]t\,\:s$.)

The remaining case $f=\[a_{p+1},b_{p+1})=\[c_{q-1},d_{q-1})$ needs to be
considered specially, since we can't delete this interval twice.
The following picture might help clarify the situation:
$$\vbox{
  \halign{\hfil#\hfil\cr
  $s$\cr
  \noalign{\vskip-.4\baselineskip}
  \hbox to 19\unit{\downbracefill}\cr}
  \medskip
  \intpic a_1[0..5)b_1\\
  \intpic a_2[2..12)b_2\\
  \intpic a_p[3..15)b_p\\
  \intpic (\;a_{p+1}[6..16)b_{p+1}\quad
          \hbox{same as $\[c_{q-1},d_{q-1})$ below$\;)$}\\
  \intpic a_k[11..19)b_k\\
  \smallskip
  \intpic c_1[4..7)d_1\\
  \intpic c_{q-1}[6..16)d_{q-1}\\
  \intpic c_q[8..23)d_q\\
  \intpic c_l[14..26)d_l\\
  \smallskip
  \halign{\kern4\unit\hfil#\hfil\cr
  \hbox to 22\unit{\upbracefill}\cr
  $t$\cr}
  \moveright 9\unit\hbox{\smash{\vbox to 12.5\baselineskip{
     \cleaders\hbox to0pt{\hss\vrule height.5ex
                              \vrule height 1ex depth .5ex width0pt\hss}\vfil
     \medskip\hbox to0pt{\hss$x$\hss}}}}
}$$

Suppose $g$ is an interval of $F\:t$ that is contained in $\[c_j,d_j)$ if and
only if $j=q-1$. Then $g$ contains a point $<c_q$. If $x\in g$ we have $g=f$,
since $g\seq s\cap t$. Otherwise $g\seq\[c_{q-1},x)\seq\[c_{q-1},b_p)=
\[a_{p+1},b_p)$. It follows that the maximal intervals of $F\]s\,\:t$ are
$$\[c_1,d_1),\;\ldots,\;\[c_{q-2},d_{q-2}),\;\[c_{q-1},b_p),\;
  \[c_q,d_q),\;\ldots,\;\[c_l,d_l).$$
These intervals are replaced in $F\]s\]t$ by
$$\[c_2,d_1),\;\ldots,\;\[c_{q-1},d_{q-2}),\;\[c_q,b_p),\;
  \[c_{q+1},d_q),\;\ldots,\;\[c_l,d_{l-1}).$$
Thus $F\]s\]t$ is formed almost as in the previous case, but with $\[a_{p+1},
b_p)$ and $\[c_q,d_{q-1})$ replaced by $\[c_q,b_p)$. And we get precisely
the same intervals in $F\]t\]s$.

(Is there a simpler proof?)

@* Practice. The computer program in the remainder of this note
operates on a family of intervals defined by a graph on $n+1$
vertices $\{0,1,\ldots,n\}$. We regard an edge between $u$ and $v$
as the half-open interval $\[u,v)$, when $u<v$.

Graphs are represented as in the algorithms of the Stanford GraphBase~[\sgb],
and the reader of this program is supposed to be familiar with the elementary
conventions of that system.
@^Stanford GraphBase@>

The program reads two command-line parameters,
$m$ and $n$, and an optional third parameter representing a random-number
seed. (The seed value is zero by default.) The Franzblau/Kleitman algorithm
is then applied to the graph |random_graph(n+1,m,0,0,0,0,0,0,0,seed)|,
a~random graph with vertices $\{0,1,\ldots,n\}$ and $m$ edges.
Alternatively, the user can specify an arbitrary graph as input by typing
the single command-line parameter \.{-g}$\langle\,$filename$\,\rangle$;
in this case the named file should describe the graph in |save_graph| format
(as in the {\sc MILES\_SPAN} program of~[\sgb]).
@.Usage@>

When the computation is finished, a minimal generating family and a
maximal irredundant subfamily will be printed on the standard output file.

If a negative value is given for |n|, the random graph is reversed from
left to right; each interval $\[a,b)$ is essentially replaced by $\[-b,-a)$
(but minus signs are suppressed in the output).
This feature lends credibility to the correctness of our
highly asymmetric algorithm and program, because we can verify the fact that
the minimum generating family of the mirror image of~|F| is indeed
the mirror image of |F|'s minimum generating family.

In practice, the algorithm tends to be interesting only when $m$ and $n$ are
roughly equal. If $n$ is large compared to~$m$, we can remove any vertices of
degree zero; such vertices aren't the endpoint of any interval. If $m$ is
large compared to~$n$, we can almost always find $n$ irredundant intervals by
inspection. The running time in general is readily seen to be $O(mn+n^2)$.

@d panic(k) { fprintf(stderr,"Oops, we're out of memory! (Case %d)\n",k);
              return k; }
@.Oops, we're out of memory@>

@c
#include "gb_graph.h" /* the GraphBase data structures */
#include "gb_rand.h" /* the |random_graph| generator */
#include "gb_save.h" /* the |restore_graph| generator */
@#
@h@#
Graph *F; /* the graph that defines intervals */
Graph *G; /* a graph of intervals that generate |F| */
@#
@<Subroutines@>@;
@#
main(argc,argv)
  int argc; /* the number of command-line arguments, plus 1 */
  char *argv[]; /* the command-line arguments */
{
  register Vertex *t,*u,*v,*w,*x; /* current vertices of interest */
  register Arc *a,*b,*c; /* current arcs of interest */
  @<Scan the command-line options and generate |F|@>;
  @<Compute |G| and |S| by the Franzblau/Kleitman algorithm@>;
  if (gb_trouble_code) panic(1);
@^abnormal exit 1@>
  @<Construct an irredundant subfamily of |F| with the cardinality of |G|@>;
  @<Print the results@>;
  return 0; /* this is the normal exit */
}

@ @<Scan the command-line options...@>=
{
  int m=0,n=0,seed=0;
  if (argc>=3 && sscanf(argv[1],"%d",&m)==1 && sscanf(argv[2],"%d",&n)==1) {
    if (argc>3) sscanf(argv[3],"%d",&seed);
    if (m<0) {
      m=-m; /* we assume the user meant to negate |n| instead of |m| */
      n=-n;
    }
    if (n>=0) F=random_graph(n+1,m,0,0,0,0,0,0,0,seed);
    else {
      G=random_graph(-n+1,m,0,0,0,0,0,0,0,seed);
      @<Set |F| to the mirror image of |G|@>;
      gb_recycle(G);
    }
  } else if (argc==2 && strncmp(argv[1],"-g",2)==0)
    F=restore_graph(argv[1]+2);
  else {
    fprintf(stderr,"Usage: %s m n [seed]  |  %s -gfoo.gb\n",argv[0],argv[0]);
@.Usage@>
    return 2;
@^abnormal exit 2@>
  }
  if (!F) {
    fprintf(stderr,
      "Sorry, can't create the graph! (error code %ld)\n",panic_code);
@.Sorry, can't create the graph@>
    return 3;
@^abnormal exit 3@>
  }
}
printf("Applying Franzblau/Kleitman to %s:\n",F->id);

@ @<Set |F|...@>=
F=gb_new_graph(G->n);
if (!F) panic(4);
@^abnormal exit 4@>
make_compound_id(F,"reflect(",G,")");
for (v=G->vertices,u=F->vertices+F->n-1;v<G->vertices+G->n;u--,v++) {
  v->clone=u;
  u->name=gb_save_string(v->name);
}
for (v=G->vertices;v<G->vertices+G->n;v++)
  for (a=v->arcs;a;a=a->next)
    gb_new_arc(v->clone,a->tip->clone,1);

@* The main algorithm. We follow the outline of \S\outline.

@<Compute |G| and |S|...@>=
@<Make |G| a copy of |F|, retaining only leftward arcs@>;
for (v=G->vertices+2;v<G->vertices+G->n;v++)
  @<Reduce all minimal bad intervals with right endpoint |v|
     and record them in |S|@>;

@ The algorithm doesn't need pointers from the left endpoint of an interval
to the right endpoint; leftward pointers are sufficient. (This observation
makes the reduction procedure faster.)

While copying |F|, we remove its rightward arcs, and we assign
length~1 to all its leftward arcs. Later on, we will represent intervals
of |S| by recording them in |F| as leftward arcs of length~|-1|.

We also clear two utility fields of |F|'s vertices, since they will
be used by the algorithm later. (They might be nonzero, if |F| was
supplied with the \.{-g} option.)

@d clone u.V /* the vertex in |F| that matches a vertex in |G|,
                or vice versa */

@<Make |G| a copy of |F|, retaining only leftward arcs@>=
switch_to_graph(NULL); /* prepare to return to graph |F| later */
G=gb_new_graph(F->n); /* a graph with nameless vertices and no arcs */
if (!G) panic(5);
@^abnormal exit 5@>
for (u=F->vertices,v=G->vertices;u<F->vertices+F->n;u++,v++) {
  u->clone=v; @+ v->clone=u;
  u->y.I=u->z.I=0;
  v->name=gb_save_string(u->name);
  for (a=u->arcs,b=NULL;a;a=a->next)
    if (a->tip>=u) { /* we will remove the non-leftward arc |a| */
       if (b) b->next=a->next;
       else u->arcs=a->next;
    }@+else { /* we will copy the leftward arc |a| */
      gb_new_arc(v,a->tip->clone,0); /* the length in $G$ is 0 */
      a->len=1; /* but in $F$ the length is 1 */
      b=a; /* |b| points to the last non-removed arc */
    }
}
if (gb_trouble_code) panic(6);
@^abnormal exit 6@>
switch_to_graph(F); /* now we can add arcs to |F| again */

@ Here's the most interesting part of the program, algorithmwise.
Given a vertex~|v|, we
want to find the largest |u|, if any, such that $\[u,v)$ is bad for the
intervals in~|G|. So we sweep through the intervals $\[u,v)$ from right to
left, decreasing~|u| until it reaches a limiting value~|t|. Here |t| is the
least upper bound on a left endpoint that could guarantee double coverage
of all points in $\[u,v)$.

The utility field |x->count| records the number of intervals with left
endpoint |x| and right endpoint |w| in the range |u<w<=v|.
Another utility field
|x->link| is used to link vertices with nonzero counts together so that
we can clear the counts to zero again afterwards.

It's easy to see that each iteration of the |while| loop in this
section takes at most $O(m+n)$ steps. The actual computation time is,
however, usually much faster. 

This program is designed to work correctly when $G$ contains more than one arc
from $u$ to~$v$. Duplicate arcs are discarded as a special case of the
reduction procedure.

@d count z.I /* coverage decreases by this much when we pass to the left */
@d link  y.V /* pointer to a vertex
                  whose |count| field needs to be zeroed later */

@<Reduce all minimal bad intervals...@>=
{
  while (1) {
    int coverage=0;
         /* the number of intervals $\subseteq\[t,v)$ that contain |u| */
    int potential=0; /* sum of |x->count| for |x<t| */
    Vertex *cleanup=NULL; /* head of the list of vertices with nonzero count */
    for (u=v,t=v-1;u>t;u--) {
      coverage -= u->count; /* we prepare to decrease |u| */
      @<Update the counts for all intervals ending at |u|@>;
      if (coverage+potential<2) { /* there's no bad interval ending at |v| */
        @<Clean up all |count| fields@>;
        goto done_with_v;
      }
      while (coverage<2) {
        t--;
        coverage += t->count;
        potential -= t->count;
      }
    }
    gb_new_arc(v->clone,u->clone,-1);
      /* $\[u,v)$ is minimally bad; we record it in |S=-F| */
    @<Replace $G$ by $G\]\int u,v)$@>;
    @<Clean up all |count| fields@>; /* now we'll try again */
  }
  done_with_v:;
}

@ @<Update the counts for all intervals ending at |u|@>=
for (a=u->arcs;a;a=a->next) {
  w=a->tip;
  if (w->count==0) {
    w->link=cleanup;
    cleanup=w;
  }
  w->count++;
  if (w>=t) coverage++;
  else potential++;
}

@ @<Clean up all |count| fields@>=
for (w=cleanup;w;w=w->link) w->count=0;

@ The reduction process is kind of cute too.

@<Replace $G$ by $G\]\int u,v)$@>=
for (a=v->arcs,c=NULL,w=v;a;c=a,a=a->next)
  if (a->tip>=u && a->tip<w) w=a->tip,b=c;
/* now $\[w,v)$ is the longest interval from |v| inside $\[u,v)$;
   we'll remove it */
if (b) b->next=b->next->next;
else v->arcs=v->arcs->next; @/@,
/* the remaining job is to shorten the other maximal arcs in $\[u,v)$ */
for (t=v-1;w>u;t--) {
  for (a=t->arcs,x=w; a; a=a->next)
    if (a->tip>=u && a->tip<x) x=a->tip,b=a;
  if (x<w) b->tip=w,w=x; /* $\[x,t)$ is the longest interval from |t| */
}

@* The d\'enouement. Now we build a binary tree in the original graph |F|,
by filling in some of the utility fields of |F|'s vertices.
If a node in the tree is labeled with |x| and with the interval $[u,v)$,
we represent it by |x->left=u| and |x->right=v|; the subtrees of this
node are |x->llink| and |x->rlink|. The root of the whole tree is
|F->root|.

The |rlink| field happens to be the same as the |count| field, but this
is no problem because the |rlink| is never changed or examined until after
the |count| has been reset to zero for the last time.

@d left x.V /* left endpoint of interval labeling this node */
@d right w.V /* right endpoint of interval labeling this node */
@d llink v.V /* left subtree of this node */
@d rlink z.V /* right subtree of this node */
@d root uu.V /* root node of the binary tree for this graph */

@<Construct an irredundant...@>=
F->root=make_tree(F->vertices,F->vertices+F->n-1);

@ With a little care we could maintain a stack within |F| itself, but
it's easier to use recursion in \CEE/. Let's just hope the system
programmers have given us a large enough runtime stack to work with.

This subroutine is based on the trick explained in \S\trick.

@<Subroutines@>=
Vertex *make_tree(t,w)
  Vertex *t,*w;
{
  register Vertex *u,*v,*x;
  register Arc *a;
  @<Find a vertex |x| with $N_x\,F\:\int t,w)-N_x\,S\:\int t,w)=1$@>;
  if (!x) return NULL; /* $F\:\[t,w)$ is empty */
  @<Find an interval $\int u,v)$ such that $x\in\int u,v)\seq\int t,w)$@>;
  x->left=u;
  x->right=v;
  x->llink=make_tree(t,x);
  x->rlink=make_tree(x+1,w);
  return x;
}

@ A subtle bug is avoided here when we realize that a vertex might
already be in the cleanup list when its |count| is zero.

@<Find a vertex |x|...@>=
{
  register int coverage=0; /* coverage in |F| minus |S| */
  Vertex *cleanup=w+1; /* |w+1| is a sentinel value */
  for (v=w,x=NULL;v>t;v--) {
    coverage -= v->count; /* now |coverage| refers to $N_{v-1}$ */
    for (a=v->arcs;a;a=a->next) {
      u=a->tip;
      if (u>=t) {
        if (u->link==NULL) u->link=cleanup,cleanup=u;
        u->count += a->len; /* the length is $+1$ for $F$, $-1$ for $S$ */
        coverage += a->len;
      }
    }
    if (coverage==1) {
      x=v-1;@+ break;
    }
  }
  if (!x && cleanup<=w) fprintf(stderr,"This can't happen!\n");
@.This can't happen@>
  while (cleanup<=w) {
    v=cleanup->link; cleanup->count=0; cleanup->link=NULL; cleanup=v;
  }
}

@ @<Find an interval...@>=
for (v=w;v>x;v--) {
  for (a=v->arcs;a;a=a->next) if (a->len>0) {
    u=a->tip;
    if (u<=x && u>=t) goto done;
  }
}
done:

@ @<Print...@>=
printf("Minimum generating family:");
for (v=G->vertices+1;v<G->vertices+G->n;v++)
  for (a=v->arcs;a;a=a->next)
    printf(" [%s..%s)",a->tip->name,v->name);
printf("\nMaximum irredundant family:");
postorder_print(F->root);
printf("\n");

@ There's just one subroutine to go. This is textbook stuff.

@<Subroutines@>=
void postorder_print(x)
  Vertex *x;
{
  if (x) {
    postorder_print(x->llink);
    postorder_print(x->rlink);
    printf(" %s[%s..%s)",x->name,x->left->name,x->right->name);
  }
}

@* Comments and extensions.
The program just presented incorporates several refinements to the
implementation sketched by Franzblau and Kleitman in~[\FK], and the author
@^Knuth, Donald Ervin@>
hopes that readers will enjoy finding them in the code. The Stanford GraphBase
provides convenient data structures, by means of which it was possible to
make the program short and sweet. However, most of the
key ideas (except for the |make_tree| procedure) can be found in~[\FK].
@^Stanford GraphBase@>
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>

@ Lubiw [\Lu] discovered that the algorithm of Franzblau and Kleitman can be
generalized so that it finds optimum irredundant subfamilies and
generating families in an appropriate sense when the points of the underlying
line have been given arbitrary nonnegative {\it weights}. It should be
interesting and instructive to extend the program above so that it
handles this more general problem.

@ The introductory remarks in \S\intro\ mention the recent breakthrough by
@^Frank, Andr\'as@>
@^Jord\'an, Tibor@>
Frank and Jord\'an~[\FJ], who showed (among many other things) that
Gy\H{o}ri's theorem can be extended to intervals on a circle as well as a
line. Such a generalization was surprising because the size of a minimum
generating set might be strictly larger than the size of a maximum irredundant
subfamily of cyclic intervals. For example, the $n$ intervals $\[k,k+2)$ for
$0\le k<n$ on
the ring of integers mod~$n$ are obviously redundant; if we leave out any one
of them, the remaining $n-1$ intervals
will cover all $n$ points. However, these cyclic
intervals cannot be generated by fewer than $n$ subintervals: No $n-1$
subintervals of length~1 will do the job, and if $\[k,k+2)$ is one of the
generators the remaining $n-1$ intervals require $n-1$ further generators
because they are irredundant.

\callthis\firstext
Gy\H{o}ri's minimax principle is restored, however, if we change the
definition of irredundant families.
@^irredundant sets, definition@>
We can say that $F$ is irredundant if each $f\in F$ has a distinguished
element $f_*\in f$, such that whenever $f$ and~$f'$ are distinct sets of~$F$
we have either $f_*\notin f'$ or $f'_*\notin f$. If $F$ is irredundant in this
sense, and if $G$~generates~$F$, it is not difficult to prove that
$\vert F\vert\le\vert G\vert$: There is a $g_f\in G$ for each $f\in F$, with
the property that $f_*\in g_f\subseteq f$; our new definition guarantees that
$g_f\ne g_{f'}$ when $f\ne f'$.

According to this new definition, the intervals $\[k,k+d)$ for $0\le k<n$,
modulo~$n$, are irredundant whenever $n>2(d-1)$, because we can let
$\[k,k+d)_*=k$. Frank and Jord\'an showed that if $F$ is any family of
intervals modulo~$n$ with the property that each intersection $f\cap f'$ of
two of its 
members is either empty or a single interval, then the size of $F$'s smallest
generating family is the size of its largest irredundant subfamily under the
new definition.

@ For intervals on a line, Gy\H{o}ri [\Gy] had already observed that both
definitions of irredundancy are equivalent. Suppose a system of
representatives $f_*\in f$ is given for all $f$ in some family~$F$ of
intervals on a line, such that $f\ne f'$ implies $f_*\notin f'$ or $f'_*\notin
f$. If we cannot arrange those intervals in a sequence $f\(1)$, $f\(2)$,
\dots, $f\(n)$ such that $f_*\(j)\notin f\(1)\cup\cdots\cup f\(j-1)$
for $1<j\le n$, there must be some cycle of intervals such that
$f_*\(1)\in f\(2)$, $f_*\(2)\in f\(3)$, \dots, $f_*\(m)\in f\(1)$,
where $m>2$. Consider the shortest such cycle, and suppose
$f_*\(1)=\min_{j=1}^m f_*\(j)$. We cannot have $f\(k-1)<f_*\(k)$ for
$1<k\le m$, because $f_*\(m)\in f\(1)$; let $k>1$ be minimum such that
$f\(k-1)$ is not strictly less than~$f_*\(k)$. Then
$f\(k-1)$ must be strictly greater than~$f_*\(k)$, and we have
$f_*\(1)<f_*\(k)<f_*\(k-1)$. There is some $j$ with $1<j<k$ and
$f_*\(j-1)<f_*\(k)<f_*\(j)$; since $f_*\(j-1)\in f\(j)$ we have
$f_*\(k)\in f\(j)$, a shorter cycle. This contradiction shows that no
cycles exist.

@ \callthis\secondext
Frank and Jord\'an gave another criterion for irredundancy that works
@^Frank, Andr\'as@>
@^Jord\'an, Tibor@>
@^irredundant sets, definition@>
also for general families of intervals on a circle when large intervals might
wrap around so that their intersection$f\cap f'$ consists of two disjoint
intervals. In such cases they allow $\{f_*,f'_*\}\subseteq f\cap f'$, but only
if $f_*$ and $f'_*$ lie in different components of $f\cap f'$. For example,
the intervals $\[k,k+d)$ for $0\le k<n$, modulo~$n$, are irredundant by this
definition for all $n>d$. Once again the minimax theorem for
generating families and irredundant subfamilies remains valid, in this
extended sense.

@ The algorithms presented by Frank and Jord\'an [\FJ] for such problems
require linear programming as a subroutine. Therefore it would be extremely
interesting to find a purely combinatorial procedure, analogous to the
algorithm of Franzblau and Kleitman, either for the wrap-restricted situation
of \S\firstext\ or for the more general setup of \S\secondext.
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>
@^Frank, Andr\'as@>
@^Jord\'an, Tibor@>

@* References.

\newdimen\refindent \refindent=27pt
\def\ref[#1] {\smallskip\noindent\hangindent\refindent
  \hbox to\refindent{\hfill[#1]\enspace}}

\ref[\CR] Joseph C. Culberson and Robert A. Reckhow, ``Covering polygons
is hard,'' {\sl Journal of Algorithms\/ \bf17} (1994), 2--44.
@^Culberson, Joseph Carl@>
@^Reckhow, Robert Allen@>

\ref[\FJ] Andr\'as Frank and Tibor Jord\'an, ``Minimal edge-coverings of pairs
of sets,'' {\sl Journal of Combinatorial Theory\/ \bf B65} (1995), 73--110.
@^Frank, Andr\'as@>
@^Jord\'an, Tibor@>

\ref[\FK] Deborah S. Franzblau and Daniel J. Kleitman, ``An algorithm for
 constructing polygons with rectangles,'' {\sl Information and Control\/
 \bf63} (1984), 164--189.
@^Franzblau, Deborah Sharon@>
@^Kleitman, Daniel J [Isaiah Solomon]@>

\ref[\Gy] Ervin Gy\H{o}ri, ``A minimax theorem on intervals,'' {\sl Journal
 of Combinatorial Theory\/ \bf B37} (1984), 1--9.
@^Gy\H{o}ri, Ervin@>

\ref[\KB] Donald E. Knuth and P. B. Bendix, ``Simple word problems in
 universal algebras,'' in {\sl Computational Problems in Abstract
 Algebra}, edited by J. Leech (Oxford:  Pergamon, 1970), 263--297.
 Reprinted in {\sl Automation of Reasoning}, edited by J\"org~H.
 Siekmann and Graham Wrightson, {\bf2} (Springer, 1983), 342--376.
@^Knuth, Donald Ervin@>
@^Bendix, Peter Bernard@>

\ref[\vone] Donald E. Knuth, {\sl Fundamental Algorithms}, Volume~1 of
 {\sl The Art of Computer Programming\/} (Reading, Massachusetts:
 Addison-Wesley, 1968), $\rm xxii + 634$~pp.

\ref[\vthree] Donald E. Knuth, {\sl Sorting and Searching}, Volume~3 of
 {\sl The Art of Computer Programming\/} (Reading, Massachusetts:
 Addison-Wesley, 1973), $\rm xii + 722$~pp.\ + foldout illustration.
 
\ref[\sgb] Donald E. Knuth, {\sl The Stanford GraphBase\/}:\ A Platform
 for Combinatorial Computing (New York: ACM Press, 1993), $\rm viii+576$~pp.
 Available via anonymous ftp from \.{labrea.stanford.edu} in
 directory \.{\char`\~ftp/pub/sgb}.

\ref[\cweb] Donald E. Knuth and Silvio Levy, {\sl The {\slttten CWEB} System
of Structured Documentation\/} (Reading, Massachusetts: Addison-Wesley,
1994).
@^Levy, Silvio Vieira Ferreira@>

\ref[\Lu] Anna Lubiw, ``A weighted min-max relation for intervals,''
 {\sl Journal of Combinatorial Theory\/ \bf B53} (1991), 173--194.
@^Lubiw, Anna@>

@ The author thanks the referees of this note for many valuable suggestions
that greatly improved the presentation.
@^Knuth, Donald Ervin@>

@* Index.

