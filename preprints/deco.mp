% illustrations for "Deconstructing Coroutines" and SPIDERS
path unitcircle;
numeric s; s=1/sqrt2;
unitcircle = ((0,-1){right}...(s,-s)...(1,0){up}...
     (s,s)...(0,1){left}...(-s,s)...(-1,0){down}...
     (-s,-s)...cycle);

% Arrowhead Modifications for TAOCP
ahangle := 65;
ahlength := 6;
vardef arrowhead expr p =
  save q, e, f, g; path q; pair e; pair f; pair g;
  e = point length p of p;
  q = gobble(p shifted -e cutafter makepath(pencircle scaled 2ahlength))
    cuttings;
  f = point 0 of (q rotated 0.5ahangle) shifted e;
  g = point length q of (reverse q rotated -0.5ahangle) shifted e;
  f .. {dir (angle direction length q of (q rotated 0.5ahangle) - 0.3ahangle)}e
    & e{dir (angle direction 0 of ((reverse q) rotated -0.5ahangle)+0.3ahangle)} .. g
enddef;

def _finarr text t =
  draw _apth t;
  draw arrowhead _apth t        % do not fill
enddef;

def _findarr text t =
  draw _apth t;
  draw arrowhead _apth withpen currentpen t;
  draw arrowhead reverse _apth withpen currentpen t
enddef;


numeric nrad; nrad=5pt;
vardef ncirc(expr $) = unitcircle scaled nrad shifted $ enddef;
def nlab(expr n) =
fill ncirc(z[n]) withcolor white;
draw ncirc(z[n]);
label(decimal n,z[n]);
enddef;

numeric u; u=20pt; % grid unit for drawings

beginfig(1)
z1=origin; z2=(2u,0);
z12=.5[z1,z2]+(0,u/3);
z21=.5[z1,z2]-(0,u/3);
drawarrow z1...z12...z2 cutafter ncirc(z2);
drawarrow z2...z21...z1 cutafter ncirc(z1);
for n=1 upto 2: nlab(n); endfor
endfig;

beginfig(2)
z1=origin; z2=(2u,u/2); z3=(2u,-u/2); z4=(4u,0);
pair off,noff; off=(0,u/6);
drawarrow z1... .5[z1,z2]+off...z2 cutafter ncirc(z2);
drawarrow z2... .5[z2,z4]+off...z4 cutafter ncirc(z4);
drawarrow z1... .5[z1,z3]-off...z3 cutafter ncirc(z3);
drawarrow z3... .5[z3,z4]-off...z4 cutafter ncirc(z4);
for n=1 upto 4: nlab(n); endfor
endfig;

beginfig(3)
off:=(0,u);
z1=origin; z2=z1+off;
z3=z1+(2u,0);
z4=z3+(2u,0); z5=z4+off; z6=z5+off;
draw z1--z2; draw z4--z6;
for n=1 upto 6: nlab(n); endfor
endfig;

beginfig(4)
off:=(u,u); noff:=off yscaled -1;
z1=origin; z2=z1+off; z3=z2+noff; z4=z3+off; z5=z4+noff;
draw z1--z2--z3--z4--.5[z4,z5];
for n=1 upto 4: nlab(n); endfor
endfig;

beginfig(5)
z4=origin; z3=z4+off; z2=z3+noff; z5=z2+off; z1=z2+noff; z6=z1+off; z7=z6+noff;
z8=z9+noff; z1=z8+off;
draw z4--z3--z2--z5; draw z2--z1; draw z9--z8--z6--z7;
for n=1 upto 9: nlab(n); endfor
endfig;

beginfig(6)
off:=(1.3u,0); noff:=(0,-u);
z1=origin;
z6=z2+off=z1+noff; z8=z6+off;
z5=z3+.7off; z7=z6+noff; z9=z8+noff;
.5[z3,z5]=z2+noff;
z4=z3+noff;
drawarrow z1--z2 cutafter ncirc(z2);
drawarrow z1--z6 cutafter ncirc(z6);
drawarrow z8--z1 cutafter ncirc(z1);
drawarrow z2--z3 cutafter ncirc(z3);
drawarrow z2--z5 cutafter ncirc(z5);
drawarrow z7--z6 cutafter ncirc(z6);
drawarrow z8--z9 cutafter ncirc(z9);
drawarrow z4--z3 cutafter ncirc(z3);
for n=1 upto 9: nlab(n); endfor
endfig;

bye.

beginfig(1)
z0=origin; z1=(100,0);
drawarrow (z0--z1) cutafter ncirc(z1);
nlab(0,z0); nlab(1,z1);
endfig;
end.

