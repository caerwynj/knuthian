% illustrations for Dancing Links

% first, data structure stuff:
numeric u; u=.15in;
numeric h; h=34u;
numeric v; v=32u;
newinternal j,k,n;
numeric s[]; s1=s2=s3=s5=s6=2; s4=s7=3;
pair U[],D[],L[],R[];

def databoxes =
 pickup pencircle scaled 1pt;
 draw (0,0)--(h,0)--(h,v)--(0,v)--cycle dashed withdots;
 for i=0 upto 7:
  j:=(3+4i)*u; k:=28u; n:=n+1;
  pickup pencircle scaled 2pt;
  U[n]=(j-.5u,k+1.5u); drawdot U[n];
  D[n]=(j+.5u,k-1.5u); drawdot D[n];
  if i>0:
     label(char(64+i) infont "cmr10",(j,k+.5u));   
     label(char(48+s[i]) infont "cmr10",(j,k-.5u));
  else: label("h" infont "cmmi10",(j-1.6u,k));
  fi
  L[n]=(j-.5u,k-1.5u); drawdot L[n];
  R[n]=(j+.5u,k+1.5u); drawdot R[n];
  pickup pencircle scaled .4pt;
  draw (j-u,k-2u)--(j+u,k-2u)--(j+u,k+2u)--(j-u,k+2u)--cycle;
 endfor
 for t=(15u,23u),(23u,23u),(27u,23u),(7u,19u),(19u,19u),(31u,19u),
      (11u,15u),(15u,15u),(27u,15u),(7u,11u),(19u,11u),(11u,7u),(31u,7u),
      (19u,3u),(23u,3u),(31u,3u):
   n:=n+1;
   pickup pencircle scaled 2pt;
   U[n]=t+(-.5u,+.5u); drawdot U[n];
   D[n]=t+(+.5u,-.5u); drawdot D[n];
   L[n]=t+(-.5u,-.5u); drawdot L[n];
   R[n]=t+(+.5u,+.5u); drawdot R[n];
   pickup pencircle scaled .4pt;
   draw (t+(-u,-u))--(t+(+u,-u))--(t+(+u,+u))--(t+(-u,+u))--cycle;
 endfor
enddef;

def ulink(expr i,j) =
  drawarrow U[i]--(U[i]+(0,u));
  if ypart U[j] > ypart U[i]:
    drawarrow U[i]--(L[j]-(0,.5u));
  else:
    draw U[i]--(xpart U[i],v);
    drawarrow (xpart L[j],0)--(L[j]-(0,.5u));
  fi
enddef;
def dlink(expr i,j) =
  drawarrow D[i]--(D[i]-(0,u));
  if ypart D[j] < ypart D[i]:
    drawarrow D[i]--(R[j]+(0,.5u));
  else:
    draw D[i]--(xpart D[i],0);
    drawarrow (xpart R[j],v)--(R[j]+(0,.5u));
  fi
enddef;
def llink(expr i,j) =
  drawarrow L[i]--(L[i]-(u,0));
  if xpart L[j] < xpart L[i]:
    drawarrow L[i]--(D[j]+(.5u,0));
  else:
    draw L[i]--(0,ypart L[i]);
    drawarrow (h,ypart D[j])--(D[j]+(.5u,0));
  fi
enddef;
def rlink(expr i,j) =
  drawarrow R[i]--(R[i]+(u,0));
  if xpart R[j] > xpart R[i]:
    drawarrow R[i]--(U[j]-(.5u,0));
  else:
    draw R[i]--(h,ypart R[i]);
    drawarrow (0,ypart U[j])--(U[j]-(.5u,0));
  fi
enddef;

beginfig(2)
databoxes;
for t=(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,1),(9,10),(10,11),(11,9),
      (12,13),(13,14),(14,12),(15,16),(16,17),(17,15),(18,19),(19,18),(20,21),
      (21,20),(22,23),(23,24),(24,22):
  rlink(xpart t,ypart t); llink(ypart t,xpart t);
endfor
for t=(2,12),(12,18),(18,2),(3,15),(15,20),(20,3),(4,9),(9,16),(16,4),
      (5,13),(13,19),(19,22),(22,5),(6,10),(10,23),(23,6),(7,11),(11,17),
      (17,7),(8,14),(14,21),(21,24),(24,8):
  dlink(xpart t,ypart t); ulink(ypart t,xpart t);
endfor
endfig;

def ulnk(expr i,j) =
  drawarrow U[i]--(U[i]+(0,u));
  if ypart U[j] > ypart U[i]:
    draw U[i]--(L[j]-(0,1.5u));
  else:
    draw U[i]--(xpart U[i],v);
    draw (xpart L[j],0)--(L[j]-(0,1.5u));
  fi
enddef;
def dlnk(expr i,j) =
  drawarrow D[i]--(D[i]-(0,u));
  if ypart D[j] < ypart D[i]:
    draw D[i]--(R[j]+(0,1.5u));
  else:
    draw D[i]--(xpart D[i],0);
    draw (xpart R[j],v)--(R[j]+(0,1.5u));
  fi
enddef;
def llnk(expr i,j) =
  drawarrow L[i]--(L[i]-(u,0));
  if xpart L[j] < xpart L[i]:
    draw L[i]--(D[j]+(1.5u,0));
  else:
    draw L[i]--(0,ypart L[i]);
    draw (h,ypart D[j])--(D[j]+(1.5u,0));
  fi
enddef;
def rlnk(expr i,j) =
  drawarrow R[i]--(R[i]+(u,0));
  if xpart R[j] > xpart R[i]:
    draw R[i]--(U[j]-(1.5u,0));
  else:
    draw R[i]--(h,ypart R[i]);
    draw (0,ypart U[j])--(U[j]-(1.5u,0));
  fi
enddef;
def bypass(expr a,b) =
  theta:=angle(b-a);
  draw (a-1.5u*dir theta){dir theta}...
       (a-u*dir theta+.5u*dir(theta+90)){dir(theta+90)}...
       (a+1.25u*dir(theta+90)){dir theta}..
       (b+1.25u*dir(theta+90)){dir theta}...
       (b+u*dir theta+.5u*dir(theta+90)){dir(theta-90)}...
       (b+1.5u*dir theta){dir theta};
enddef;

beginfig(3)
s4:=1; s7:=2; databoxes;
databoxes;
for t=(3,4),(4,5),(5,6),(6,7),(7,8),(8,1),(9,10),(10,11),(11,9),
      (12,13),(13,14),(14,12),(15,16),(16,17),(17,15),(18,19),(19,18),(20,21),
      (21,20),(22,23),(23,24),(24,22):
  rlink(xpart t,ypart t); llink(ypart t,xpart t);
endfor
for t=(2,12),(12,18),(18,2),(3,15),(15,20),(20,3),(4,9),(9,16),(16,4),
      (22,5),(6,10),(10,23),(23,6),(7,11),(11,17),
      (17,7),(21,24),(24,8):
  dlink(xpart t,ypart t); ulink(ypart t,xpart t);
endfor

rlnk(1,2); rlink(2,3); bypass(U2,R2);
llnk(3,2); llink(2,1); bypass(D2,L2);
ulnk(22,19); ulnk(19,13); ulink(13,5); bypass(L19,U19); bypass(L13,U13);
dlnk(5,13); dlink(13,19); dlink(19,22); bypass(R13,D19);
ulnk(21,14); ulink(14,8); bypass(L14,U14);
dlnk(8,14); dlink(14,21); bypass(R14,D14);
endfig;

beginfig(4)
s2:=1; s5:=1; s7:=1; databoxes;
databoxes;
for t=(3,4),(6,7),(9,10),(10,11),(11,9),
      (12,13),(13,14),(14,12),(15,16),(16,17),(17,15),(18,19),(19,18),(20,21),
      (21,20),(22,23),(23,24),(24,22):
  rlink(xpart t,ypart t); llink(ypart t,xpart t);
endfor
for t=(2,12),(12,18),(18,2),(3,15),(4,9),(9,16),(16,4),
      (22,5),(6,10),(7,11),(11,17),(17,7):
  dlink(xpart t,ypart t); ulink(ypart t,xpart t);
endfor

rlnk(1,2); rlink(2,3); bypass(U2,R2);
llnk(3,2); llink(2,1); bypass(D2,L2);
ulnk(22,19); ulnk(19,13); ulink(13,5); bypass(L19,U19); bypass(L13,U13);
dlnk(5,13); dlink(13,19); dlink(19,22); bypass(R13,D19);
ulnk(21,14); ulink(14,8); bypass(L14,U14);
dlnk(8,14); dlink(14,21); bypass(R14,D14);

rlnk(4,5); rlink(5,6); bypass(U5,R5);
llnk(6,5); llink(5,4); bypass(D5,L5);
rlnk(7,8); rlink(8,1); bypass(U8,R8);
llnk(1,8); llink(8,7); bypass(D8,L8);
ulnk(3,20); ulink(20,15); bypass(L20,U20);
dlnk(15,20); dlink(20,3); bypass(R20,D20);
ulnk(6,23); ulink(23,10); bypass(L23,U23);
dlnk(10,23); dlink(23,6); bypass(R23,D23);
ulnk(8,24); ulink(24,21); bypass(L24,U24);
dlnk(21,24); dlink(24,8); bypass(R24,D24);
endfig;

% next, polyomino stuff:

def softpath expr p =
 for i=1 upto length p:
  subpath (i-.95,i-.05) of p ..
 endfor cycle
enddef;

def innerpath expr p =
 for i=1 upto length p:
  innerknot i of p--
 endfor cycle
enddef;

vardef innerknot expr i of p =
 pair zz; zz=whatever[point i-1 of p, point i of p]
                 +eps*dir(angle(point i of p - point i-1 of p)+90)
               =whatever[point i of p,point i+1 of p]
                 +eps*dir(angle(point i+1 of p - point i of p)+90);
 if known zz: zz else: (point i of p)
                  + eps*dir(angle(point i+1 of p - point i-1 of p)+90) fi
enddef;

newinternal eps; eps:=.03; % distance to innerknot
newinternal theta; % current direction of path being formed
pair zz; % current point in path being formed
numeric sfactor; sfactor=15; % scale factor

def II = hide(theta:=0; zz:=origin) zz-- enddef; % start a path
def SS = hide(zz:=zz+dir theta) zz-- enddef; % continue in direction theta
def LL = hide(theta:=theta+90) SS enddef; % turn left and continue
def RR = hide(theta:=theta-90) SS enddef; % turn right and continue
def CC = cycle enddef; % end a path

def r = rotated 90 enddef;
def t = transformed transpose enddef;
transform transpose; transpose = identity reflectedabout (origin, (1,1));

def strokeit expr p of z =
  draw (softpath innerpath p) shifted z scaled sfactor
enddef;
def _pathof suffix $ = $.p enddef;
def at = of enddef;
def place text t =
 fillit _pathof t withcolor _colorof t;
 strokeit _pathof t enddef;
def fillit expr p of z =
  fill (softpath innerpath p) shifted z scaled sfactor
enddef;
def _colorof suffix $ = $.c killtext enddef;
def killtext text t = enddef;

vardef makepiece@# (expr hue,shape) =
path @#.p, @#'.p; @#.p=shape; @#'.p=reverse (shape t);
color @#.c, @#'.c; @#.c=@#'.c=hue;
enddef;

makepiece F(.50white, II SS LL SS RR LL LL SS LL RR LL LL CC);
makepiece I(.99white, II SS LL SS SS SS SS LL LL SS SS SS CC);
makepiece L(.70white, II SS SS LL LL RR SS SS LL LL SS SS CC);
makepiece P(.80white, II SS LL RR LL SS LL SS LL SS CC);
makepiece N(.85white, II SS LL RR LL SS SS LL LL SS RR LL CC);
makepiece T(.90white, II SS LL SS RR LL LL SS SS LL LL RR CC);
makepiece U(.92white, II SS SS SS LL SS LL LL RR RR LL LL CC);
makepiece V(.60white, II SS SS SS LL LL SS RR SS LL LL SS CC);
makepiece W(.94white, II SS SS LL LL RR LL RR LL LL SS LL CC);
makepiece X(.40white, II SS LL RR LL LL RR LL LL RR LL LL CC);
makepiece Y(.96white, II SS LL SS SS SS LL LL RR LL LL RR CC);
makepiece Z(.98white, II SS SS LL LL RR SS LL SS LL LL RR CC);

path Y[].p, Y[]'.p;
color Y[].c, Y[]'.c;
Y1.c=.95white;
Y2.c=.80white;
Y3.c=.60white;
Y4.c=.30white;

for i=1 upto 4:
 Y[i].p=Y.p;
 Y[i]'.p=Y'.p;
 Y[i]'.c=Y[i].c;
endfor

beginfig(1)
place F' at (3,2);
place I r at (5,7);
place L r r at (8,8);
place P r r r at (0,4);
place N' r r r at (5,8);
place T r at (3,1);
place U r r r at (0,7);
place V r at (8,0);
place W r r at (5,7);
place X at (2,4);
place Y r r r at (1,1);
place Z' r at (7,1);
path frame; frame = II LL SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS RR
                     SS SS SS SS SS SS SS RR SS SS SS SS SS SS CC;
path iframe; iframe = II SS SS LL SS LL SS LL CC;
draw (softpath innerpath frame) scaled sfactor;
draw (softpath innerpath iframe) shifted (3,3) scaled sfactor;
endfig;

beginfig(61)
place Y2 at (1,8);
place Y3 at (2,10);
place Y1 at (8,9);
place Y3 at (9,4);
place Y3 r at (8,9);
place Y3 r at (7,6);
place Y3 r r at (1,10);
place Y3 r r at (7,5);
place Y1 r r r at (5,1);
place Y2' at (1,14);
place Y2' at (6,14);
place Y1' at (11,14);
place Y3' at (4,12);
place Y2' at (10,12);
place Y2' at (11,9);
place Y4' at (6,8);
place Y4' at (1,4);
place Y4' at (2,1);
place Y1' r at (1,11);
place Y2' r at (1,1);
place Y4' r at (3,6);
place Y1' r at (4,9);
place Y3' r at (10,9);
place Y1' r at (11,6);
place Y1' r at (11,1);
place Y3' r at (13,5);
place Y2' r at (14,2);
place Y4' r r at (8,14);
place Y4' r r at (13,14);
place Y2' r r at (8,11);
place Y4' r r at (14,11);
place Y2' r r at (7,8);
place Y1' r r at (4,6);
place Y3' r r at (5,3);
place Y1' r r at (4,1);
place Y3' r r at (14,1);
place Y2' r r r at (5,6);
place Y1' r r r at (7,8);
place Y2' r r r at (8,6);
place Y4' r r r at (9,4);
place Y2' r r r at (11,8);
place Y4' r r r at (12,5);
place Y3' r r r at (14,14);
place Y4' r r r at (14,9);
place Y1' r r r at (14,4);
path frame; frame = II LL SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

beginfig(62)
place Y4 at (4,3);
place Y2 at (10,9);
place Y2 at (10,4);
place Y3 at (12,10);
place Y4 at (12,5);
place Y4 at (14,10);
place Y1 at (14,5);
place Y2 r at (5,14);
place Y2 r at (10,14);
place Y3 r at (5,12);
place Y3 r at (10,12);
place Y1 r at (8,10);
place Y3 r at (4,9);
place Y2 r at (6,7);
place Y1 r r at (1,4);
place Y3 r r at (3,7);
place Y1 r r at (6,7);
place Y1 r r at (9,8);
place Y3 r r at (10,11);
place Y1 r r at (12,12);
place Y1 r r at (12,7);
place Y2 r r at (14,12);
place Y3 r r at (14,7);
place Y1 r r r at (3,14);
place Y4 r r r at (8,14);
place Y4 r r r at (3,12);
place Y4 r r r at (2,9);
place Y4 r r r at (7,4);
place Y2 r r r at (1,3);
place Y2 r r r at (10,3);
place Y3 r r r at (10,1);
place Y1' at (11,14);
place Y4' at (3,1);
place Y1' r at (1,11);
place Y1' r at (1,5);
place Y3' r at (7,6);
place Y2' r r at (4,11);
place Y3' r r at (9,3);
place Y1' r r at (12,2);
place Y3' r r at (5,1);
place Y2' r r at (10,1);
place Y4' r r r at (1,7);
place Y2' r r r at (7,8);
place Y4' r r r at (8,12);
place Y1' r r r at (14,4);
path frame; frame = II LL SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

beginfig(63)
place Y3 at (12,3);
place Y3 at (14,6);
place Y4 at (14,1);
place Y2 r at (5,14);
place Y3 r at (5,12);
place Y4 r at (8,10);
place Y1 r at (4,9);
place Y3 r at (11,8);
place Y2 r at (6,7);
place Y4 r at (12,3);
place Y1 r r at (1,4);
place Y4 r r at (6,7);
place Y1 r r at (14,8);
place Y4 r r r at (3,14);
place Y1 r r r at (3,12);
place Y2 r r r at (6,10);
place Y3 r r r at (2,9);
place Y2 r r r at (9,8);
place Y2 r r r at (1,3);
place Y1 r r r at (11,1);
place Y1' at (6,14);
place Y1' at (11,14);
place Y4' at (10,12);
place Y3' at (7,11);
place Y4' at (10,9);
place Y4' at (8,6);
place Y2' at (10,2);
place Y3' at (3,1);
place Y3' at (8,1);
place Y1' r at (1,11);
place Y4' r at (1,5);
place Y1' r at (3,3);
place Y1' r at (7,5);
place Y2' r at (8,3);
place Y3' r r at (13,14);
place Y2' r r at (10,13);
place Y2' r r at (4,11);
place Y1' r r at (14,11);
place Y1' r r at (12,5);
place Y1' r r at (9,3);
place Y4' r r at (5,1);
place Y2' r r at (10,1);
place Y3' r r r at (1,7);
place Y3' r r r at (4,7);
place Y2' r r r at (14,14);
path frame; frame = II LL SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

beginfig(64)
place Y1 at (14,11);
place Y1 r r at (1,4);
place Y1' r at (1,11);
place Y1' r r r at (14,4);
path frame; frame = II LL SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

beginfig(10)
place F r r at (2,5);
place F' r r r at (8,5);
place I r at (7,8);
place L r at (5,0);
place L' at (5,0);
place P at (0,6);
place P' r at (10,6);
place N r r at (2,7);
place N' r r r at (8,7);
place T r r r at (5,8);
place U r r at (8,6);
place V r r r at (2,8);
place W r r r at (3,3);
place X at (3,3);
place Y r at (7,6);
place Y' r r r at (6,5);
place Z r at (3,1);
place Z' at (7,1);
path frame; frame = II LL SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS RR SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

beginfig(9)
place F at (22,0);
place F' r r at (26,2);
place I r at (29,0);
place L r at (5,0);
place L' r r at (12,3);
place P r at (16,0);
place P' at (8,0);
place N r r r at (18,2);
place N' r r at (5,3);
place T r r r at (27,2);
place U r r r at (5,3);
place V r r r at (0,3);
place W r r at (16,3);
place X at (7,0);
place Y r at (29,2);
place Y' at (18,2);
place Z at (17,0);
place Z' r at (13,0);
path frame; frame = II LL SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS RR SS SS RR SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS SS CC;
draw (softpath innerpath frame) scaled sfactor;
endfig;

% changes for polysticks
def BB = hide(theta:=theta+180) SS enddef; % turn around and continue
def ST = hide(zz:=zz+dir theta) zz enddef; % go in direction theta and stop
def LT = hide(theta:=theta+90) ST enddef; % turn left and stop
def RT = hide(theta:=theta-90) ST enddef; % turn right and stop

def softerpath expr p =
 subpath (if cycle p: .2 else: .15 fi,
  if point 2 of p = point 0 of p: .85 else: .8 fi) of p
 for i=2 upto length p:
  .. subpath (i-.8,i-if (point i-1 of p=point i+1 of p) or
             (not cycle p and (i=length p)): .15 else: .2 fi) of p
 endfor
 if cycle p: .. cycle fi
enddef;

def strokeit expr p of z =
  draw (softerpath p) shifted z scaled sfactor
enddef;
def place text t =
 strokeit _pathof t withpen pencircle scaled .1sfactor;
 strokeit _pathof t withpen pencircle scaled (.1sfactor-1pt) withcolor _colorof t
enddef;

sfactor:=40;

makepiece F(.81white, II LL RR BB RR RT); % orange (in 845 puzzle)
makepiece H(.99white, II LL RR RR BB LL RT); % green
makepiece I(.35white, II LL SS SS ST);
makepiece J(.89white, II RR LL LL ST); % white
makepiece L(.95white, II BB RR SS ST); % gray
makepiece N(.85white, II LL RR LL ST); 
makepiece O(.24white, II SS LL LL CC);
makepiece P(.59white, II LL RR LL LT); % tan
makepiece R(.65white, II LL LL BB LL RT); % purple
makepiece T(.44white, II SS RR SS BB SS RT);
makepiece U(.71white, II RR LL SS LT); % pink
makepiece V(.76white, II RR SS LL ST);
makepiece W(.97white, II RR LL RR LT); % yellow
makepiece X(.10white, II SS RR BB RR BB RR BB RT); % red
makepiece Y(.92white, II LL SS LL BB LT); % blue
makepiece Z(.52white, II BB RR SS LT);

beginfig(1101)
place F' r r at (5,1);
place H at (-2,1);
place I r at (5,0);
place J at (2,3);
place L at (1,0);
place N' r r r at (4,3);
place O at (4,4);
place P' at (2,1);
place R' r at (1,2);
place T r r r at (5,4);
place U r r r at (1,5);
place V r r at (2,0);
place W at (1,5);
place X at (0,1);
place Y' at (1,5);
place Z' at (2,5);
endfig;

beginfig(1102)
place F' r at (3,2);
place H r r r at (0,5);
place I r at (4,2);
place J at (-2,2);
place L at (1,0);
place N' r at (1,2);
place O at (4,4);
place P' r at (2,2);
place R r r r at (2,1);
place T r r at (3,0);
place U at (3,1);
place V r r r at (4,5);
place W at (3,5);
place X at (0,1);
place Y' r r r at (5,4);
place Z at (5,1);
endfig;

beginfig(1103)
place F' r at (5,1);
place H' r r r at (0,4);
place I r at (4,0);
place J r r r at (1,5);
place L at (-1,1);
place N r r at (1,3);
place O at (4,0);
place P at (3,0);
place R r r at (2,5);
place T at (1,2);
place U r r at (3,4);
place V r r at (5,3);
place W r r r at (4,4);
place X at (0,1);
place Y' r at (4,2);
place Z' r at (2,1);
endfig;

beginfig(1104)
place F' r at (1,2);
place H' r at (3,2);
place I r at (4,2);
place J' at (3,4);
place L at (1,0);
place N at (-2,1);
place O at (4,4);
place P' r r r at (1,5);
place R r r r at (2,1);
place T r r at (3,0);
place U at (3,1);
place V r r r at (2,5);
place W at (3,5);
place X at (0,1);
place Y' r r r at (5,4);
place Z at (5,1);
endfig;

beginfig(1105)
place F r at (5,4);
place H' r r r at (0,5);
place I r at (4,5);
place J' r at (5,3);
place L at (1,0);
place N' r r at (4,1);
place O at (2,3);
place P' at (0,2);
place R' r at (4,0);
place T at (1,2);
place U r at (4,3);
place V r at (3,0);
place W r at (0,3);
place X at (0,1);
place Y at (-1,1);
place Z' r at (2,1);
endfig;

beginfig(131)
place F at (0,2);
place F' r r r at (0,2);
place H at (3,0);
place H' r r r at (3,4);
place R r at (3,3);
place R' r r at (3,1);
place T r r r at (4,3);
place X at (0,2);
place Y r at (4,4);
place Y' r r at (4,0);
endfig;

beginfig(132)
place F at (0,2);
place F' r r r at (0,2);
place H r r at (2,4);
place H' r at (2,0);
place R r r r at (2,1);
place R' at (2,3);
place T r r r at (4,3);
place X at (0,2);
place Y r r r at (1,0);
place Y' at (1,4);
endfig;

beginfig(12)
place O at (0,4);
place T at (1,5);
place J' at (4,4);
place I at (0,0);
place Z at (4,2);
place V r at (2,3);
place Y at (5,2);
place R at (1,2);
place W r r at (3,1);
place P' r at (5,1);
place F r r at (1,2);
place H' at (1,0);
place N r at (3,1);
place X at (3,1);
place U at (3,1);
drawarrow ((2.5,2.5)--(2.8,2.8)) scaled sfactor;
drawarrow ((3.5,3.5)--(3.2,3.2)) scaled sfactor;
endfig;

beginfig(14)
place L r at (3,3);
place Z r at (5,3);
place P r at (7,1);
place J' at (7,2);
place V r at (7,1);
place J r at (9,2);
place P' at (9,1);
place O at (11,2);
place W r at (11,1);
place U r r at (15,1);
place Z' at (15,3);
place N r at (20,0);
place L' at (17,3);
place N' r r at (20,4);
place I at (20,0);
endfig;

beginfig(15)
pickup pencircle scaled .1sfactor;
for i=0 upto 4: for j=4-i upto 5+i:
 draw ((i+.15,j)--(i+.85,j)) scaled sfactor;
 draw ((j,i+.15)--(j,i+.85)) scaled sfactor;
endfor endfor
for i=0 upto 3: for j=4-i upto 5+i:
 draw ((8.85-i,j)--(8.15-i,j)) scaled sfactor;
 draw ((j,8.85-i)--(j,8.15-i)) scaled sfactor;
endfor endfor
endfig;

% changes for polyiamonds
sfactor:=15;
def ll = hide(theta:=theta+60) SS enddef; % turn soft left and continue
def rr = hide(theta:=theta-60) SS enddef; % turn soft right and continue
def LL = hide(theta:=theta+120) SS enddef; % turn hard left and continue
def RR = hide(theta:=theta-120) SS enddef; % turn hard right and continue
def r = rotated 60 enddef;
def place text t =
 fillit _pathof t withcolor _colorof t;
 strokeit _pathof t enddef;
def strokeit expr p of z =
  draw (softpath innerpath p) shifted ((xpart z)*dir 60 + (ypart z,0)) scaled sfactor
enddef;
def fillit expr p of z =
  fill (softpath innerpath p) shifted ((xpart z)*dir 60 + (ypart z,0)) scaled sfactor
enddef;
transform transpose; transpose = identity reflectedabout (origin,right+dir 60);

makepiece A(.90white, II ll RR LL ll SS LL SS CC); % pink (acc to O'Beirne)
makepiece B(.99white, II SS SS LL rr LL SS LL CC); % yellow
makepiece C(.93white, II ll ll rr ll LL SS ll CC); % dark pink
makepiece D(.00white, II SS ll ll ll ll CC);       % black
makepiece E(.96white, II SS SS ll LL rr LL rr CC); % light pink
makepiece F(.70white, II SS ll ll rr LL ll ll CC); % red
makepiece G(.50white, II SS ll LL RR ll LL SS CC); % dark green
makepiece H(.60white, II SS rr LL ll rr LL ll CC); % light green
makepiece I(.20white, II SS ll SS SS LL ll SS CC); % brown
makepiece J(.85white, II SS ll SS ll LL SS rr CC); % orange
makepiece K(.80white, II SS LL RR LL SS LL SS CC); % light blue
makepiece L(.40white, II SS SS LL rr ll LL SS CC); % dark blue

path frame; frame = II SS ll rr ll rr ll ll rr ll rr ll ll rr ll rr ll ll rr ll rr ll ll rr ll rr ll ll rr ll CC;
beginfig(80)
place A r r r r r at (7,3);
place B r at (3,9);
place C r r at (7,4);
place D at (4,5);
place E r r at (1,7);
place F at (5,1);
place F' at (9,2);
place G r at (2,10);
place G' r at (6,2);
place H at (2,3);
place H' r r r at (7,8);
place I r at (1,9);
place I' r r at (1,9);
place J r at (0,8);
place J' at (8,1);
place K r r r r at (5,3);
place K' r r r r r at (7,5);
place L r r r at (5,3);
place L' at (7,5);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated -30;
endfig;

beginfig(81)
place A r r at (6,3);
place B r r at (4,7);
place C r r r r r at (6,2);
place D at (5,4);
place E at (2,3);
place F r r at (9,4);
place F' r at (6,1);
place G r r r at (9,4);
place G' r r at (3,5);
place H r r r r r at (5,1);
place H' r r at (7,7);
place I r r at (3,10);
place I' r at (0,7);
place J at (1,5);
place J' r r r at (5,9);
place K r r r at (8,7);
place K' at (6,5);
place L r r r r r at (3,7);
place L' r r r r at (3,7);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated -30;
endfig;

beginfig(82)
place A at (4,6);
place B r at (0,7);
place C r at (8,6);
place D at (6,4);
place E r r r r r at (6,3);
place F r at (1,5);
place F' r at (1,9);
place G at (4,2);
place G' r r at (4,9);
place H r r r r at (5,3);
place H' r r r r at (5,7);
place I at (5,2);
place I' r r at (5,8);
place J at (2,6);
place J' r r at (3,6);
place K r r r r r at (7,0);
place K' r r r at (7,8);
place L r r at (8,4);
place L' r r r r at (3,7);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated 90;
endfig;

beginfig(83)
place A r r r r at (4,7);
place B r r at (5,6);
place C r r r r at (2,4);
place D at (6,3);
place E r at (2,6);
place F r r at (9,4);
place F' r at (6,1);
place G r r at (4,4);
place G' r at (6,6);
place H r r at (4,8);
place H' r r r r at (3,7);
place I r at (5,6);
place I' r r at (4,5);
place J r r r at (4,7);
place J' r r r at (3,5);
place K at (4,2);
place K' r r r at (8,6);
place L at (5,7);
place L' r r r r r at (5,7);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated -30;
endfig;

beginfig(84)
place A r r r r at (6,4);
place B r at (2,6);
place C r r r r at (3,2);
place D at (7,3);
place E r r r r at (9,1);
place F r r r r at (9,5);
place F' at (9,2);
place G r r r r at (7,6);
place G' r r r r at (8,5);
place H r r r at (5,9);
place H' r r r at (7,4);
place I r at (3,8);
place I' r r at (0,8);
place J r r r r at (8,0);
place J' r r r at (3,10);
place K r r r at (6,3);
place K' r r r r at (4,7);
place L r r r r r at (2,6);
place L' r r at (3,4);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated 30;
endfig;

beginfig(85)
place A r r at (4,4);
place B r at (6,7);
place C r r r r r at (0,7);
place D at (7,2);
place E r at (4,4);
place F at (7,3);
place F' at (7,0);
place G r r at (3,7);
place G' r at (3,7);
place H r r r at (9,5);
place H' r r at (5,3);
place I r r at (6,7);
place I' at (2,7);
place J at (5,7);
place J' r r r at (3,5);
place K at (3,5);
place K' r r r at (5,7);
place L at (3,8);
place L' r r r at (2,7);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated -30;
endfig;

beginfig(86)
place A at (6,5);
place B at (6,3);
place C at (4,9);
place D at (8,3);
place E r at (1,8);
place F at (5,1);
place F' r r r r r at (5,1);
place G at (0,7);
place G' r r r r r at (5,3);
place H r r r r r at (4,4);
place H' r r r at (6,5);
place I r at (2,10);
place I' r at (4,3);
place J r r r at (9,2);
place J' r r at (1,6);
place K r r at (6,7);
place K' r r r at (4,8);
place L r at (6,7);
place L' r r r r at (4,8);
draw (softpath innerpath reverse frame) shifted (7 right) scaled sfactor;
currentpicture:=currentpicture rotated 90;
endfig;

beginfig(71)
place A r at (4,3);
place B r r r r r at (3,3);
place C r r r r at (6,2);
place D at (1,9);
place E r r r r r at (4,4);
place F' at (1,6);
place G' at (1,5);
place H' r r r r r at (3,6);
place I' r r at (3,9);
place J r at (3,7);
place K' r at (3,3);
place L r r at (0,12);
path frame; frame = II SS SS SS SS SS SS LL SS SS SS SS SS ll SS SS SS SS SS LL SS SS SS SS CC;
draw (softpath innerpath reverse frame) shifted (6 right) scaled sfactor;
currentpicture:=currentpicture rotated 30;
endfig;

beginfig(72)
path frame; frame = II SS SS SS SS SS SS SS SS SS RR SS LL SS SS ll SS SS ll SS SS ll SS SS LL SS RR SS SS SS SS SS SS SS SS LL CC;
draw (softpath innerpath reverse frame) scaled sfactor;
currentpicture:=currentpicture rotated 180;
endfig;

beginfig(73)
place A r at (4,4);
place B r r at (5,7);
place C r r at (4,4);
place D at (1,7);
place E r at (3,5);
place F' r at (5,4);
place G r r r at (5,7);
place H' r r r r at (5,5);
place I' at (0,5);
place J r at (3,3);
place K r r r r at (3,4);
place L r r r r r at (8,1);
path frame; frame = II SS SS SS RR SS LL SS SS ll SS SS SS ll SS SS SS ll SS SS LL SS RR SS SS LL SS rr CC;
draw (softpath innerpath reverse frame) shifted (2 dir 60 + 2 right) scaled sfactor;
currentpicture:=currentpicture rotated -90;
endfig;

beginfig(74)
place A r r at (1,9);
place B at (2,4);
place C r r r r at (8,3);
place D at (2,6);
place E r at (2,8);
place F' r r r r r at (7,4);
place G r r r r at (6,6);
place H' r r r at (6,5);
place I at (1,8);
place J' at (4,2);
place K r r at (3,4);
place L r r r r r at (6,0);
path frame; frame = II SS SS SS SS SS RR SS LL SS ll SS SS SS ll SS SS SS ll SS LL SS RR SS SS SS SS LL SS rr CC;
draw (softpath innerpath reverse frame) shifted (2 dir 60 + 2 right) scaled sfactor;
currentpicture:=currentpicture rotated 90;
endfig;

beginfig(75)
place A r r at (1,9);
place B at (2,1);
place C r r r at (5,9);
place D at (2,3);
place E r r r at (6,8);
place F at (2,9);
place G r r at (1,11);
place H r r r r r at (4,3);
place I' at (2,5);
place J' r r r at (4,8);
place K r at (4,7);
place L at (1,8);
path frame; frame = II SS SS SS SS SS SS RR SS LL SS SS SS ll SS SS ll SS SS ll SS SS SS LL SS RR SS SS SS SS SS LL CC;
draw (softpath innerpath frame) shifted (2 dir 60 + right) scaled sfactor;
endfig;


% finally, the queens problem:
numeric u; u=20pt;
numeric r[],f[];
labeloffset:=5bp;
def queengrid =
 for i=0 upto 8:
  draw (0,i*u)--(8u,i*u);
  draw (i*u,0)--(i*u,8u);
  if i<8:
   label.lft(("R"&char(48+i)) infont "cmr10",(0,(i+.5)*u));
   if r[i]>=0: label.rt(char(48+r[i]) infont "cmr10",(8u,(i+.5)*u)); fi
   label.top(("F"&char(48+i)) infont "cmr10",((i+.5)*u,8u));
   if f[i]>=0: label.bot(char(48+f[i]) infont "cmr10",((i+.5)*u,0)); fi
  fi
 endfor
enddef;
def queen(expr i,j)=
 label("Q" infont "chess20" scaled .75,((i+.5)*u,(j+.5)*u))
enddef;
def ex(expr i,j)=
 label(char 2 infont "cmsy10",((i+.5)*u,(j+.5)*u))
enddef;

beginfig(160)
for i=0 upto 7: r[i]=f[i]=8; endfor
queengrid;
drawarrow (9.1u,4.5u)--(8.6u,4.5u);
endfig;

beginfig(161)
r0:=6; r1:=6; r2:=6; r3:=6; r4:=-1; r5:=6; r6:=6; r7:=6;
f0:=7; f1:=7; f2:=7; f3:=6; f4:=5; f5:=5; f6:=5; f7:=-1;
queengrid;
queen(7,4);
for t=(4,7),(5,6),(6,5),(6,3),(5,2),(4,1),(3,0),(0,4),(1,4),(2,4),(3,4),
      (4,4),(5,4),(6,4),(7,7),(7,6),(7,5),(7,3),(7,2),(7,1),(7,0):
 ex(xpart t,ypart t);
endfor
drawarrow (4.5u,-1.25u)--(4.5u,-.75u);
endfig;

beginfig(162)
r0:=5; r1:=5; r2:=4; r3:=4; r5:=-1; r6:=4; r7:=4;
f0:=5; f1:=5; f2:=4; f3:=4; f4:=-1; f5:=4; f6:=4;
queengrid;
queen(7,4); queen(4,5);
for t=(4,7),(5,6),(6,5),(6,3),(5,2),(4,1),(3,0),(0,4),(1,4),(2,4),(3,4),
      (4,4),(5,4),(6,4),(7,7),(7,6),(7,5),(7,3),(7,2),(7,1),(7,0),
      (0,5),(1,5),(2,5),(3,5),(5,5),(4,7),(4,6),(4,4),(4,3),(4,2),
      (4,0),(0,1),(1,2),(2,3),(6,7),(2,7),(3,6):
 ex(xpart t,ypart t);
endfor
drawarrow (9.1u,3.5u)--(8.6u,3.5u);
endfig;

beginfig(163)
r0:=3; r1:=3; r2:=3; r3:=-1; r6:=3; r7:=2;
f0:=4; f1:=3; f2:=2; f3:=2; f5:=-1; f6:=3;
queengrid;
queen(7,4); queen(4,5); queen(5,3);
for t=(4,7),(5,6),(6,5),(6,3),(5,2),(4,1),(3,0),(0,4),(1,4),(2,4),(3,4),
      (4,4),(5,4),(6,4),(7,7),(7,6),(7,5),(7,3),(7,2),(7,1),(7,0),
      (0,5),(1,5),(2,5),(3,5),(5,5),(4,7),(4,6),(4,4),(4,3),(4,2),
      (4,0),(0,1),(1,2),(2,3),(6,7),(2,7),(3,6),
      (0,3),(1,3),(3,3),(5,7),(5,1),(5,0),(2,0),
      (3,1),(6,2),(2,6),(1,7): 
 ex(xpart t,ypart t);
endfor
drawarrow (3.5u,-1.25u)--(3.5u,-.75u);
endfig;

bye.
