% illustrations for "partitioned tensor products and their spectra"

numeric w,t,m,st,sm,s,r;
w=1.5in;  % distance between left and right foci
t=2.5in;    % height of top foci (for G)
st=.4in;  % spread between points of G
m=1.5in;    % height of middle foci (for H)
sm=.35in; % spread between points of H
s=.35in;  % spread between upper and lower foci (for GxH)
labeloffset:=.4in;

def arc(expr p) =
 drawarrow subpath (0,.8) of p;
 draw subpath (.8,1) of p;
enddef;

beginfig(1);
y1=y2; y3=y4; y1-y3=st; .5[y1,y3]=t;
x1=x3=0; x2=x4=w;
z0=(0,m);
r * sqrt3 = sm;
z5=z0-(r,0);
z6=z0+((r,0) rotated 60);
z7=z0+((r,0) rotated-60);
x8=x9=w; .5[y8,y9]=m; y8-y9=sm;

z10=(0,s); z30=(0,-s);
z10-z0=z15-z5=z16-z6=z17-z7=z28-z8=z29-z9;
z30-z0=z35-z5=z36-z6=z37-z7=z48-z8=z49-z9;

pickup pencircle scaled 2.5pt;
drawdot z1; drawdot z2; drawdot z3; drawdot z4;
drawdot z5; drawdot z6; drawdot z7; drawdot z8; drawdot z9;
drawdot z15; drawdot z16; drawdot z17; drawdot z28; drawdot z29;
drawdot z35; drawdot z36; drawdot z37; drawdot z48; drawdot z49;

pickup pencircle scaled .4pt;
arc(z1--z2);
arc(z2--z3);
arc(z3--z4);
arc(z5{up}..z6{up rotated-120});
arc(z6{up rotated-120}..z7{up rotated 120});
arc(z7{up rotated 120}..z5{up});
arc(z6--z8);
arc(z7{.5[z8,z9]-z7}..z8);
arc(z8--z9);
arc(z9--z7);
arc(z15{up}..z16{up rotated-120});
arc(z16{up rotated-120}..z17{up rotated 120});
arc(z17{up rotated 120}..z15{up});
arc(z35{up}..z36{up rotated-120});
arc(z36{up rotated-120}..z37{up rotated 120});
arc(z37{up rotated 120}..z35{up});
arc(z16--z28);
arc(z17{.5[z28,z29]-z17}..z28);
arc(z28--z29);
arc(z48--z49);
arc(z36--z48);
arc(z37{.5[z48,z49]-z37}..z48);
arc(z29--z37);

pickup pencircle scaled 1pt;
draw (.5w,-s-.4in)--(.5w,t+st+.2in) dashed withdots;

labeloffset:=.4in;
label.lft(btex $G=$ etex,.5[z1,z3]);
label.lft(btex $H=$ etex, z0);
label.lft(btex $G\mathbin{\underline{\mkern-2mu\times\mkern-2mu}}H=$ etex,
                      .5[z10,z30]);
label.bot("(a)",(.5w,-s-.35in));
endfig;

beginfig(11); % actually Fig 1b
y1-y3=st; .5[y1,y3]=y2=t;
x1=x3=0; x2=w;
y4=y5=.5[y6,y7]=m; y6-y7=sm;
x5-x4=sm; .5[x4,x5]=0; x6=x7=w;
x14=x34=x4; x15=x35=x5; x26=x27=x6;
y14=y15=s; .5[y26,y27]=0; y26-y27=y6-y7; y34=y35=-s;

pickup pencircle scaled 2.5pt;
drawdot z1; drawdot z2; drawdot z3;
drawdot z4; drawdot z5; drawdot z6; drawdot z7;
drawdot z14; drawdot z15; drawdot z26; drawdot z27; drawdot z34; drawdot z35;

pickup pencircle scaled .4pt;
draw z1--z2--z3;
draw z4--z5--z6--z7--z5;
draw z14--z15--z26--z27--z15;
draw z34--z35--z26--z27--z35;

pickup pencircle scaled 1pt;
draw (.5w,-s-.4in)--(.5w,t+st+.2in) dashed withdots;

label.bot("(b)",(.5w,-s-.35in));
endfig;

beginfig(2);
y1=y2; y3=y4; y1-y3=st; .5[y1,y3]=t;
x1=x3=0; x2=x4=w;
z0=(0,m);
z5=z0-(r,0);
z6=z0+((r,0) rotated 60);
z7=z0+((r,0) rotated-60);
x8=x9=w; .5[y8,y9]=m; y8-y9=sm;

z10=(0,s); z30=(0,-s);
z10-z0=z15-z5=z16-z6=z17-z7=z28-z8=z29-z9;
z30-z0=z35-z5=z36-z6=z37-z7=z48-z8=z49-z9;

pickup pencircle scaled 2.5pt;
drawdot z15; drawdot z16; drawdot z17; drawdot z28; drawdot z29;
drawdot z35; drawdot z36; drawdot z37; drawdot z48; drawdot z49;

pickup pencircle scaled .4pt;
arc(z15{up}..z16{up rotated-120});
arc(z16{up rotated-120}..z17{up rotated 120});
arc(z17{up rotated 120}..z15{up});
arc(z35{up}..z36{up rotated-120});
arc(z36{up rotated-120}..z37{up rotated 120});
arc(z37{up rotated 120}..z35{up});
arc(z16--z48);
arc(z17{.5[z48,z49]-z17}..z48);
arc(z28--z29);
arc(z48--z49);
arc(z29--z17);
arc(z49--z37);

pickup pencircle scaled 1pt;
draw (.5w,-s-.4in)--(.5w,m-sm-.2in) dashed withdots;

label.lft(btex $G^R\mathbin{\underline{\mkern-2mu\times\mkern-2mu}}H=$ etex,
                      .5[z10,z30]);
label.bot("(a)",(.5w,-s-.35in));
endfig;

beginfig(21); % actually Fig 2b
y1-y3=st; .5[y1,y3]=y2=t;
x1=x3=0; x2=w;
y4=y5=.5[y6,y7]=m; y6-y7=sm;
x5-x4=sm; .5[x4,x5]=0; x6=x7=w;
x24=x4; x25=x5; x16=x17=x36=x37=x6;
y24=y25=0; .5[y16,y17]=s; .5[y36,y37]=-s; y16-y17=y36-y37=y6-y7;

pickup pencircle scaled 2.5pt;
drawdot z16; drawdot z17; drawdot z24; drawdot z25; drawdot z36; drawdot z37;

pickup pencircle scaled .4pt;
draw z24--z25--z16--z17--z25;
draw z25--z36--z37--z25;

pickup pencircle scaled 1pt;
draw (.5w,-s-.4in)--(.5w,m-sm-.2in) dashed withdots;

label.bot("(b)",(.5w,-s-.35in));
endfig;

beginfig(3);
numeric del,w;
del=.04in; w=1.0in;
vardef upper(expr p) = p+(-del,del) enddef;
vardef lower(expr p) = p+(del,-del) enddef;
for i=0 upto 1: for j=0 upto 1: for k=0 upto 1:
  z[i][j][k]=(i*w+j*w/2,j*w/2+k*w);
endfor endfor endfor
pickup pencircle scaled 2.5pt;
for i=0 upto 1: for j=0 upto 1: for k=0 upto 1:
  if (i+j+k)mod 2 = 0: drawdot upper(z[i][j][k]); drawdot lower(z[i][j][k]);
  else: drawdot z[i][j][k]; fi
endfor endfor endfor
pickup pencircle scaled .4pt;

def doit(suffix i,ii,iii,j,jj,jjj)=
  draw z.i.ii.iii--upper(z.j.jj.jjj);
  draw z.i.ii.iii--lower(z.j.jj.jjj);
enddef;

doit(0,0,1,0,0,0); doit(0,0,1,0,1,1); doit(0,0,1,1,0,1);
doit(0,1,0,0,0,0); doit(0,1,0,0,1,1); doit(0,1,0,1,1,0);
doit(1,0,0,0,0,0); doit(1,0,0,1,0,1); doit(1,0,0,1,1,0);
doit(1,1,1,1,1,0); doit(1,1,1,1,0,1); doit(1,1,1,0,1,1);
endfig;

bye
  
