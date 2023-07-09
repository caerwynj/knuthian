% illustrations for The Sandwich Theorem

u=20;

beginfig(1);
for j=0,1,2: for k=0,1: z[j][k]=(j,k)*u; endfor endfor
dotlabel.top(btex $\scriptstyle u$ etex,z[0][1]);
dotlabel.top(btex $\scriptstyle v$ etex,z[1][1]);
dotlabel.top(btex $\scriptstyle w$ etex,z[2][1]);
dotlabel.bot(btex $\scriptstyle x$ etex,z[0][0]);
dotlabel.bot(btex $\scriptstyle y$ etex,z[1][0]);
dotlabel.bot(btex $\scriptstyle z$ etex,z[2][0]);

draw z[0][0]--z[2][0];
draw z[0][1]--z[2][1];

setbounds currentpicture to (-1,-1)*u--(3,-1)*u--(3,2)*u--(-1,2)*u--cycle;
endfig;

beginfig(2);
for j=0,1,2: for k=0,1: z[j][k]=(j,k)*u; endfor endfor
dotlabel.top(btex $\scriptstyle u$ etex,z[0][1]);
dotlabel.top(btex $\scriptstyle v$ etex,z[1][1]);
dotlabel.top(btex $\scriptstyle w$ etex,z[2][1]);
dotlabel.bot(btex $\scriptstyle x$ etex,z[0][0]);
dotlabel.bot(btex $\scriptstyle y$ etex,z[1][0]);
dotlabel.bot(btex $\scriptstyle z$ etex,z[2][0]);

draw z[0][0]--z[2][0];
draw z[0][1]--z[2][1];
draw z[0][0]--z[1][1]--z[2][0];
draw z[2][1]--z[1][0]--z[0][1];

setbounds currentpicture to (-1,-1)*u--(3,-1)*u--(3,2)*u--(-1,2)*u--cycle;
endfig;

beginfig(3);
for j=0,1,2: for k=0,1: z[j][k]=(j,k)*u; endfor endfor
dotlabel.top(btex $\scriptstyle u$ etex,z[0][1]);
dotlabel.top(btex $\scriptstyle v$ etex,z[1][1]);
dotlabel.top(btex $\scriptstyle w$ etex,z[2][1]);
dotlabel.bot(btex $\scriptstyle x$ etex,z[0][0]);
dotlabel.bot(btex $\scriptstyle y$ etex,z[1][0]);
dotlabel.bot(btex $\scriptstyle z$ etex,z[2][0]);

draw z[0][0]--z[2][0];
draw z[0][1]--z[2][1];
draw z[0][0]--z[1][1]--z[2][0]--z[2][1]--z[1][0]--z[0][1]--cycle;
draw z[1][0]--z[1][1];

setbounds currentpicture to (-1,-1)*u--(3,-1)*u--(3,2)*u--(-1,2)*u--cycle;
endfig;

beginfig(4);
for j=0,1,2: for k=0,1: z[j][k]=(j,k)*u; endfor endfor
dotlabel.top(btex $\scriptstyle u$ etex,z[0][1]);
dotlabel.top(btex $\scriptstyle v$ etex,z[1][1]);
dotlabel.top(btex $\scriptstyle w$ etex,z[2][1]);
dotlabel.bot(btex $\scriptstyle x$ etex,z[0][0]);
dotlabel.bot(btex $\scriptstyle y$ etex,z[1][0]);
dotlabel.bot(btex $\scriptstyle z$ etex,z[2][0]);

draw z[0][0]--z[2][0];
draw z[0][1]--z[2][1];
draw z[0][0]--z[1][1]--z[2][0]--z[2][1]--z[1][0]--z[0][1]--cycle;
draw z[1][0]--z[1][1];
draw z[0][1]{left}..(-.4,1.4)*u..tension 2.3..(2.4,1.4)*u
        ..tension 1.5..{left}z[2][0];
draw z[0][0]{left}..(-.4,-.4)*u..tension 2.3..(2.4,-.4)*u
        ..tension 1.5..{left}z[2][1];

setbounds currentpicture to (-1,-1)*u--(3,-1)*u--(3,2)*u--(-1,2)*u--cycle;
endfig;

beginfig(5);
pair delx,dely,delz;
delx=(-40,-30);
dely=(+40,-30);
delz=(0,48);

z 1 0 0 = (0,0);
z 1 0 0 = z 0 0 0 + delx;
z 0 1 0 = z 0 0 0 + dely;
z 0 0 1 = z 0 0 0 + delz;
z 1 0 1 = z 1 0 0 + delz;

defaultfont:="cmr9";
dotlabel.urt("000",z 0 0 0);
dotlabel.lft("100",z 1 0 0);
dotlabel.lft("101",z 1 0 1);
dotlabel.top("001",z 0 0 1);
dotlabel.rt ("010",z 0 1 0);

% kludge to avoid dvips bug
% defaultfont:="cmr8";
% dotlabel.urt("000",z 0 0 0);
% dotlabel.lft("100 ",z 1 0 0);
% dotlabel.lft("101 ",z 1 0 1);
% dotlabel.top("001",z 0 0 1);
% dotlabel.rt ("010",z 0 1 0);

draw z 0 0 1 -- z 1 0 1 -- z 1 0 0 -- z 0 1 0 -- cycle;
draw z 1 0 1 -- z 0 1 0;
draw z 1 0 0 -- z 0 0 0 dashed evenly;
draw z 0 1 0 -- z 0 0 0 dashed evenly;
draw z 0 0 1 -- z 0 0 0 dashed evenly;

endfig;

end.

