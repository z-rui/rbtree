%prologues:=3;

pickup pencircle scaled .4pt;
defaultpen := savepen;

input boxes;

u := 10pt;
path triangle;
triangle := (0, 0) -- (-1u, -2u) -- (1u, -2u) -- cycle;

def cuta(expr p)(suffix a, b) =
	p cutbefore bpath a cutafter bpath b
enddef;

def singlerotcomm =
	Y.c - z1 = whatever*(Y.c-Z.c) xscaled -1;
	X.c - z2 = whatever*(X.c-Y.c) xscaled -1;
	y1 = ypart Z.n;
	y2 = ypart Y.n;
	z3 = Z.s;
	drawboxed(X, Y, Z);
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
	drawarrow (X.n shifted (0, 2u))--X.n;
	drawarrow cuta(X.c--Y.c, X, Y);
	drawarrow cuta(Y.c--Z.c, Y, Z);
	drawarrow X.c--z2 cutbefore bpath X;
	drawarrow Y.c--z1 cutbefore bpath Y;
enddef;

beginfig(1);
	circleit.X(btex $x\mathstrut$ etex);
	circleit.Y(btex $y\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	X.c - Y.c = (Y.c - Z.c) xscaled -1 = (2u, 3u);
	singlerotcomm;
endfig;

beginfig(2);
	circleit.X(btex $y\mathstrut$ etex);
	circleit.Y(btex $x\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	X.c - Y.c = (Y.c - Z.c) xscaled -1 = (-2u, 3u);
	singlerotcomm;
endfig;

def common = 
	circleit.X(btex $x\mathstrut$ etex);
	circleit.Y(btex $y\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	X.c - Z.c = (2u, 3u);
	Y.c - Z.c = (-3u, 2u);
	Y.c - z1 = (X.c - z2) xscaled -1 = whatever*(X.c - Z.c);
	y2 = ypart Z.n;
	z3 = Z.s;
	drawboxed(X, Y, Z);
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
	drawarrow cuta(X.c--Z.c, X, Z);
	drawarrow cuta(Y.c--Z.c, Y, Z) dashed evenly;
	drawarrow X.c--z2 cutbefore bpath X;
	drawarrow Y.c--z1 cutbefore bpath Y;
enddef;

beginfig(3);
	common;
	drawarrow (X.n shifted (0, 2u))--X.n;
endfig;

beginfig(4);
	common;
	drawarrow (Y.n shifted (0, 2u))--Y.n;
endfig;

def doublerotcomm(expr sign) = 
	X.c - Y.c = (Y.c - Z.c) xscaled -1 = (sign*2u, 3u);
	Y.c - z1 = Z.c - z3 = whatever*(X.c - Y.c);
	X.c - z2 = Z.c - z4 = whatever*(Y.c - Z.c);
	y1 = ypart Z.n;
	y2 = ypart Y.n;
	drawboxed(X, Y, Z);
	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label(btex$\alpha$etex, z[3] shifted (0, -4/3*u));
	label(btex$\beta$etex, z[4] shifted (0, -4/3*u));
	drawarrow (X.n shifted (0, 2u))--X.n;
	drawarrow cuta(X.c--Y.c, X, Y);
	drawarrow cuta(Y.c--Z.c, Y, Z);
	drawarrow X.c--z2 cutbefore bpath X;
	drawarrow Y.c--z1 cutbefore bpath Y;
	drawarrow Z.c--z3 cutbefore bpath Z;
	drawarrow Z.c--z4 cutbefore bpath Z;
enddef;

beginfig(5);
	circleit.X(btex $x\mathstrut$ etex);
	circleit.Y(btex $y\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	doublerotcomm(1);
endfig;

beginfig(6);
	circleit.X(btex $y\mathstrut$ etex);
	circleit.Y(btex $x\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	doublerotcomm(-1);
endfig;

beginfig(7);
	circleit.X(btex $x\mathstrut$ etex);
	circleit.Y(btex $y\mathstrut$ etex);
	circleit.Z(btex $z\mathstrut$ etex);
	z2 - z1 = z3 - z2 = z4 - z3 = (3u, 0);
	Y.c - z1 = X.c - z3 =
	(Y.c - z2) xscaled -1 = (X.c - z4) xscaled -1 = whatever*(2,3);
	Z.c - .5[Y.c,X.c] = (0, 3u);
	drawboxed(X, Y, Z);
	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label(btex$\alpha$etex, z[2] shifted (0, -4/3*u));
	label(btex$\beta$etex, z[3] shifted (0, -4/3*u));
	drawarrow (Z.n shifted (0, 2u))--Z.n;
	drawarrow cuta(Z.c--Y.c, Z, Y);
	drawarrow cuta(Z.c--X.c, Z, X);
	drawarrow Y.c--z1 cutbefore bpath Y;
	drawarrow Y.c--z2 cutbefore bpath Y;
	drawarrow X.c--z3 cutbefore bpath X;
	drawarrow X.c--z4 cutbefore bpath X;
endfig;

def inscommpre = 
	circleit.P(btex $P$ etex);
	circleit.S(btex $S$ etex);
	circleit.X(btex $X$ etex);
	circleit.Y(btex $Y$ etex);

	P.c - X.c = X.c - Y.c = (P.c - S.c) xscaled -1 = (2u, 3u);
	z1 = Y.s;
	X.c - z2 = whatever*(X.c-Y.c) xscaled -1; y2 = ypart Y.n;
	z3 = S.s;
enddef;	

def inscommpost =
	%label.top (btex link etex, P.n shifted (0, 2u));
	drawarrow (P.n shifted (0, 2u))--P.n;
	drawarrow cuta(P.c--X.c)(P, X);
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow cuta(X.c--Y.c)(X, Y);
	drawarrow X.c--z2 cutbefore bpath X;
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
enddef;

beginfig(8);
	inscommpre;
	drawboxed(P);
	pickup pencircle scaled 1pt;
	drawboxed(X, Y, S);
	pickup defaultpen;
	inscommpost;
endfig;

beginfig(9);
	inscommpre;
	pickup pencircle scaled 1pt;
	drawboxed(P, Y);
	pickup defaultpen;
	drawboxed(X, S);
	inscommpost;
endfig;

beginfig(10);
	inscommpre;
	pickup pencircle scaled 1pt;
	drawboxed(X, Y);
	pickup defaultpen;
	drawboxed(P, S);
	inscommpost;
endfig;

beginfig(11);
	circleit.X(btex $X$ etex);
	circleit.Y(btex $Y$ etex);
	circleit.P(btex $P$ etex);
	circleit.S(btex $S$ etex);
	X.c - P.c = P.c - S.c = (X.c - Y.c) xscaled -1 = (-2u,3u);
	pickup pencircle scaled 1pt;
	drawboxed(Y, P);
	pickup defaultpen;
	drawboxed(X, S);
	z1 = Y.s;
	P.c - z2 = whatever*(P.c-S.c) xscaled -1; y2 = ypart S.n;
	z3 = S.s;

	drawarrow (X.n shifted (0, 2u))--X.n;
	drawarrow cuta(X.c--P.c)(X, P);
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow cuta(X.c--Y.c)(X, Y);
	drawarrow P.c--z2 cutbefore bpath P;
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
endfig;

beginfig(12);
	circleit.P(btex $P$ etex);
	circleit.S(btex $S$ etex);
	circleit.X(btex $X$ etex);
	circleit.Y(btex $Y$ etex);

	P.c - X.c = (X.c - Y.c) xscaled -1 = (P.c - S.c) xscaled -1 = (2u, 3u);
	X.c-z1 = whatever*(X.c-Y.c) xscaled -1; y1 = ypart Y.n;
	Y.c-z2 = X.c-z1 = (Y.c-z3) xscaled -1;
	z4 = S.s;
	pickup pencircle scaled 1pt;
	drawboxed(X, Y);
	pickup defaultpen;
	drawboxed(P, S);
	drawarrow (P.n shifted (0, 2u))--P.n;
	drawarrow cuta(P.c--X.c)(P, X);
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow cuta(X.c--Y.c)(X, Y);
	drawarrow X.c--z1 cutbefore bpath X;
	drawarrow Y.c--z2 cutbefore bpath Y;
	drawarrow Y.c--z3 cutbefore bpath Y;
	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label (btex$\alpha$etex, (0,-4/3*u)shifted z2);
	label (btex$\beta$etex, (0,-4/3*u)shifted z3);
endfig;

beginfig(13);
	circleit.P(btex $P$ etex);
	circleit.S(btex $S$ etex);
	circleit.X(btex $X$ etex);
	circleit.Y(btex $Y$ etex);

	drawboxed(S); % tricky part -- must draw it first

	Y.c = .5[X.c,P.c] + (0, 3u);
	P.c-S.c = (-2u,3u);
	P.c-z3 = whatever*(P.c-S.c) xscaled -1; y3 = ypart S.n;
	X.c-z1 = (X.c-z2) xscaled -1 = whatever*(2,3);
	ypart X.c = ypart P.c;
	z3-z2=z2-z1;
	z4 = S.s;

	pickup pencircle scaled 1pt;
	drawboxed(X, P);
	pickup defaultpen;
	drawboxed(Y);
	drawarrow (Y.n shifted (0, 2u))--Y.n;
	drawarrow cuta(Y.c--X.c)(Y, X);
	drawarrow cuta(Y.c--P.c)(Y, P);
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow X.c--z1 cutbefore bpath X;
	drawarrow X.c--z2 cutbefore bpath X;
	drawarrow P.c--z3 cutbefore bpath P;
	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label (btex$\alpha$etex, (0,-4/3*u)shifted z2);
	label (btex$\beta$etex, (0,-4/3*u)shifted z3);
endfig;

def delcomm = 
	circleit.P(btex$P$etex);
	circleit.S(btex$S$etex);
	circleit.X(btex$X$etex);
	circleit.A(btex$A$etex);
	circleit.B(btex$B$etex);

	P.c-S.c = S.c-A.c = (2u, 3u);
	P.c-X.c = S.c-B.c = (-2u, 3u);

	drawunboxed(P,S,A,B);
	%forsuffixes s=P,S,A,B:
	%	draw bpath s dashed dashpattern(on 2 off 2);
	%endfor
	drawboxed(X);
	drawarrow (P.n shifted (0, 2u))--P.n;
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow cuta(P.c--X.c)(P, X);
	drawarrow cuta(S.c--A.c)(S, A);
	drawarrow cuta(S.c--B.c)(S, B);
	z1 = A.s;
	z2 = B.s;
	z3 = X.s;
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
enddef;

beginfig(14);
	delcomm;
endfig;

beginfig(15);
	delcomm;
	drawboxes(A,B,P);
	pickup pencircle scaled 1pt;
	drawboxes(S);
endfig;

beginfig(16);
	circleit.S(btex$S$etex);
	circleit.A(btex$A$etex);
	circleit.P(btex$P$etex);
	circleit.B(btex$B$etex);
	circleit.X(btex$X$etex);

	S.c-P.c = P.c-X.c = (-2u, 3u);
	S.c-A.c = P.c-B.c = (2u, 3u);

	pickup pencircle scaled 1pt;
	drawboxed(P);
	pickup defaultpen;
	drawboxed(S,A,B,X);
	z1 = A.s;
	z2 = B.s;
	z3 = X.s;
	drawarrow (S.n shifted (0, 2u))--S.n;
	drawarrow cuta(S.c--A.c)(S, A);
	drawarrow cuta(S.c--P.c)(S, P);
	drawarrow cuta(P.c--B.c)(P, B);
	drawarrow cuta(P.c--X.c)(P, X);
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
endfig;

beginfig(17);
	delcomm;
	drawboxes(S);
	draw bpath A withpen pencircle scaled 1pt;
endfig;

beginfig(18);
	circleit.S(btex$S$etex);
	circleit.A(btex$A$etex);
	circleit.P(btex$P$etex);
	circleit.B(btex$B$etex);
	circleit.X(btex$X$etex);

	S.c-P.c = P.c-X.c = (-2u, 3u);
	S.c-A.c = P.c-B.c = (2u, 3u);

	drawboxed(A,P,X);
	drawunboxed(S,B);
	z1 = A.s;
	z2 = B.s;
	z3 = X.s;
	drawarrow (S.n shifted (0, 2u))--S.n;
	drawarrow cuta(S.c--A.c)(S, A);
	drawarrow cuta(S.c--P.c)(S, P);
	drawarrow cuta(P.c--B.c)(P, B);
	drawarrow cuta(P.c--X.c)(P, X);
	for i = 1 upto 3:
		draw triangle shifted z[i];
	endfor
endfig;

beginfig(19);
	circleit.P(btex$P$etex);
	circleit.S(btex$S$etex);
	circleit.X(btex$X$etex);
	circleit.A(btex$A$etex);
	circleit.B(btex$B$etex);

	P.c-S.c = S.c-A.c = (2u, 3u);
	P.c-X.c = S.c-B.c = (-2u, 3u);

	drawunboxed(P,B);
	draw bpath B withpen pencircle scaled 1pt;
	drawboxed(X,A,S);
	drawarrow (P.n shifted (0, 2u))--P.n;
	drawarrow cuta(P.c--S.c)(P, S);
	drawarrow cuta(P.c--X.c)(P, X);
	drawarrow cuta(S.c--A.c)(S, A);
	drawarrow cuta(S.c--B.c)(S, B);
	z1 = A.s;
	z2 = X.s;
	B.c - z3 = (B.c - z4) xscaled -1 = whatever*(2,3);
	y1-y3 = 2u;
	drawarrow B.c--z3 cutbefore bpath.B;
	drawarrow B.c--z4 cutbefore bpath.B;
	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label (btex$\alpha$etex, z3 shifted(0, -4/3*u));
	label (btex$\beta$etex, z4 shifted(0, -4/3*u));
endfig;

beginfig(20);
	circleit.B(btex$B$etex);
	circleit.S(btex$S$etex);
	circleit.P(btex$P$etex);
	circleit.A(btex$A$etex);
	circleit.X(btex$X$etex);

	z1 = A.s;
	z4 = X.s;
	x2-x1 = x3-x2 = x4-x3 = 3u;
	y1=y4; y2=ypart A.n; y3=ypart X.n;

	xpart S.c = .5[x1,x2];
	xpart P.c = .5[x3,x4];
	ypart S.c = ypart P.c = ypart A.c + 3u;
	B.c = .5[S.c,P.c] shifted (0, 3u);

	drawboxed(S,P,A,X);
	drawunboxed(B);

	drawarrow (B.n shifted (0,2u))--B.n;
	drawarrow cuta(B.c--S.c)(B,S);
	drawarrow cuta(B.c--P.c)(B,P);
	drawarrow cuta(S.c--A.c)(S,A);
	drawarrow cuta(P.c--X.c)(P,X);
	drawarrow S.c--z2 cutbefore bpath.S;
	drawarrow P.c--z3 cutbefore bpath.P;

	for i = 1 upto 4:
		draw triangle shifted z[i];
	endfor
	label (btex$\alpha$etex, z2 shifted(0, -4/3*u));
	label (btex$\beta$etex, z3 shifted(0, -4/3*u));
endfig;

beginfig(21);
	delcomm;
	drawboxes(S,A,B);
	draw bpath.P withpen pencircle scaled 1pt;
endfig;

beginfig(22);
	delcomm;
	drawboxes(A,B,P);
	draw bpath.S withpen pencircle scaled 1pt;
endfig;

beginfig(23);
	delcomm;
	drawboxes(S,A,B,P);
endfig;
end
