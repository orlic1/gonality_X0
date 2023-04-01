// This file proves (parts of )Propostitions 4.8., 4.14 and 4.17 checking whether certain quotients of X_0(N) are trigonal over Q or not. 
load "new_models.m";

//Now we prove Proposition 4.8 by checking that the trigonal maps are defined over Q 
X, ws, pairs:=eqs_quos(135,[[135]]);
Genus4GonalMap(pairs[1,1]);
X:=ModularCurveQuotient(215,[215]);
Genus4GonalMap(X);


//Now we prove Proposition 4.14 by explicitly constructing degree 3 functions 

X, ws, pairs:=eqs_quos(84,[[84]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(84) is trigonal over Q

X, ws, pairs:=eqs_quos(93,[[93]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(93) is trigonal over Q

X, ws, pairs:=eqs_quos(115,[[115]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(115) is trigonal over Q

X, ws, pairs:=eqs_quos(116,[[116]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(116) is trigonal over Q

X, ws, pairs:=eqs_quos(129,[[129]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(129) is trigonal over Q

X, ws, pairs:=eqs_quos(137,[[137]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(137) is trigonal over Q

X, ws, pairs:=eqs_quos(155,[[155]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(155) is trigonal over Q

X, ws, pairs:=eqs_quos(159,[[159]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// this proves that X_0^+(159) is trigonal over Q

// Now we prove Propostion 4.17, by showing that quotients of X_0(N) are not trigonal by showing that there are no degree 3 functions over F_p, where p is a prime of good reduction.

X, ws, pairs:=eqs_quos(110,[[55]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(7));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2; 
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(145,[[29]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(11));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2; 
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(161,[[161]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(5));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2; 
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(173,[[173]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(5));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2; 
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(177,[[59]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(5));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2; 
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(188,[[47]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(3));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2;
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(199,[[199]]);
Xw:=pairs[1,1];
D:=DefiningEquations(Xw);
D2:=[];
for i:=1 to #D do
p:=D[i];
l:=LCM([Denominator(a):a in Coefficients(p)]);
p:=p*l;
D2:=D2 cat [p];
end for;
C:=Scheme(ProjectiveSpace(Rationals(),Genus(Xw)-1),D2);
C2:=ChangeRing(C,GF(5));
FF := FunctionField(C2);
AFF := AlgorithmicFunctionField(FF);
pls1:=Places(AFF,1);
pls2:=Places(AFF,2);
#pls1,#pls2;
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 
