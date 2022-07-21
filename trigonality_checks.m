// This file proves Propostitions 4.14 and 4.16 checking whether certain quotients of X_0(N) are trigonal over Q or not. 
load "new_models.m";

//First we prove Proposition 4.14 by explicitly constructing degree 3 functions 

X, ws, pairs:=eqs_quos(84,[[84]]);
Xw:=pairs[1,1];
pts:=PointSearch(Xw,20);
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
is_trigonal(pairs[1,1]);
//returns true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(129) is trigonal over Q

X, ws, pairs:=eqs_quos(137,[[137]]);
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(137) is trigonal over Q

X, ws, pairs:=eqs_quos(155,[[155]]);
pts:=PointSearch(Xw,20);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//this proves that X_0^+(155) is trigonal over Q

X, ws, pairs:=eqs_quos(159,[[159]]);
is_trigonal(pairs[1,1]);
//true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// this proves that X_0^+(159) is trigonal over Q

// Now we prove Propostion 4.16, by showing that quotients of X_0(N) are not trigonal by showing that there are no degree 3 functions over F_p, where p is a prime of good reduction.

X, ws, pairs:=eqs_quos(145,[[29]]);
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
//does not find any functions
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
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// fails
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
is_trigonal(pairs[1,1]);
//true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// fails
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
is_trigonal(pairs[1,1]);
//true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// fails
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
is_trigonal(pairs[1,1]);
//true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// fails
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
#pls1,#pls2; // 3 12
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
//returns 1 in all cases, proving that the quotient is not trigonal 

X, ws, pairs:=eqs_quos(199,[[199]]);
is_trigonal(pairs[1,1]);
//true
Xw:=pairs[1,1];
pts:=PointSearch(Xw,100);
plcs:=[Place(p): p in pts];
assert Maximum([Dimension(RiemannRochSpace(p+q+r)):p,q,r in plcs]) eq 2;
// fails
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
#pls1,#pls2; // 6 11
pls:=Places(AFF,3);
Max({Dimension(RiemannRochSpace(p)):p in Places(AFF,3)});
Max({Dimension(RiemannRochSpace(p+q)):p in pls1, q in pls2});
Max({Dimension(RiemannRochSpace(p+q+u)):p,q,u in pls1});
//returns 1 in all cases, proving that the quotient is not trigonal 
