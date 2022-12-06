
  1
  2
  3
  4
  5
  6
  7
  8
  9
 10
 11
 12
 13
 14
 15
 16
 17
 18
 19
 20
 21
 22
 23
 24
 25
 26
 27
 28
 29
 30
 31
 32
 33
 34
 35
 36
 37
 38
 39
 40
 41
 42
 43
 44
 45
 46
 47
 48
 49
 50
 51
 52
 53
 54
 55
 56
 57
 58
 59
 60
 61
 62
 63
 64
 65
 66
 67
 68
 69
 70
 71
 72
 73
 74
 75
 76
 77
 78
 79
 80
 81
 82
 83
 84
 85
 86
 87
 88
 89
 90
 91
 92
 93
 94
 95
 96
 97
 98
 99
100
101
102
103
104
105
106
107
108
109
110
111
112
113
114
115
116
117
118
119
120
121
122
123
124
125
126
127
128
129
130
131
132
133
134
135
136
137
138
139
140
141
142
143
144
145
146
147
148
149
150
151
152
153
154
155
156
157
158
159
160
161
162
163
164
165
166
167
168
169
170
171
172
173
174
175
176
177
178
179
180
181
182
183
184
185
186
187
188
189
190
191
192
193
194
195
196
197
198
199
200
201
202
203
204
205
206
207
208
209
210
211
212
213
214
215
216
217
218
219
220
221
222
223
224
225
226
227
228
229
230
231
232
233
234
235
236
237
238
239
240
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
