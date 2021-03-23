
------------------< checking the lefschetz operator conjecture >---------------------
restart
load "Eur_ProjSpHF.m2"

--over Krasner
n = 3
ML = allMatroidsNoSym(n);
ML/(i -> #i)
time PS = poset(flatten ML, isQuot) -- 8 secs when n = 5

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0}}}
L/rank
--Lam = {matrix{{0}}} | (drop(L,-1)/transpose)
Lam = reverse L
Hcand = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k)))

--making the global Lefschetz operator
globalLef = method()
--given a list L of matrices, representing the "raising operators" for each degree,
--outputs a matrix representing the operator on the whole space
globalLef(List) := Matrix => L -> (
    --not yet implemented
    )
zeroMat = (m,n) -> matrix apply(m, i -> apply(n, j -> 0/1))

a = symbol a;
b = symbol b;
R = QQ[flatten apply(7, i -> apply(7, j -> a_(i,j))) | flatten apply(7, i -> apply(7, j -> b_(i,j)))]
R_49
H1 = transpose genericMatrix(R,7,7)
H2 = transpose genericMatrix(R,R_49,7,7)	
(H1 * (transpose matrix{{1,1,1,1,1,1,1}}) + (transpose matrix{{1,1,1,1,1,1,1}}))
eq1 = flatten entries oo
(matrix {{1,1,1,1,1,1,1}} * H2) - matrix{{1,1,1,1,1,1,1}}
eq2 = flatten entries oo
H2 * L_1 - L_1 * H1 - 2* L_1
eq3 = flatten entries oo
I = ideal(eq1 | eq2 | eq3)
I = ideal mingens I
J = I + ideal apply(gens ring prune I, i -> sub(i,R))
J = ideal mingens J
J_*

--finding H matrix assuming symmetric
a = symbol a;
b = symbol b;
R = QQ[ apply(28, i -> a_i) | apply(28, i -> b_i)]
R_28
H1 = transpose genericSymmetricMatrix(R,7)
H2 = transpose genericSymmetricMatrix(R,R_28,7)	
(H1 * (transpose matrix{{1,1,1,1,1,1,1}}) + (transpose matrix{{1,1,1,1,1,1,1}}))
eq1 = flatten entries oo
(matrix {{1,1,1,1,1,1,1}} * H2) - matrix{{1,1,1,1,1,1,1}}
eq2 = flatten entries oo
H2 * L_1 - L_1 * H1 - 2* L_1
eq3 = flatten entries oo
I = ideal(eq1 | eq2 | eq3)
I = ideal mingens I
J = I + ideal apply(gens ring prune I, i -> sub(i,R))
J = ideal mingens J
subs = apply(J_*, f -> (
	if #terms f == 1 then first terms f => 0
	else if #terms f == 2 then first terms f => last terms f
	else error "not one or two terms"
	)
    )
sub(H1,subs)
sub(H2,subs)

H = {matrix{{-1}}, sub(H1,subs), sub(H2,subs), matrix{{1}}}

--Lie bracket if A is raising and B is lowering
bracketRL = (A,B,i) -> (
    if i == 0 then - B_(i+1) * A_i
    else if i == n then A_(i-1) * B_i
    else A_(i-1) * B_i - B_(i+1) * A_i
    )

--Lie bracket if A neither raises nor lowers, and B lowers
bracketNL = (A,B,i) -> (
    if i == 0 then - B_i * A_i
    else A_(i-1) * B_i - B_i * A_i
    )

--Lie bracket if A neither raises nor lowers, and B raises
bracketNR = (A,B,i) -> (
    if i == n then - B_i * A_i
    else A_(i+1) * B_i - B_(i) * A_i
    )

apply(n+1, i -> bracketNR(H,L,i))
L



--this naive one didn't work but for record
H = apply(n+1, i -> bracketRL(L,Lam,i))
apply(n+1, i -> bracketNR(H,L,i))
L
apply(n+1, i -> bracketNL(H,Lam,i))
Lam

apply(n+1, i -> bracketNR(Hcand,L,i))
L
apply(n+1, i -> bracketNL(Hcand,Lam,i))
Lam






n = 3
ML = allMatroidsNoSym(n, makeHyperfield GF(2));
ML/(i -> #i)
time PS = poset(flatten ML, isQuot) -- 8 secs when n = 5

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0}}}
L/rank
Lam = {matrix{{0}}} | (drop(L,-1)/transpose)
H = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k)))

LbracketLam = i -> (
    if i == 0 then - Lam_(i+1) * L_i
    else if i == n then L_(i-1) * Lam_i
    else L_(i-1) * Lam_i - Lam_(i+1) * L_i
    )

LbracketLam 0
LbracketLam 1
LbracketLam 2
LbracketLam 3


n = 3
ML = allMatroidsNoSym(n, makeHyperfield "Sign");
ML/(i -> #i)
time PS = poset(flatten ML, isQuot) -- 8 secs when n = 5

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0}}}
L/rank
Lam = {matrix{{0}}} | (drop(L,-1)/transpose)
H = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k)))

LbracketLam = i -> (
    if i == 0 then - Lam_(i+1) * L_i
    else if i == n then L_(i-1) * Lam_i
    else L_(i-1) * Lam_i - Lam_(i+1) * L_i
    )

LbracketLam 0
LbracketLam 1
LbracketLam 2
LbracketLam 3

--------------------------------< bunch of tests >-------------------------------


--Hyperfield tests
restart
load "Eur_ProjSpHF.m2"
F = GF(8)
HF = makeHyperfield(F)
HF.sum({0,1})
HF.sum({0,1,4})
HF.product({1,4})
minusHF = minusOf(HF)
minusHF 4

K = makeHyperfield "Krasner"
minusK = minusOf K
minusK 1
minusK 0

S = makeHyperfield "Sign"
minusS = minusOf S
minusS 1
S.sum {0,1,1}
S.sum {0,1,-1}

--FMatroid tests
restart
load "Eur_ProjSpHF.m2"
F = GF(2)
A = sub(transpose matrix drop(toList({0,0,0}..{1,1,1}),1),F)
FM = makeFMatroid(A)
peek FM
dual FM
peek oo


L = threeTermRels(3,7);
isWellDefined(FM,L)
isWellDefined(FM)

M = uniformMatroid(2,4)
F = makeHyperfield(GF(2))
FM = makeFMatroid(M,F, hashTable apply(bases M, b -> (sort elements b, F.one)))
isWellDefined(FM) --should be false because Uniform(2,4) is not realizable over GF(2)
lifts(M,F) --no realization over GF(2)
ML = lifts(M,makeHyperfield(GF(3))) --but 8 many over GF(3)
oo/dual/(m -> m.Fbases)
ML/(m-> m.Fbases)
S = makeHyperfield "Sign"
lifts(M,S) --and 24 many over signed hyperfield
#oo
--note that 24 + 8 = 2^5, noting that plucker condition for GF(3) and S are exactly complementary

M = uniformMatroid(1,3)
F = makeHyperfield "Sign"
lifts(M,F)



--allMatroidsNoSym tests
restart
load "Eur_ProjSpHF.m2"

ML3 = flatten allMatroidsNoSym 3
--truncML3 = drop(drop(ML3,1),-1)
P = poset(ML3, isQuot);
displayPoset P
ML3Rk = apply(4, i -> select(ML3, m -> rank m == i))

ML4 = flatten allMatroidsNoSym 4;
apply(5, i -> #(select(ML4, m -> rank m == i)))
P = poset(ML4, isQuot);
displayPoset P

time ML5 = flatten allMatroidsNoSym 5;
apply(6, i -> #(select(ML5, m -> rank m == i)))
time P = poset(ML5, isQuot); --7.5 sec
displayPoset P --not helpful


time ML6 = flatten allMatroidsNoSym 6; --10 secs
apply(7, i -> #(select(ML6, m -> rank m == i)))


--Lefschetz operators over Krasner
n = 5
ML = allMatroidsNoSym n;
MLR = apply(n+1, i -> select(ML, m -> rank m == i));
MLR/(l -> #l)

Lef = r -> (
    matrix apply(MLR_(r+1), i -> apply(MLR_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

L = apply(n, i -> Lef i);
L/rank
rank (L_3*L_2*L_1)
rank (L_2)


n = 6
ML = allMatroidsNoSym n; --12 secs
MLR = apply(n+1, i -> select(ML, m -> rank m == i));
MLR/(l -> #l)

Lef = r -> (
    matrix apply(MLR_(r+1), i -> apply(MLR_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

L = apply(n, i -> Lef i); --30 secs
L/rank
rank (L_4*L_3*L_2*L_1)
rank (L_3*L_2)



--allMatroids over F tests
restart
load "Eur_ProjSpHF.m2"

--sanity check over Kranser
K = makeHyperfield "Krasner"
n = 3
ML = allMatroidsNoSym n
MLK = allMatroidsNoSym(n,K)
ML/(i -> #i)
MLK/(i -> #i)
P = poset(flatten ML, isQuot)
PK = poset(flatten MLK, isQuot)
P == PK
ML2 = allMatroidsNoSym(n, makeHyperfield GF(2))
P2 = poset(flatten ML2, isQuot)
displayPoset P2
displayPoset PK

--oriented matroids
S = makeHyperfield "Sign"
n = 3
time ML = allMatroidsNoSym(n,S); --6 secs when n = 5
ML/(i -> #i)
time PS = poset(flatten ML, isQuot) -- 50 secs when n = 4
displayPoset PS
ML3 = allMatroidsNoSym(n, makeHyperfield GF(3))
P3 = poset(flatten ML3, isQuot)
displayPoset P3

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i); --50 secs when n = 4
L/reducedRowEchelonForm
L/rank
A = (L_2*L_1)
A == transpose A
eigenvalues A
