
------------------< checking the lefschetz operator conjecture >---------------------






------------------< checking the lefschetz operator conjecture >---------------------
restart
load "Eur_ProjSpHF.m2"

--over Krasner
n = 3
ML = allMatroidsNoSym(n);
--ML = allMatroidsNoSym(n, makeHyperfield "Sign");
--ML = allMatroidsNoSym(n, makeHyperfield GF(3));
rks = ML/(i -> #i)
--ML = ML/(i -> select(i, m -> #(components m) == 1))
time PS = poset(flatten ML, isQuot) -- 8 secs when n = 5

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0/1}}}
L/rank
--Lam = {matrix{{0}}} | (drop(L,-1)/transpose)
H = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k)))

GL = globalOperator(L,1)
mapsByDeg(GL,rks,1) == L

GH = globalOperator(H,0)
mapsByDeg(GH,rks,0) == H

bracket(GH,GL) == 2*GL

time GLam = findLambda(GH,GL) -- 35 secs when n = 4 and over Krasner

bracket(GH,GLam) == -2* GLam
bracket(GL,GLam) == GH

Lam = mapsByDeg(GLam,rks,-1)

netList reverse Lam
netList reverse {0, Lam_1*(22/3), Lam_2*110, Lam_3*(22/3)} --for Krasner
netList reverse {0, Lam_1*(7/3), Lam_2*42, Lam_3*(7/3)} --for GF(2)
netList reverse {0, Lam_1*(10), Lam_2*90, Lam_3*(10)} --for Sign
netList reverse {0, Lam_1*(13/3), Lam_2*39, Lam_3*(13/3)} --for GF(3)




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
