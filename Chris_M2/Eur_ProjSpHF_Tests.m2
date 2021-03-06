
----------------------------------< matroid homology >------------------------------------
restart
load "Eur_ProjSpHF.m2"

n = 3
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)

M = uniformMatroid(2,3)

--given a matroid m and an index i, contracts by i and adds it back as a loop
myContract = (m,i) -> (
    B := (select(bases m, b -> member(i,b)))/elements/(b -> delete(i,b));
    matroid(elements m.groundSet, B)
    )

--given a matroid m
delC = (m,ml) -> (
    r := rank m;
    nonL := sort elements (m.groundSet - set loops m);
    hashTable (plus, apply(#nonL, i -> (
	    mc := myContract(m,nonL_i);
	    (position(ml_(r-1), j -> j == myContract(m,nonL_i)),(-1/1)^i)
	    )
	))
    )

matroidComplex = method()
matroidComplex(ZZ) := n -> (
    ML := allMatroidsNoSym(n);
    rks := ML/(i -> #i);
    E := elements ((first first ML).groundSet);
    mats := apply(n, k -> transpose matrix apply(rks_(k+1), i -> (
		M := (ML_(k+1))_i;
		DC := delC(M,ML);
		apply(rks_k, j -> (
			if member(j,keys DC) then DC#j
			else 0
			)
		    )
		)
	    )
	);
    chainComplex mats
    )

C = matroidComplex 3
C.dd^2



----------------------------------< shellability >------------------------------------
restart
load "Eur_ProjSpHF.m2"
needsPackage "SimplicialDecomposability"

n = 3
--ML = allMatroidsNoSym(n,makeHyperfield("Sign"));
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)
time P = poset(flatten ML, isQuot);
OC = orderComplex P;
--time isShellable OC --VERY SLOW
betti res dual monomialIdeal OC



------------------------------< principal truncations >-------------------------------
restart
load "Eur_ProjSpHF.m2"

--n = 6 case
n = 6
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)

princLef = r -> (
    princs := hashTable apply(ML_r, m -> (m, select(apply(ML_1, u -> u + m), i -> rank i == r+1)));
    sub(matrix apply(ML_(r+1), i -> apply(ML_r, j -> #select(princs#j, k -> k == i))),QQ)
    )

time PL = apply(n, i -> princLef i) | {matrix{{0/1}}}; --1500 seconds!
PL;
PL/rank --not full rank!
rank (PL_3*PL_2)
rank (PL_3*PL_2*PL_1)
rank (PL_4*PL_3*PL_2*PL_1*PL_0)
rks

--fl = openOutAppend "princLef_nEquals6"
--fl << toExternalString PL << close

fl = openIn "princLef_nEquals6"
PLL  = value get fl;
PLL/rank


--n = 4 case
n = 5
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)

princLef = r -> (
    princs := hashTable apply(ML_r, m -> (m, select(apply(ML_1, u -> u + m), i -> rank i == r+1)));
    sub(matrix apply(ML_(r+1), i -> apply(ML_r, j -> #select(princs#j, k -> k == i))),QQ)
    )

princLef2 = r -> (
    princs := hashTable apply(ML_r, m -> (m, select(apply(ML_1, u -> u + m), i -> rank i == r+1)));
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if #select(princs#j, k -> k == i) > 0 then 1/1 else 0))
    )

time PL = apply(n, i -> princLef2 i) | {matrix{{0/1}}};
PL/rank

--fake Lambda
Lam = {matrix{{0}}} | (drop(PL,-1)/transpose)

LbracketLam = i -> (
    if i == 0 then - Lam_(i+1) * PL_i
    else if i == n then PL_(i-1) * Lam_i
    else PL_(i-1) * Lam_i - Lam_(i+1) * PL_i
    )

LbracketLam 0
LbracketLam 1
LbracketLam 2
LbracketLam 3

--real Lambda
H = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k)))
GL = globalOperator(PL,1)
mapsByDeg(GL,rks,1) == PL

GH = globalOperator(H,0)
mapsByDeg(GH,rks,0) == H

bracket(GH,GL) == 2*GL

time GLam = findLambda(GH,GL)

bracket(GH,GLam) == -2* GLam
bracket(GL,GLam) == GH

Lam = mapsByDeg(GLam,rks,-1)

netList reverse Lam


------------------------------< regular matroids >-------------------------------
restart
load "Eur_ProjSpHF.m2"

F2 = makeHyperfield GF(2)
F3 = makeHyperfield GF(3)

to2 = m -> (
    mat := m.matroid;
    H := hashTable apply(keys m.Fbases, i -> (i, if (m.Fbases)#i == 0 then 0 else 1));
    makeFMatroid(mat,F2,H)
    )

--sanity checks
--ML = allMatroidsNoSym(4,makeHyperfield(GF(3)))
--ML_2/to2/isWellDefined

regularMatroids = n -> (
    ML := allMatroidsNoSym(n, F3);
    apply(ML, l -> select(l, m -> isWellDefined to2 m))
    )

isRegQuot = (m,n,L) -> (
    isQuot(m,n,L) and isQuot(to2 m, to2 n, L)
    )


n = 4
ML = allMatroidsNoSym(n, F3);
ML/(l -> #l)
time RML = regularMatroids n;
rks = RML/(l -> #l)
time P = poset(flatten RML, (a,b) -> isRegQuot(a,b,singleIncidences(rank a, rank b, n)));
--displayPoset P
isLattice P


Lef = r -> (
    L := singleIncidences(r,r+1,n);
    matrix apply(RML_(r+1), i -> apply(RML_r, j -> if isRegQuot(j,i,L) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0/1}}}
L/rank
--fake Lambda
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

--real Lambda
GL = globalOperator(L,1)
mapsByDeg(GL,rks,1) == L

GH = globalOperator(H,0)
mapsByDeg(GH,rks,0) == H

bracket(GH,GL) == 2*GL

time GLam = findLambda(GH,GL)

bracket(GH,GLam) == -2* GLam
bracket(GL,GLam) == GH

Lam = mapsByDeg(GLam,rks,-1)

netList reverse Lam


---------------< valuative relations become primitive elements? >-------------------
restart
load "Eur_ProjSpHF.m2"

--n = 4 case
n = 4
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0/1}}};
L/rank

ker L_2 --can see the three valuative relations


--n = 5 case
n = 5
ML = allMatroidsNoSym(n);
rks = ML/(i -> #i)

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0/1}}};
L/rank

Lsq = L_3*L_2
--ker Lsq
flatten entries (gens ker Lsq)_0, i -> i != 0 
positions(flatten entries (gens ker Lsq)_0, i -> i != 0 )
rel = (ML_2)_oo
netList (rel/nonbases)

positions(ML_2, m -> rank(m,set{0}) == 0 and #(bases m) == 6 )
bases (ML_2)_26
bases (ML_2)_81
bases (ML_2)_51
bases (ML_2)_56
I = id_(QQ^171);
v = I_26 + I_81 - I_51 - I_56
Lsq * v




----------------------< Poincare pairing computations >--------------------------
restart
load "Eur_ProjSpHF.m2"

n = 4;
ML = allMatroidsNoSym n;
rks = ML/(i -> #i)

r=2
pair1 = matrix apply(ML_r, i -> apply(ML_(n-r), j -> (
	    Bi := bases i;
	    Bj := bases j;
	    if any((Bi ** Bj)/product, s -> s === set {}) then 1/1 else 0)
	)
    )

pair2 = matrix apply(ML_2, i -> apply(ML_2, j -> (
	    Bi := bases i;
	    Bj := bases j;
	    (#select((Bi ** Bj)/product, s -> s === set {}))/1
	    )
	)
    )
pair3 = matrix apply(ML_r, i -> apply(ML_(n-r), j -> (
	    Fi := delete(i.groundSet, flats i);
	    Fj := delete(j.groundSet, flats j);
	    joined := Fi | Fj;
	    if #(unique joined) == #joined then 1/1 else 0
	    )
	)
    )
pair4 = matrix apply(ML_2, i -> apply(ML_2, j -> (
	    Fi := flats i;
	    Fj := flats j;
	    if #(unique ((Fi ** Fj)/product)) == 2^n then 1/1 else 0
	    )
	)
    )

boxSum = (S,T) -> (
    symDiff := (S + T) - (S * T);
    apply(subsets (S*T), i -> i + symDiff)
    )

pair5 = matrix apply(ML_2, i -> apply(ML_2, j -> (
	    E := i.groundSet;
	    Fi := (flats i)/(f -> E - f);
	    Fj := (flats j)/(f -> E - f);
	    if #(unique flatten ((Fi ** Fj)/(k -> boxSum toSequence k))) == 2^n then 1/1 else 0
	    --if #(unique ((Fi ** Fj)/product)) == 2^n then 1/1 else 0
	    )
	)
    )

rank pair3

signCount = L -> tally apply(L, i -> (
	if abs(i) < 10^(-10) then "0"
	else if i < 0 then "-"
	else "+"
	)
    )

sort toList eigenvalues pair3
sort toList eigenvalues pair1
signCount toList eigenvalues pair3
signCount toList eigenvalues pair1
signCount toList eigenvalues pair2

gens ker pair1 == gens ker pair3

signCount toList eigenvalues pair5

gens ker pair1, gens ker pair3, gens ker pair5

------------------< checking the lefschetz operator conjecture >---------------------
restart
load "Eur_ProjSpHF.m2"

--over Krasner
n = 4
ML = allMatroidsNoSym(n);
ML = allMatroidsNoSym(n, makeHyperfield "Sign");
ML = allMatroidsNoSym(n, makeHyperfield GF(2));
rks = ML/(i -> #i)
--ML = ML/(i -> select(i, m -> #(components m) == 1))
time PS = poset(flatten ML, isQuot); -- 8 secs when n = 5
isLattice PS

Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    )

time L = apply(n, i -> Lef i) | {matrix{{0/1}}}
L/(l -> (transpose l) * l)
oo_1
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


--valuative relations become primitive elements?
Lsq = L_3*L_2
positions(ML_2, m -> rank(m,set{0}) == 0 and #(bases m) == 6 )
bases (ML_2)_26
bases (ML_2)_81
bases (ML_2)_51
bases (ML_2)_56
I = id_(QQ^171);
v = I_26 + I_81 - I_51 - I_56
Lsq * v

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
