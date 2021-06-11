
------------------< Lefschetz property for ordinary matroids (Krasner) >---------------------
restart
load "Eur_ProjSpHF.m2"

n = 3; --ground set has size n = 3
ML = allMatroidsNoSym(n); --all matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}} --the matrices for the candidate "Lefschetz operator"
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)) -- matrices of compositions L_i * ... * L_(n-1-i) 
--these square matrices are symmetric when n is odd since ML lists by lower rank matroids then takes dual
Lcomp/eigenvalues/signCount
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full
H = apply(n+1, k -> (2*k - n) * id_(QQ^(#ML_k))) -- the "H matrix" of the SL2 representation by H,X,Y
GL = globalOperator(L,1);
GH = globalOperator(H,0);
time GLam = findLambda(GH,GL);-- 35 secs when n = 4 and over Krasner
Lam = mapsByDeg(GLam,rks,-1) --the Lambda (lowering operator, where the L is the raising operator)
bracket(GH,GLam) == -2* GLam --check SL2 rep properties
bracket(GL,GLam) == GH

n = 4; --ground set has size n = 4
ML = allMatroidsNoSym(n); --all matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}} --the matrices for the candidate "Lefschetz operator"
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)) -- matrices of compositions L_i * ... * L_(n-1-i) 
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full

n = 5; --ground set has size n = 5
ML = allMatroidsNoSym(n); --all matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}}; --the matrices for the candidate "Lefschetz operator"
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)); -- matrices of compositions L_i * ... * L_(n-1-i) 
--these square matrices are symmetric when n is odd since ML lists by lower rank matroids then takes dual
Lcomp/eigenvalues/signCount
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full

n = 6; --ground set has size n = 6
ML = allMatroidsNoSym(n); --all matroids on n elements (10 secs when n = 6)
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}}; --the matrices for the candidate "Lefschetz operator" (60 secs when n = 6)
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)); -- matrices of compositions L_i * ... * L_(n-1-i) 
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full


------------------< Lefschetz property for oriented matroids >---------------------
restart
load "Eur_ProjSpHF.m2"

n = 3; --ground set has size n = 3
ML = allMatroidsNoSym(n, makeHyperfield "Sign"); --all oriented matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}} --the matrices for the candidate "Lefschetz operator"
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)) -- matrices of compositions L_i * ... * L_(n-1-i) 
--these square matrices are symmetric when n is odd since ML lists by lower rank matroids then takes dual
Lcomp/eigenvalues/signCount
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full

n = 4; --ground set has size n = 4
ML = allMatroidsNoSym(n, makeHyperfield "Sign"); --all oriented matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}}; --the matrices for the candidate "Lefschetz operator" (50 secs when n = 4)
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)); -- matrices of compositions L_i * ... * L_(n-1-i) 
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full

-*-- n = 5 case: don't run "Lef" on personal laptops (unless not using it for some time...)
n = 5; --ground set has size n = 5
ML = allMatroidsNoSym(n, makeHyperfield "Sign"); --all oriented matroids on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}} --the matrices for the candidate "Lefschetz operator"
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)) -- matrices of compositions L_i * ... * L_(n-1-i) 
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full
-----------*-


------------------< Lefschetz property for matroids over finite fields >---------------------
restart
load "Eur_ProjSpHF.m2"

n = 4; --ground set has size n = 4
ML = allMatroidsNoSym(n, makeHyperfield GF(2)); --all matroids over F2 on n elements 
rks = ML/(i -> #i) -- number of matroids for each rank
Lef = r -> (
    matrix apply(ML_(r+1), i -> apply(ML_r, j -> if isQuot(j,i) then 1/1 else 0))
    );
L = apply(n, i -> Lef i) | {matrix{{0/1}}}; --the matrices for the candidate "Lefschetz operator" (50 secs when n = 4)
Lcomp = apply((n+1)//2, i -> product reverse apply(toList(i..(n-1-i)), j -> L_j)); -- matrices of compositions L_i * ... * L_(n-1-i) 
Lrks = Lcomp/rank --the ranks of the square matrices
Lrks == apply((n+1)//2, i -> rks_i)--check that the ranks are full
