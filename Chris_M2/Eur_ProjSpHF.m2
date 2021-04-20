-*----------------------------------------------------------------------------------
Codes for Projective Spaces over Hyperfields

Author: Christopher Eur
----------------------------------------------------------------------------------*-



------------------------------------< Hyperrings >----------------------------------------

--given a (finite) GaloisField outputs a list of all its elements
elements(GaloisField) := F -> (
    p := char F;
    v := first gens F;
    d := degree ideal ambient F;
    apply(toList((d:0)..(d:p-1)), s -> sum(d, i -> s_i * v^i))
    )

--Hyperfield is an immutable hash table with keys:
--elements => a List of elements in the hyperring (should be finite)
--zero => a Thing, the identity element under hyperaddition
--one => a Thing, the identity element under multiplication
--sum => a FunctionClsoure whose input is a list of elements and output is the hyper-sum
--product => a FunctionClsoure whose input is a list of elements and output is the product


Hyperfield = new Type of HashTable
Hyperfield.synonym = "hyperfield"

globalAssignment Hyperfield
net Hyperfield := HF -> net ofClass class HF | " on elements " | toString(HF.elements)



makeHyperfield = method()

--input: a list L whose elements are
--(L_0 = zero, L_1 = one, and L_2 = a List of elements of the hyperfield)
--s: a FunctionClosure for the hypersum
--p: a FunctionClosure for the product
--output: a hyperring with appropriate assignments
makeHyperfield(List, FunctionClosure, FunctionClosure) := Hyperfield => (L, s, p) -> (
    H := new Hyperfield from {
	symbol elements => L_2,
	symbol zero => L_0,
	symbol one => L_1,
	symbol sum => s,
	symbol product => p,
	cache => new CacheTable
	};
    H
    )

--computes the hypersum-minus and caches it as a FunctionClosure
minusOf = method()
minusOf(Hyperfield) := FunctionClosure => F -> (
    if not F.cache.?minusOf then (
	m := hashTable apply(F.elements, i -> (
		invs := select(F.elements, j -> member(F.zero, F.sum({i,j})));
		if #invs != 1 then (
		    error "hyper-additive inverses not well-defined!"
		    );
		(i, first invs)
		)
	    );
	F.cache.minusOf = i -> m#i;
	);
    F.cache.minusOf
    )

--makes Hyperfield from a GaloisField R
makeHyperfield(GaloisField) := Hyperfield => R -> (
    L := {0_R, 1_R, elements R};
    s := l -> unique {sum(l/(i -> sub(i,R)))};
    p := l -> product(l/(i -> sub(i,R)));
    F := makeHyperfield(L,s,p);
    F.cache.minusOf = i -> minus sub(i,R);
    F
    )


--makes named Hyperrings: so far only "Krasner", "Sign" hyperfields are pre-made
makeHyperfield(String) := Hyperfield => S -> (
    if not member(S, {"Krasner", "Sign"}) then (
	error "only 'Krasner' and 'Sign' are implemented so far"
	);
    if S == "Krasner" then (
	L := {0,1, {0,1}};
	p := l -> product l;
	s := l -> (
	    num1s := #select(l, i -> i == 1);
	    if num1s == 0 then {0}
	    else if num1s == 1 then {1}
	    else {0,1}
	    );
	return makeHyperfield(L,s,p);
	);
    if S == "Sign" then (
	L = {0,1, {0,1,-1}};
	p = l -> product l;
	s = l -> (
	    num1sOrNegs := (#select(l, i -> i == 1), #select(l, i -> i == -1));
	    if num1sOrNegs == (0,0) then {0}
	    else if num1sOrNegs_1 == 0 then {1}
	    else if num1sOrNegs_0 == 0 then {-1}
	    else {0,1,-1}
	    );
	return makeHyperfield(L,s,p);
	);
    )

--input: a polynomial f with {-1,0,1}-coefficients over ZZ or QQ, a hyperfield F, 
--and a hash table H whose keys are variables in the polynomial ring and values in F
--output: if f evaluated as such contains the F-zero element
isNull = method()
isNull(RingElement,Hyperfield,HashTable) := Boolean => (f,F,H) -> (
    var := gens ring f;
    monoms := exponents f;
    coeffs := flatten entries transpose last coefficients f;
    toSum := apply(#monoms, i -> (
	    pre := F.product(apply(positions(monoms_i, j -> j != 0), k -> H#(var_k)));
	    if coeffs_i == -1 then (minusOf(F)) pre else pre
	    )
	);
    member(F.zero, F.sum(toSum))
    )


----------------------------------< ordinary matroids >------------------------------------

needsPackage "Matroids"

--given a list that is a permutation of {0,1,..,n-1}, outputs a FunctionClosure that
--performs the permutation on a sublist
listToFunction = L -> l -> (
    apply(l, i -> L_i)
    )

weakUnique = L -> (
    newL := {};
    apply(L, i -> if all(newL, j -> i != j) then newL = newL | {i});
    newL
    )


allMatroidsNoSym = method()

--all matroid of rank r on n elements, with isomorphism by permutation allowed
allMatroidsNoSym(ZZ,ZZ) := List => (r,n) -> (
    ML := select(allMatroids n, m -> rank m == r);
    perms := (permutations n)/listToFunction;
    flatten apply(ML, m -> weakUnique apply(perms, f -> matroid(m_*, sort((bases m)/elements/f))))
    )

--all matroids on n elements, with isomorphisms allowed
-- reasonable only for n < 8
allMatroidsNoSym(ZZ) := List => n -> (
    half := n//2;
    ML := allMatroids n;
    MLR := apply(half+1, i -> select(ML, m -> rank m == i));
    perms := (permutations n)/listToFunction;
    firstHalf := apply(MLR, ml -> flatten (
	    apply(ml, m -> weakUnique apply(perms, f -> matroid(m_*, sort((bases m)/elements/f))))
	    )
	);
    secondHalf := (
	if odd n then reverse (firstHalf/(l -> l/dual))
	else drop(reverse (firstHalf/(l -> l/dual)),1)
	);
    firstHalf | secondHalf
    )


isQuot = method()
isQuot(Matroid,Matroid) := Boolean => (m,n) -> isSubset(flats m, flats n)






-------------------------------------< F-matroids >--------------------------------------

FMatroid = new Type of HashTable
FMatroid.synonym = "F-matroid"

--an FMatroid is an immutable hash table with keys:
-- matroid => the underlying matroid M
-- field => the hyperfield F
-- Fbases => a hash table whose keys are bases of M (as sorted Lists, not Sets) and values in F

globalAssignment FMatroid
net FMatroid := FM -> net ofClass class FM |  " of rank " | toString(FM.matroid.rank) | " on " | toString(#FM.matroid.groundSet) | " elements over " | net FM.field


makeFMatroid = method()

--makes a FMatroid given a matroid M, hyperfield F, and a hash table H of valuated bases
makeFMatroid(Matroid, Hyperfield, HashTable) := FMatroid => (M,F,H) -> (
    new FMatroid from {
	symbol matroid => M,
	symbol field => F,
	symbol Fbases => H,
	cache => new CacheTable
	}
    )

--makes a FMatroid of rank r on n elements from r x n matrix A over a field F
makeFMatroid(Matrix) := FMatroid => A -> (
    F := makeHyperfield(ring A_(0,0));
    M := matroid A;
    H := hashTable apply(bases M, b -> (sort elements b, determinant A_(sort elements b)));
    makeFMatroid(M,F,H)
    )

dual(FMatroid) := FMatroid => {} >> opts -> FM -> (
    M := dual FM.matroid;
    F := FM.field;
    H := hashTable apply(bases M, b -> (
	    compl := M.groundSet - b;
	    bList := sort elements b;
	    complList := sort elements compl;
	    signature := sign( bList | complList );
	    val := FM.Fbases#complList;
	    if signature == 1 then (bList, val) else (bList, (minusOf(F)) val)
	    )
	);
    makeFMatroid(M,F,H)
    )

bases(FMatroid) := HashTable => FM -> FM.Fbases

--input: an FMatroid FM and a list L of polynomials whose variables are indexed by subsets(n,r)
--outputs: checks whether Fbases satisfies the isNull condition imposed by polynomials in L
--Note: when underlying matroid of FM is well-defined and F is perfect hyperfield, can use
--L to be just the three-term plucker relations
isWellDefined(FMatroid,List) := Boolean => (FM,L) -> (
    if L == {} then return true;
    R := ring first L;
    F := FM.field;
    B := bases FM.matroid;
    H := hashTable apply(gens R, i -> (
	    S := set last baseName i;
	    if member(S, B) then (i,FM.Fbases#(sort elements S)) else (i,F.zero)
	    )
	);
    all(L, f -> isNull(f,F,H))
    )

--tests the three-term relations for well-definedness
isWellDefined(FMatroid) := Boolean => FM -> (
    M := FM.matroid;
    L := threeTermRels(rank M, #(elements M.groundSet));
    isWellDefined(FM,L)
    )


lifts = method()

--input: a matroid M and a hyperfield F
--output: the list of all F-matroids (up to global scaling) whose underlying matroid is M
lifts(Matroid,Hyperfield) := (M,F) -> (
    units := set(F.elements) - set({F.zero});
    B := bases M;
    cands := (elements (units ^** (#B-1)));
    apply(#B-1, i -> cands = cands/splice);
    cands = apply(cands, i -> {1} | toList i);
    FMcands := apply(cands, i -> makeFMatroid(M,F,hashTable apply(#B, j -> (sort elements B_j, i_j))));
    r := rank M;
    n := #(elements M.groundSet);
    L := threeTermRels(r,n);
    select(FMcands, m -> isWellDefined(m,L))
    )

--same as above, but the relations are provided beforehand as a list L
lifts(Matroid,Hyperfield,List) := (M,F,L) -> (
    units := set(F.elements) - set({F.zero});
    B := bases M;
    cands := (elements (units ^** (#B-1)));
    apply(#B-1, i -> cands = cands/splice);
    cands = apply(cands, i -> {1} | toList i);
    FMcands := apply(cands, i -> makeFMatroid(M,F,hashTable apply(#B, j -> (sort elements B_j, i_j))));
    select(FMcands, m -> isWellDefined(m,L))
    )


--input: integers r and n, Hyperfield F
--output: all F-matroids of rank r on n elements over hyperfield F
allMatroidsNoSym(ZZ,ZZ,Hyperfield) := (r,n,F) -> (
    ML := allMatroidsNoSym(r,n);
    L := threeTermRels(r,n);
    flatten apply(ML, m -> lifts(m,F,L))    
    )

allMatroidsNoSym(ZZ,Hyperfield) := (n,F) -> (
    half := n//2;
    firstHalf := apply(half+1, i -> allMatroidsNoSym(i,n,F));
    secondHalf := (
	if odd n then reverse (firstHalf/(l -> l/dual))
	else drop(reverse  (firstHalf/(l -> l/dual)), 1)
	);
    firstHalf | secondHalf
    )

--tests whether two F-matroids form a F-quotient FM <<-- FN
isQuot(FMatroid,FMatroid) := (FM,FN) -> (
    F := FM.field;
    if F =!= FN.field then error "underlying hyperfields are different";
    M := FM.matroid;
    N := FN.matroid;
    r := rank M;
    s := rank N;
    if r == s then return FM === FN;
    if not isQuot(M,N) then return false;
    n := #(elements M.groundSet);
    L := singleIncidences(r,s,n);
    if L == {} then return true;
    R := ring first L;
    BM := bases M;
    BN := bases N;
    H := hashTable apply(gens R, i -> (
	    S := set last baseName i;
	    if member(S, BM) then (i,FM.Fbases#(sort elements S))
	    else if member(S,BN) then (i, FN.Fbases#(sort elements S))
	    else (i,F.zero)
	    )
	);
    all(L, f -> isNull(f,F,H))
    )

isQuot(FMatroid,FMatroid,List) := (FM,FN,L) -> (
    F := FM.field;
    if F =!= FN.field then error "underlying hyperfields are different";
    M := FM.matroid;
    N := FN.matroid;
    r := rank M;
    s := rank N;
    if r == s then return FM === FN;
    if not isQuot(M,N) then return false;
    n := #(elements M.groundSet);
    if L == {} then return true;
    R := ring first L;
    BM := bases M;
    BN := bases N;
    H := hashTable apply(gens R, i -> (
	    S := set last baseName i;
	    if member(S, BM) then (i,FM.Fbases#(sort elements S))
	    else if member(S,BN) then (i, FN.Fbases#(sort elements S))
	    else (i,F.zero)
	    )
	);
    all(L, f -> isNull(f,F,H))
    )


---------------------------< Lie bracket related functions >-----------------------------

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


--making the global Lefschetz operator
globalOperator = method()

--auxiliary function: matrices filled with 0 (in QQ)
zeroMat = (m,n) -> matrix apply(m, i -> apply(n, j -> 0/1))

--given a list L of matrices, representing the linear maps that change degree by
--an integer d = -1, 0, or 1, outputs a matrix representing the operator on the whole space
globalOperator(List,ZZ) := Matrix => (L,d) -> (
    rks := L/numcols;
    n := #L;
    matrix apply(n, i -> apply(n, j -> (
		if i-j == d then L_j
		else zeroMat(rks_i,rks_j)
		)
	    )
	)
    )

--reverses the globalOperator function from square matrix G,
--given the ranks list rks and degree d = -1, 0, or 1
mapsByDeg = method()
mapsByDeg(Matrix,List,ZZ) := List => (G,rks,d) -> (
    sumrks := apply(#rks, i -> sum(i, j -> rks_j));
    if d == 0 then apply(#rks, i -> (
	    rows := apply(rks_i, j -> j + sumrks_i);
	    cols := apply(rks_i, j -> j + sumrks_i);
	    G_cols^rows
	    )
	)
    else if d == 1 then apply(#rks-1, i -> (
	    rows := apply(rks_(i+1), j -> j + sumrks_(i+1));
	    cols := apply(rks_i, j -> j + sumrks_i);
	    G_cols^rows
	    )
	) | {zeroMat(1, last rks)}
    else if d == -1 then {zeroMat(1,first rks)} | apply(#rks-1, i -> (
	    rows := apply(rks_i, j -> j + sumrks_i);
	    cols := apply(rks_(i+1), j -> j + sumrks_(i+1));
	    G_cols^rows
	    )
	)
    )

--bracket [A,B] = AB - BA
bracket = (A,B) -> A*B - B*A

findLambda = method()
--computes the global Lambda operator from GH, the global H, and GL, the global raising operator
findLambda(Matrix,Matrix) := Matrix => (GH,GL) -> (
    if bracket(GH,GL) != 2*GL then error "inputs (GH,GL) don't satisfy [GH,GL] = 2GL";
    x := symbol x;
    R := QQ[flatten apply(numcols GH, i -> apply(numcols GH, j -> x_(i,j)))];
    GLamX := transpose genericMatrix(R,numcols GH, numcols GH);
    GLamX = sub(GLamX, apply(gens R, i -> (
	    	pair := last baseName i;
	    	if pair_0 >= pair_1 then i => 0
	    	else i => i
	    	)
	    )
	);
    I1 := ideal flatten entries (bracket(GL,GLamX) - GH);
    I2 := ideal flatten entries (bracket(GH,GLamX) + 2*GLamX);
    I := ideal mingens (I1+I2);
    J := I; --+ ideal apply(gens ring prune I, i -> sub(i,R));
    J = ideal mingens J;
    --all(J_*, i -> member(#(terms i), {1,2}))
    subs := apply(J_*, f -> (
	    Tf := terms f;
	    if #Tf == 1 then leadMonomial f => 0
	    else if #Tf == 2 then leadMonomial f => -(last Tf)/(coefficient(leadMonomial f, f))
	    else error "not one or two terms"
	    )
    	);
    sub(sub(GLamX, subs),QQ)
    )
    




---------------------------< flag variety related functions >-----------------------------

--aux function: (-1)^(number of inversions in a list consisting of distinct integers)
sign = L -> (-1)^#(select(subsets(#L,2), i -> L_(last i) < L_(first i)))

--three term relations between Plucker coordinates
threeTermRels = method();
threeTermRels(ZZ,ZZ) := List => (r,n) -> (
    if r < 2 or n < 4 then return {};
    p := symbol p;
    pluckers := apply(subsets(n,r), i -> p_i);
    R := ZZ[pluckers];
    pVar := hashTable apply(gens R, i -> (last baseName i, i));
    toPlucker := l -> sign(l) * pVar#(sort l);
    fours := subsets(n,4);
    toThreeTerm := (c,q) -> (
	T1 := toPlucker(c | {q_0, q_1}) * toPlucker(c | {q_2, q_3});
	T2 := toPlucker(c | {q_0, q_2}) * toPlucker(c | {q_1, q_3});
	T3 := toPlucker(c | {q_0, q_3}) * toPlucker(c | {q_1, q_2});
	T1 - T2 + T3
	);
    relsPerFour := q -> (
	    compl := elements (set toList(0..(n-1)) - set q);
	    apply(subsets(compl, r-2), c -> toThreeTerm(c,q))
	    );
    flatten (fours/relsPerFour)
    )


--aux function: swaps out an element "a" in a list L with "b"
swap = (L,a,b) -> apply(L, i -> if i == a then b else i)


--given a list "ranks" of integers =< n, computes the single-exchange Plucker relations
--for the flag variety Fl(ranks;n)
singleExchanges = method();
singleExchanges(List,ZZ) := List => (ranks,n) -> (
    symbol p;
    pluckers := flatten (ranks/(r -> apply(subsets(n,r), i -> p_i)));
    R := QQ[pluckers];
    pVar := hashTable apply(gens R, i -> (last baseName i, i));
    idealGens := unique flatten apply(subsets(gens R, 2), i -> (
	    s1 := last baseName first i;
	    s2 := last baseName last i;
	    apply(s1, j -> 
		pVar#s1*pVar#s2 - sum(s2, k -> (
			s1new := swap(s1,j,k);
			s2new := swap(s2,k,j);
			if not (unique s1new == s1new and unique s2new == s2new) then 0_R
			else sign(s1new)*pVar#(sort s1new)*sign(s2new)*pVar#(sort s2new)
			)
		    )
		)
	    )
	);
    idealGens = delete(0_R, idealGens);
    pGens = {};
    apply(idealGens, i -> if not (member(i,pGens) or member(-i,pGens)) then pGens = pGens | {i});
    pGens
)

singleIncidences = method();
singleIncidences(ZZ,ZZ,ZZ) := List => (r,s,n) -> (
    if r == 0 or s == n then return {};
    full := singleExchanges({r,s},n);
    R := ring first full;
    select(full, f -> (
	    varPair := (toList factor first terms f)/value;
	    #(last baseName first varPair) != #(last baseName last varPair)
	    )
	)
    )

allExchanges = method();
allExchanges(List,ZZ) := Ideal => (ranks,n) -> (
    symbol p;
    pluckers := flatten (ranks/(r -> apply(subsets(n,r), i -> p_i)));
    R := QQ[pluckers];
    pVar := hashTable apply(gens R, i -> (last baseName i, i));
    
)


--given a list M = {M_1, .. , M_k} of matroids on [n] such that M_i quotient of M_(i+1),
--outputs the single-exchange Plucker relations for the flag Dressian
--needs the package "Matroids"
dressianEqns = method();
dressianEqns(List) := Ideal => M -> (
    ranks := M/rank;
    n := #(first M).groundSet;
    I := ideal singleExchanges(ranks,n);
    varsI := hashTable apply(gens ring I, i -> (last baseName i, i));
    toZero := ideal apply(flatten (M/nonbases), i -> varsI#(sort elements i));
    prune (I + toZero)
)


end

------------------------------------------------------------------------------------------------
---------------------------------------------< END >--------------------------------------------





------------------------------------------------------------------------------------------------
--old stuff from flag Dressian paper
------------------------------------------------------------------------------------------------

restart
load "Eur_ProjSpHF.m2"

singleExchanges({2},4)


time I = ideal singleExchanges({2,3},6);
varsI = hashTable apply(gens ring I, i -> (last baseName i, i));
#I_*
J = I + ideal(varsI#{0,1,3},varsI#{0,2,4},varsI#{3,4,5},varsI#{1,2,5})
J' = prune J
#J'_*
#(gens ring J')
toString J'_*
toString gens ring J'

M2 = matroid completeGraph 4;
M1 = uniformMatroid(2,6);
I = dressianEqns({M1,M2})
dim I
I2 = sub(I,GF(2^3)[gens ring I])
dim I2

I = dressianEqns({uniformMatroid(2,6),uniformMatroid(3,6)})

singleExchanges({2,3},6)


I = ideal singleExchanges({1,2,3,4},5)
time I = flagVariety({1,2,3,4},5);



listToString = L -> (S := ""; apply(L, i -> S = concatenate(S|toString(i))); S)
varList = R -> (
    symbol p; symbol q;
    r1 := #(last baseName first gens R);
    apply(gens R, i -> (
	    L := last baseName i;
	    if #L == r1 then q_(listToString L) else p_(listToString L)
	    )
	)
    )

S = QQ[varList ring I];
Ifinal = (map(S, ring I, gens S))I

toString Ifinal
toString gens ring Ifinal

#(gens ring Ifinal)


time I2 = flagVariety({2,3},6);
#I2_*
varsI2 = hashTable apply(gens ring I2, i -> (last baseName i, i));
J2 = I2 + ideal(varsI2#{0,1,3},varsI2#{0,2,4},varsI2#{3,4,5},varsI2#{1,2,5})
#J2_*
J2' = prune J2
dim J2'
radical J2'
#J2'_*

#I_*
#I2_*
numcols mingens I


I = Grassmannian(2,6)
varsI = hashTable apply(gens ring I, i -> (last baseName i, i))
J = I + ideal(varsI#(0,1,3),varsI#(0,2,4),varsI#(3,4,5),varsI#(1,2,5))
J = sub(J,QQ[gens ring J])
dim J
