/* vim: set syntax=magma : */
/*

*/
    
declare attributes AlgEtQIdl : SortKey; //See SortKeyPrime for a description.
declare attributes AlgEtQOrd : WKICM_barCanonicalRepresentatives, // a sequence, indexed as WKICM_bar, containing the 
                                                                // canonical representative of each weak class
                              SingularPrimesSorted;  // singular primes of the order, according to the their SortKey.

intrinsic SortKeyPrime(P::AlgEtQIdl)->SeqEnum[RngIntElt]
{Given a P of the maximal order of an etale algebra K over Q, returns a sequence of 3 integers [ j , N , i ], in the following way:
- Write K = K1 x ... x Kn with Ki a number field, and sort them according to the lexicographic order of the coefficients of the defining poly, starting from the constant term.
- Write P as a direct sum of n ideals, according to the same order.
- Then j is the unique component which does not contain the unit element, and
- N.i is the LMFDB label of P.
If P is a prime of a non-maximal order the output is the smallest sortkey of the finitely many primes of the maximal order above  P, sorted lexicographically.
Important: we assume that the number fields forming the etale algebra are different.}
    if not assigned P`SortKey then
        S:=Order(P);
        A:=Algebra(S);
        if IsMaximal(S) then
            require IsPrime(P) : "The ideal is not prime";
            nfs:=[ Coefficients(DefiningPolynomial(K)) : K in Components(A) ];
            require #nfs eq #Seqset(nfs) : "We need the number fields forming the etale algebra to be different";
            ind:=[1..#nfs];
            ParallelSort(~nfs,~ind);
            _,Ps:=IsProductOfIdeals(P);
            Ps:=< Ps[ind[i]] : i in [1..#ind] >; //sorted
            j:=[ i : i in [1..#nfs] | not One(Order(Ps[i])) in Ps[i] ][1];
            P_lmfdb:=LMFDBLabel(Ps[j]);
            P_lmfdb:=[ eval(s) : s in Split(P_lmfdb,".") ];
            assert #P_lmfdb eq 2;
            P`SortKey:=[ j ] cat P_lmfdb;
        else
            O:=MaximalOrder(A);
            pp:=PrimesAbove(O!!P);
            require forall{Q : Q in pp | (OneIdeal(S) meet S!!Q) eq P} : "The ideal is not prime";
            P`SortKey:=Min([ $$(Q) : Q in pp ]);
        end if;
    end if;
    return P`SortKey;
end intrinsic;

intrinsic SortPrimes(seq::SeqEnum[AlgEtQIdl]) -> SeqEnum[AlgEtQIdl]
{Given a sequence of primes of an order S, it sorts the sequence according to the lexicographic order of their SortKey.}
    keys:=[ SortKeyPrime(P) : P in seq ];
    ParallelSort(~keys,~seq);
    return seq;
end intrinsic;

intrinsic ComparePrimes(P::AlgEtQIdl,Q::AlgEtQIdl) -> RngIntElt 
{It returns -1 if P < Q, 0 if P eq Q, and 1 if P > Q, where the ordering is determined by the lexicographic order of their SortKeys.}
    require Order(P) eq Order(Q) : "The input ideals must be primes of the same order";
    if P eq Q then
        return 0;
    else
        P:=SortKeyPrime(P);
        Q:=SortKeyPrime(Q);
        if P lt Q then
            return -1;
        else 
            return 1;
        end if;
    end if;
end intrinsic;

intrinsic SortSingularPrimes(S::AlgEtQOrd) -> SeqEnum[AlgEtIdl]
{It sorts the singular primes of the order according to the scheme described in ComparePrimes.}
    if not assigned S`SingularPrimesSorted then
        if IsMaximal(S) then
            S`SingularPrimesSorted:=[PowerStructure(AlgEtQIdl)|];
        else
            S`SingularPrimesSorted:=SortPrimes(SingularPrimes(S));
        end if;
    end if;
    return S`SingularPrimesSorted;
end intrinsic;

my_hnf:=function(I,basis)
    M:=Matrix(AbsoluteCoordinates(ZBasis(I),basis));
    N:=Nrows(M);
    den:=Denominator(M);
    M:=ChangeRing(den*M,Integers());
    M:=HermiteForm(M);
    out:=[den];
    for i in [1..N] do
        for j in [i..N] do
            Append(~out,M[i,j]);
        end for;
    end for;
    ChangeUniverse(~out,Integers());
    return out;
end function;

intrinsic WKICM_barCanonicalRepresentatives(S::AlgEtQOrd)->SeqEnum[AlgEtQIdl]
{Let S be an order in an étale algebra K=Q[F]=Q[x]/(h), where h is a squarefree q-Weil polynomial. This intrinsic returns a sequence of canonical representatives of the classes in WKICM_bar(S), indexed in the same way. TODO what is canonical.}
    if not assigned S`WKICM_barCanonicalRepresentatives then
        cm:=CohenMacaulayType(S);
        if cm eq 1 then
            S`WKICM_barCanonicalRepresentatives:=[OneIdeal(S)];
        else
            if cm eq 2 then
                pp:=NonGorensteinPrimes(S);
                St:=TraceDualIdeal(S);
                d:=Index(St,OneIdeal(S));
                dSt:=d*St; // dSt c S.
                if #pp eq 1 then
                    S`WKICM_barCanonicalRepresentatives:=[OneIdeal(S),dSt];
                else
                    pows:=[];
                    for P in pp do
                        _,p,e:=IsPrimePower(Integers()!Index(S,P)); // e=Valuation(p,Index(S,P));
                        m:=Valuation(Index(S,dSt),p) div e; // Here we are using Proposition 4.2 of Klueners and Pauli 
                                                          // "Computing residue class rings ...".
                                                          // With such an m we have:
                                                          //   pp[i]^m \subseteq I_pp[i]
                        Append(~pows,P^m);
                    end for;
                    pows_hat:=[ &*[ pows[j] : j in [1..#pp] | j ne i ] : i in [1..#pp] ];
                    Is:=[ seq : seq in CartesianProduct([[OneIdeal(S),dSt] : i in [1..#pp]]) ];
                    out:=[];
                    for I in Is do
                        L:=&+[ (I[i]+pows[i]) * pows_hat[i] : i in [1..#pows_hat]];
                        assert IsInvertible(L) select L eq OneIdeal(S) else L ne OneIdeal(S);
                        Append(~out,L);
                    end for;
                    S`WKICM_barCanonicalRepresentatives:=out;
                end if;
            else //general case
                pp:=SingularPrimes(S);
                PS,pS:=PicardGroup(S);
                US,uS:=UnitGroup(S);

                G_acting:=function(P)
                    T:=MultiplicatorRing(P);
                    PT,pT:=PicardGroup(T);
                    UT,uT:=UnitGroup(T);
                    US_sub:=sub<UT | [ uS(US.i)@@uT : i in [1..Ngens(US)]] >;
                    ext:=hom<PS->PT | s:->(T!!pS(s))@@pT>;
                    ker:=[ pS(L) : L in Kernel(ext)];
                    // we need to replace L in ker so that T!!L = T.
                    for i in [1..#ker] do
                        L:=ker[i];
                        test,x:=IsPrincipal(T!!L);
                        assert test;
                        ker[i]:=(1/x)*L;
                    end for;
                    // next one is time consuming
                    assert forall{L : L in ker | T!!L eq T};
                    units:=[ uT(u) : u in Transversal(UT,US_sub) ];
                    return <T,units,ker>;
                end function;

                A:=Algebra(S);
                f:=DefiningPolynomial(A);
                g:=Degree(f) div 2;
                q:=Round(ConstantCoefficient(f)^(1/g));
                F:=PrimitiveElement(A);
                V:=q/F;
                basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];
                pp:=SortSingularPrimes(S);
                G:=G_acting(pp[1]);
                size:=#G[2]*#G[3];
                for i in [2..#pp] do
                    G_i:=G_acting(pp[i]);
                    size_i:=#G_i[2]*#G_i[3];
                    if (size_i lt size) then
                        // if size_i eq size then I keep what I already have, since the primes are sorted
                        G:=G_i;
                        size:=size_i;
                    end if;
                end for;
                T:=G[1];
                // T now contains the one with the smallest G_acting
                wkS:=WKICM_bar(S);
                wkT_can:=$$(T); // recursion here
                wkS_can:=[];
                for iI->I in wkS do
                    if IsInvertible(I) then
                        Append(~wkS_can,OneIdeal(S));
                    else
                        TI:=T!!I;
                        stop:=false;
                        j:=0;
                        repeat
                            j+:=1;
                            J:=wkT_can[j];
                            stop:=IsWeakEquivalent(TI,J);
                        until stop;
                        L:=ColonIdeal(J,TI);
                        x,xL:=MakeCoprime(L,T!!Conductor(S));
                        L1:=S!!xL meet OneIdeal(S); // L1 satisfies T!!L1=xL.
                        assert IsInvertible(L1);
                        I1:=(1/x)*I*L1; // I1 satisfies T!!I1 = J and I1 is weak eq to I.
                        assert IsWeakEquivalent(I1,I);
                        assert T!!I1 eq J;
                        candidates:=[ u*L*I1 : u in G[2] , L in G[3] ];
                        assert forall{ I2 : I2 in candidates | T!!I2 eq J }; //This is time consuming
                        sort_keys_candidates:=[ my_hnf(I1,basis) : I1 in candidates ];
                        ParallelSort(~sort_keys_candidates,~candidates);
                        Append(~wkS_can,candidates[1]);
                    end if;
                end for;
                S`WKICM_barCanonicalRepresentatives:=wkS_can;
            end if;
        end if;
    end if;
    return S`WKICM_barCanonicalRepresentatives;
end intrinsic;

seq_of_dims:=function(I)
// Given an ideal I over an order S, not necessarily the multipicator ring, 
// it returns a sequence the sequence of integers dim_(S/P) (I/PI), where P runs over the singular primes of S, sorted
// according to the ordering described in ComparePrimes
    S:=Order(I);
    if IsMaximal(S) then
        return [PowerStructure(RngIntElt)|];
    else
        return [ Ilog(Integers()!Index(S,P) , Integers() ! Index(I,P*I) ) : P in SortSingularPrimes(S) ];
    end if;
end function;

intrinsic SortKeysWKICM_bar(S::AlgEtQOrd) -> SeqEnum[SeqEnum[RngIntElt]]
{TODO}
    cm:=CohenMacaulayType(S);
    if cm le 2 then
        return [ seq_of_dims(I) : I in WKICM_bar(S) ];
    else
        A:=Algebra(S);
        f:=DefiningPolynomial(A);
        g:=Degree(f) div 2;
        q:=Round(ConstantCoefficient(f)^(1/g));
        F:=PrimitiveElement(A);
        V:=q/F;
        basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];
        return [ seq_of_dims(I) cat my_hnf(I,basis) : I in WKICM_barCanonicalRepresentatives(S) ];
    end if;
end intrinsic;

intrinsic SortKeysOrders(seq::SeqEnum[AlgEtQOrd]) -> SeqEnum[SeqEnum[RngIntElt]]
{TODO}
    A:=Algebra(seq[1]);
    f:=DefiningPolynomial(A);
    g:=Degree(f) div 2;
    q:=Round(ConstantCoefficient(f)^(1/g));
    F:=PrimitiveElement(A);
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];
    O:=MaximalOrder(A);
    return [ [Index(O,S)] cat my_hnf(S,basis) : S in seq ];
end intrinsic;

function Base26Encode(n)
        alphabet := "abcdefghijklmnopqrstuvwxyz";
        s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
        while n gt 0 do
                s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
        end while;
        return s;
end function;

function IsogenyLabel(f)
    g:=Degree(f) div 2;
    q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
    str1:=Reverse(Prune(Coefficients(f)))[1..g];
    str2:="";
    for a in str1 do
        if a lt 0 then
            str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
            else
            str2:=str2 cat Base26Encode(a) cat "_";
        end if;
    end for;
    str2:=Prune(str2);
    isog_label:=Sprintf("%o.%o.",g,q) cat str2;
    return isog_label;
end function;

RemoveBlanks:=function(str)
// given a string str removes the blank spaces
    return &cat(Split(str," "));
end function;

two_generating_set:=function(I,basis)
// given an invertible ideal I over some order S and a basis of the algebra
// it returns a pair [ c,elt ] where c is the smallerst integer in I and elt is a 
// not canonical
    S:=Order(I);
    A:=Algebra(S);
    if I eq OneIdeal(S) then
        M:=1;
        d:=1;
        alpha:=[0 : i in [1..#basis]]; //zero of A
    else
        M:=MinimalInteger(I);
        if M*S eq I then
            d:=1;
            alpha:=[0 : i in [1..#basis]]; //zero of A
        else
            zbI:=Rows(LLL(Matrix(AbsoluteCoordinates(ZBasis(I),basis))));
            k:=0;
            stop:=false;
            repeat
                k+:=1;
                j:=0;
                repeat
                    j+:=1;
                    rndm_coeffs:=[ Random(-k,k) : i in [1..#basis] ];
                    elt_coeffs:=[ [ rndm_coeffs[i]*z : z in ElementToSequence(zbI[i]) ] : i in [1..#basis] ];
                    elt_coeffs:=[ &+[ e[i] : e in elt_coeffs] : i in [1..#basis] ];
                    elt:=SumOfProducts(elt_coeffs,basis);
                    assert elt in I;
                    stop:=Ideal(S,[A!M,elt]) eq I;
                until stop or j eq 30;
            until stop;
            d:=LCM([ Denominator(e) : e in elt_coeffs]);
            nums:=[d*e : e in elt_coeffs];
            alpha:=nums;
        end if;
    end if;
    out:="[" cat Sprintf("%o,%o,%o",M,d,alpha) cat "]";
    out:=RemoveBlanks(out);
    return out;
end function;

intrinsic FillSchema(R::AlgEtQOrd)->MonStgElt
{ see Table av_fq_weak_equivalences at https://github.com/roed314/root-unitary/blob/stage_based/postgres_schema.md  }
    f:=ChangeRing(DefiningPolynomial(Algebra(R)),Integers());
    F:=PrimitiveElement(Algebra(R));
    g:=Degree(f) div 2;
    q:=Round(ConstantCoefficient(f)^(1/g));
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];

    isog_label:=IsogenyLabel(f);
    oo:=OverOrders(R);
    oo_sort_keys:=SortKeysOrders(oo);
    ParallelSort(~oo_sort_keys,~oo);

    // orders are now sorted.
    // orders with the same index are grouped together, and already in the right order
    indices_oo:=[ oo_sort_keys[i][1] : i in [1..#oo] ];

    // We construct the labels of the orders
    labels_oo:=[];
    current_index:=indices_oo[1];
    i:=0;
    for iS->S in oo do
        N:=indices_oo[iS];
        if N eq current_index then
            i+:=1;
        else
            // we sorted we reset the counter
            i:=1;
            current_index:=N;
        end if;
        label_S:=Sprintf("%o.%o",N,i);
        Append(~labels_oo,label_S);
    end for;

    min_oo:=[];
    // Populate min_oo: in the i-th entry we put the labels of the minimal overorders of oo[i].
    // The computation is done as follows:
    // adj_mat[i,j] = 1 if oo[i] subsetneq oo[j], and 0 otherwise (the adjacency matrix of the strinct inclusion graph)
    // The transitive reduction of the the correspondig graph (which is the subgraph whose edges are the minimal inclusions) 
    // is obtained by squaring the adj_mat and 
    adj_mat:=ZeroMatrix(Integers(),#oo);
    for i,j in [1..#oo] do
        if i ne j and oo[i] subset oo[j] then
            adj_mat[i,j]:=1;
        else
            adj_mat[i,j]:=0;
        end if;
    end for;
    adj_mat_sq:=adj_mat^2; 
    for i in [1..#oo] do
        min_oo_i:=[ labels_oo[j] : j in [1..#oo] | adj_mat[i,j] eq 1 and adj_mat_sq[i,j] eq 0 ];
        Append(~min_oo,min_oo_i);
    end for;

    //conductors
    O:=MaximalOrder(Algebra(R));
    condS:=[Conductor(S) : S in oo];
    condS_prime:=[ IsPrime(ff) select "t" else "f" : ff in condS ];
    condS_ind:=[Index(oo[i],condS[i]) : i in [1..#oo]];
    condO:=[O!!ff : ff in condS];
    condO_two_gens:=[ two_generating_set(ff,basis) : ff in condO ];
    condO_prime:=[ IsPrime(ff) select "t" else "f" : ff in condO ];
    condO_ind:=[Index(O,ff) : ff in condO];
    cond_classes:=[ labels_oo[Index(condO,ff)] : ff in condO ];

    output:="";
    for iS->S in oo do
        wkS:=WKICM_barCanonicalRepresentatives(S);
        assert #wkS eq #WKICM_bar(S);
        wkS_sort_keys:=SortKeysWKICM_bar(S);
        ParallelSort(~wkS_sort_keys,~wkS);
        n_sing:=#SingularPrimes(S);
        if #min_oo[iS] eq 0 then //maximal order
            minimal_overorders_S:="{}";
        else
            minimal_overorders_S:="{" cat Prune(&cat[ Sprintf("%o,",m) : m in min_oo[iS] ]) cat "}";
        end if;

        N:=indices_oo[iS];
        pic_size:=#PicardGroup(S);
        multiplicator_ring:=labels_oo[iS];
        labelS:=Sprintf("%o.%o",isog_label,multiplicator_ring);
        for j->I in wkS do
            sort_key:=wkS_sort_keys[j];
            label:=labelS cat Sprintf(".%o",j);
            we_number:=j;
            hnf:=my_hnf(I,basis);
            ideal_basis_numerators:="{" cat Prune(&cat[Sprintf("%o,",hnf[i]):i in [2..#hnf]]) cat "}";
            ideal_basis_denominator:=hnf[1];
            dimensions:=[sort_key[i]:i in [1..n_sing]];
            is_invertible:=(#dimensions eq 0 or &+dimensions eq n_sing) select "t" else "f";
            if is_invertible eq "t" then
            // certain things should be stored only for the wk_classes that are orders
                minimal_overorders_I:=minimal_overorders_S;
                cohen_macaulay_type:=CohenMacaulayType(S);
                conductor:=condO_two_gens[iS];
                conductor_is_Sprime:=condS_prime[iS];
                conductor_is_Oprime:=condO_prime[iS];
                conductor_Sindex:=condS_ind[iS];
                conductor_Oindex:=condO_ind[iS];
                condutor_class:=cond_classes[iS];
            else
                minimal_overorders_I:="\\N";
                cohen_macaulay_type:="\\N";
                conductor:="\\N";
                conductor_is_Sprime:="\\N";
                conductor_is_Oprime:="\\N";
                conductor_Sindex:="\\N";
                conductor_Oindex:="\\N";
                condutor_class:="\\N";
            end if;
            if #dimensions eq 0 then //maximal order
                dimensions:="{}";
            else
                dimensions:="{" cat Prune(&cat[Sprintf("%o,",d):d in dimensions]) cat "}";
            end if;
            groups:=[ Quotient(I,(1-F^d)*I) : d in [1..10]];
            // if G is trivial, AbelianInvariants returns [] instead of [1]. Go figure.
            invariants:=[ #G eq 1 select [1] else AbelianInvariants(G) : G in groups ];
            rational_invariants:="{" cat Prune(&cat[Sprintf("%o,",i):i in invariants[1]]) cat "}";
            higher_invariants:=[ "[" cat Prune(&cat[Sprintf("%o,",i):i in invariants[d]]) cat "]," : d in [2..#invariants] ];
            higher_invariants:="[" cat Prune(&cat([inv : inv in higher_invariants])) cat "]";

            line_j:=Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o\n",label,we_number,pic_size,multiplicator_ring,isog_label,ideal_basis_numerators,ideal_basis_denominator,is_invertible,cohen_macaulay_type,dimensions,minimal_overorders_I,rational_invariants,higher_invariants,conductor,conductor_is_Sprime,conductor_is_Oprime,conductor_Sindex,conductor_Oindex,condutor_class);

            output cat:=line_j;
        end for;
    end for;
    return output;
end intrinsic;

function Base26Decode(s)
        alphabetbase := StringToCode("a");
        n := 0;
        for c in Eltseq(s) do n := 26*n + StringToCode(c) - alphabetbase; end for;
        return n;
end function;
function LabelToPoly(lab)
    PP:=PolynomialRing(Integers());
    lab:=Split(lab,".");
    g:=eval(lab[1]);
    q:=eval(lab[2]);
    coeffs:=Split(lab[3],"_");
    out:=[1]; //the coeff of x^2g
    for cc in coeffs do
        if #cc gt 1 then
            if cc[1] eq "a" then
                Append(~out,-Base26Decode(cc[2..#cc]));
            else
                Append(~out,Base26Decode(cc));
            end if;
        else
            Append(~out,Base26Decode(cc));
        end if;
    end for;
    assert #out eq g+1;
    out2:=[ q^(g-(i-1))*out[i] : i in [1..g] ];
    out cat:= Reverse(out2);
    Reverse(~out);
    f:=PP ! out;
    return g,q,f;
end function;


intrinsic LoadSchemaWKClasses(str::MonStgElt)->AlgEtQOrd
{Given the output of the schema for one isogeny class returns the order Z[F,V] with the attributes for overorders and weak equivalence classes populated.}
    lines:=[ Split(l,":") : l in Split(str)];
// each line consists of:
//  1  label,
//  2  we_number,
//  3  pic_size,
//  4  multiplicator_ring,
//  5  isog_label,
//  6  ideal_basis_numerators,
//  7  ideal_basis_denominator,
//  8  is_invertible,
//  9  cohen_macaulay_type,
//  10 dimensions,
//  11 minimal_overorders_I,
//  12 rational_invariants,
//  13 higher_invariants,
//  14 conductor,
//  15 conductor_is_Sprime,
//  16 conductor_is_Oprime,
//  17 conductor_Sindex,
//  18 conductor_Oindex,
//  19 condutor_class
    g,q,f:=LabelToPoly(lines[1][1]);
    A:=EtaleAlgebra(f);
    F:=PrimitiveElement(A);
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];

    zb_in_A:=function(nums,den)
        return [SumOfProducts([c/den : c in n ],basis) : n in nums ];
    end function;

    braces_to_seq_of_seqs:=function(str)
    // given a string of the form {x1,...,xn}, constructs the sequence [x1,...,xn],
    // which is used to fill an g times g upper tri matrix, 
    // whose rows are then returned (as a sequence of sequences).
        assert str[1] eq "{" and str[#str] eq "}";
        seq:=eval("[" cat str[2..#str-1] cat "]");
        T:=UpperTriangularMatrix(seq);
        return [ Eltseq(r) : r in Rows(T) ];
    end function;

    oo:=[ Order(zb_in_A(braces_to_seq_of_seqs(l[6]),eval(l[7]))) : l in lines | l[8] eq "t" ];
    oo_labels:=[ l[4] : l in lines | l[8] eq "t" ];
    oo_indices:=[ eval(Split(l,".")[1]) : l in oo_labels ];
    assert #{ x : x in oo_indices | x eq 1} eq 1; 
    O:=oo[Index(oo_indices,1)];
    assert IsMaximal(O);
    max:=Max(oo_indices);
    assert #{ x : x in oo_indices | x eq max} eq 1; 
    R:=oo[Index(oo_indices,max)];
    assert R eq Order([F,V]);
    oo_cond:=[ eval("<" cat ll[2..#ll-1] cat ">") : ll in  [ l[14] : l in lines | l[8] eq "t" ] ];
    oo_cond:=[ Ideal(O,[A!t[1]] cat zb_in_A([t[3]],t[2])) : t in oo_cond ];
    oo_min_oo:=[ Split(l[11][2..#l[11]-1], ",") : l in lines | l[8] eq "t" ];
    // note in an older version of FillSchema I put [] instead of {} in l[11].
    // the previous line is not affected by this mistake.

    for iS in [1..#oo] do
        S:=oo[iS];
        labelS:=oo_labels[iS];
        wkS:=[ Ideal(S,zb_in_A(braces_to_seq_of_seqs(l[6]),eval(l[7]))) : l in lines | l[4] eq labelS ];
        assert2 forall{ I : I in wkS | MultiplicatorRing(I) eq S };
        assert2 forall{ i : i,j in [1..#wkS] | (i eq j) eq (IsWeakEquivalent(wkS[i],wkS[j])) }; //TIME consuming
        ffS:=S!!oo_cond[iS];
        assert ffS eq Conductor(S);
        min_oo_S:=[ oo[Index(oo_labels,lab)] : lab in oo_min_oo[iS] ];
        sing_pp:=[ ColonIdeal(OneIdeal(S),S!!OneIdeal(T)) : T in min_oo_S ];
        sing_pp_set:=Seqset(sing_pp);
        assert Seqset(SingularPrimes(S)) eq sing_pp_set;
        min_oo_at_primes:=[];
        for P in Setseq(sing_pp_set) do
            min_oo_P:={@ min_oo_S[i] : i in [1..#sing_pp] | sing_pp[i] eq P @};
            Append(~min_oo_at_primes,<P,min_oo_P>);
        end for;
        S`MinimalOverOrders:=min_oo_at_primes;
        S`WKICM_bar:=wkS;
    end for;

    R`OverOrders:=oo;
    _:=WKICM(R); //to populate

    return R;
end intrinsic;

/*
    //SetDebugOnError(true);
    "Loading input";
    ord_cs_isog_classes:=Split(Read("~/266_wk_icm_rec/labelling/parallel/weil_sqfree_ord_cs.txt"));
    fld_wk:="~/266_wk_icm_rec/labelling/parallel/wk_classes/";

    AttachSpec("~/266_wk_icm_rec/labelling/parallel/AlgEt/spec");
    Attach("~/266_wk_icm_rec/labelling/parallel/labelling.m");

    "Test is starting";
    timings:=[];
    perc:=0; perc_old:=0; tot:=#ord_cs_isog_classes;
    for ifile->file in ord_cs_isog_classes do
        perc:=Truncate(100*ifile/tot); if perc gt perc_old then printf "%o%% ",perc; perc_old:=perc; end if;
        t0:=Cputime();
            try
                R:=LoadWKICM(Read(fld_wk cat file cat "_wkicm.txt"));
            catch
                e;
                R:=LoadWKICM(Read(fld_wk cat file cat "_wkicm.txt_wkicm.txt"));
            end try;
            schema:=FillSchema(R);
            assert #WKICM(R) eq #Split(schema);
            //schema;
        t1:=Cputime(t0);
        Append(~timings,t1);
    end for;
    "Total timings", &+(timings); 
*/
