//freeze;

/////////////////////////////////////////////////////
// Picard Group of orders in etale algebras over \Q
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

import "usefulfunctions.m": AllPossibilities;
import "sorting/code/sorting.m": SplitPrime;

/*TODO:
-Discrete Log in ResidueRingUnits (is it necessary?)
*/

declare attributes AlgAssVOrd:PicardGroup;
declare attributes AlgAssVOrd:PicardGroup_LMFDB;
declare attributes AlgAssVOrd:UnitGroup;

function CanonicalPrimeIdealsOverPrime(OL, p, FL, Find)
    L := NumberField(OL);
    Lp := PrimeIdealsOverPrime(L, p);
    if Find mod p eq 0 then
        // Remove primes dividing the conductor
        Lp := [I : I in Lp | One(OL) in I+FL];
    // in the other case, we keep the last element, even though its lift is automatically in the span of the others, since it might have a better order
    end if;
    if #Lp gt 1 then
        // Sort using the LMFDB label
        keys := [<StringToInteger(c) : c in Split(LMFDBLabel(Lp[z]), ".")> cat <z> : z in [1..#Lp]];
        Sort(~keys);
        Lp := [Lp[key[#key]] : key in keys];
    end if;
    return Lp;
end function;

function asProdData(S)
    A := Algebra(S);
    O := MaximalOrder(A);
    F := Conductor(S);
    P, pmap := PicardGroup(S);
    nfs:=[ Coefficients(DefiningPolynomial(K)) : K in Components(A) ];
    ind:=[1..#nfs];
    ParallelSort(~nfs, ~ind);
    b, O_asProd := IsProductOfOrders(O); assert b; assert #O_asProd eq #ind;
    O_asProd := <O_asProd[ind[i]] : i in [1..#ind]>;
    b, F_asProd := IsProductOfIdeals(O!!F); assert b; assert #F_asProd eq #ind;
    F_asProd := <F_asProd[ind[i]] : i in [1..#ind]>;
    F_indexes := [Index(Order(I),I) : I in F_asProd];
    return O_asProd, F_asProd, F_indexes;
end function;

function MakeOPrime(P, O_asProd, i)
    return Ideal(O, <(i eq j) select P else 1*O_asProd[j] : j in [1..#O_asProd]>);
end function;

function MakeSPrime(S, P)
    return S!!P meet S;
end function;

function MakeSPrime(S, P, O_asProd, i)
    // Construct a prime of S given a prime P in position i of the product decomposition O_asProd of the maximal order
    return MakeSPrime(S, MakeOPrime(P, O_asProd, i));
end function;

intrinsic CanonicalPicGenerators(S::AlgEtQOrd) -> SeqEnum, SeqEnum
{}
    O_asProd, F_asProd, F_indexes := asProdData(S);
    primes_above_p := AssociativeArray();
    primes_by_norm := [];
    Pgens := [];
    construction := [];
    Psub := sub<P|>;
    q := 1;
    while true do
        // we will loop over prime powers q
        // and then we add primes of norm q to our list of primes
        while true do
            q +:= 1;
            b, p, k := IsPrimePower(q);
            if b then // q is a prime power
                break;
            end if;
        end while;
        // if k = 1, we create a list of split primes above p.
        // this is used to create a list of primes of norm q for all powers of p.
        if k eq 1 then
            for i in [1..#O_asProd] do
                primes_above_p[<i, p>] := CanonicalPrimeIdealsOverPrime(O_asProd[i], p, F_asProd[i], F_indexes[i]);
            end for;
        end if;
        for i in [1..#O_asProd] do
            for pcnt->prime in primes_above_p[<i,p>] do
                // create a Oprime = \prod_j prime if i eq j else 1
                // where Norm(Oprime) = q = p^k
                if InertiaDegree(prime) eq k then
                    Sprime := MakeSPrime(S, P, O_asProd, i);
                    plift := Sprime@@pmap;
                    if #sub<P|Pgens cat [plift]> gt #Psub then
                        Append(~Pgens, plift);
                        Append(~construction, <i, p, pcnt, Order(plift)>);
                        Psub := sub<P|Pgens>;
                        if #Psub eq #P then
                            return Pgens, construction;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end while;
end intrinsic;

intrinsic CanonicalPicGenerators(S::AlgEtQOrd, construction::SeqEnum) -> SeqEnum
{A version that produces the canonical generators using the saved construction, and returned as prime ideals in the maximal order of S together with their orders in Pic(S) (so that the computation of Pic(S) isn't required).
Note that the returned generators are not independent; see CanonicalPicBasis}
    O_asProd, F_asProd, F_indexes := asProdData(S);
    gens := [];
    primes_above_p := AssociativeArray();
    for quad in construction do
        i, p, pcnt, ord := Explode(quad);
        if not IsDefined(primes_above_p, <i,p>) then
            primes_above_p[<i,p>] := CanonicalPrimeIdealsOverPrime(O_asProd[i], p, F_asProd[i], F_indexes[i]);
        end if;
        Lp := primes_above_p[<i,p>];
        Append(~gens, MakeOPrime(Lp[pcnt], O_asProd, i));
    end for;
end intrinsic;

intrinsic remove_whitespace(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return remove_whitespace(Sprintf("%o",X));
end intrinsic;

intrinsic GensToBasis(S::AlgEtQOrd, gens::SeqEnum) -> SeqEnum, SeqEnum
{Takes as input an order S in an etale algebra and a sequence gens of generators of Pic(S), and returns a basis of Pic(S) (aligning with the structure described by AbelianInvariants(Pic(S)))}
    P := PicardGroup(S);
    invs := AbelianInvariants(P);
    vprint User1: "Starting GensToBasis", Index(MaximalOrder(Algebra(S)), S), sprint(invs); t0:=Cputime();
    curquo := map<P -> P|x :-> x, y :-> y>;
    basis := [];
    construction := [];
    Con := AbelianGroup([Order(g) : g in gens]); // for tracking which linear combinations are used
    orders := [Order(g) : g in gens];
    while #basis lt #invs do
        Psub := sub<P|basis>;
        _, curquo := quo<P|Psub>;
        orders := [Order(curquo(g)) : g in gens];
        looking_for := invs[#invs-#basis];
        // We can skip orders that are dominated by earlier orders
        lcms := [orders[1]];
        for i in [2..#orders] do
            Append(~lcms, Lcm(lcms[i-1], orders[i]));
        end for;
        relevant := [i : i in [1..#orders] | orders[i] gt 1 and (i eq 1 or lcms[i-1] mod orders[i] ne 0)];
        n := 1; // encode subset using bits
        while true do
            ss := IntegerToSequence(n, 2);
            tt := [relevant[c] : c in [1..#ss] | ss[c] eq 1]; // the positions of the generators we'll be using to construct an element of the right order
            ord := Lcm([orders[t] : t in tt]);
            if ord eq looking_for then // it's possible to construct an element of right right order using combinations of these generators
                b := &+[gens[t] : t in tt]; // try the simplest first
                cons := &+[Con.t : t in tt];
                if Order(curquo(b)) ne ord then
                    // go through all combinations in a fixed order.  By minimality, we need to use all the generators, so no coefficient can be 0.
                    // We reverse tt since we want iteration like <1,1>, <2,1>, <1,2>, <2,2> and Cartesian product changes the last coordinate first
                    for c in CartesianProduct(<[1..orders[t]-1] : t in Reverse(tt)>) do
                        b := &+[c[#c+1-j] * gens[tt[j]] : j in [1..#tt]];
                        if Order(curquo(b)) eq ord then
                            cons := &+[c[#c+1-j] * Cons.(tt[j]) : j in [1..#tt]];
                            break;
                        end if;
                    end for;
                end if;
                // b now has the right order in the projection, but we need to subtract off some combination of the previous generators to make it the right order in P itself
                // (ord * b) in Psub, since it's 0 in the quotient.  Morever, ord*b in ord*Psub, since ord divides the order of each of the generators of Psub.  Need to find this element so that we can subtract.
                if #basis gt 0 then
                    AbSub := AbelianGroup(invs[#invs-#basis+1..#invs]);
                    iso := hom<AbSub -> P | [<AbSub.j, basis[#basis+1-j]> : j in [1..#basis]]>;
                    y := Eltseq((ord*b) @@ iso);
                    assert &and[y[j] mod ord eq 0 : j in [1..#y]];
                    b -:= &+[(y[j] div ord) * basis[#basis+1-j] : j in [1..#basis]];
                    cons -:= &+[(y[j] div ord) * construction[#basis+1-j] : j in [1..#construction]];
                end if;
                assert Order(b) eq ord;
                Append(~basis, b);
                Append(~construction, cons);
                break;
            end if;
            n +:= 1;
        end while;
        vprint User1: "basis loop", Cputime() - t0, sprint(orders), looking_for, n; t0 := Cputime();
    end while;
    Reverse(~basis);
    Reverse(~construction);
    construction := [[Integers()!c : c in Eltseq(cons)] : cons in construction];
    assert [Order(b) : b in basis] eq invs and #sub<P|basis> eq #P;
    assert &and[basis[i] eq &+[construction[i][j] * gens[j] : j in [1..#construction[i]]] : i in [1..#basis]];
    return basis, <invs, construction>;
end intrinsic;

intrinsic CanonicalPicBases(ZFV::AlgEtQOrd) -> List
{Find an abelian basis for the Picard group of each overorder of ZFV using a deterministic method}
    vprint User1: "Starting OverOrders"; t0 := Cputime();
    oo := OverOrders(ZFV);
    vprint User1: "OverOrders finished", Cputime() - t0;
    j := Index(oo, ZFV);
    vprint User1: "Starting PicardGroup"; t0 := Cputime();
    P0, pmap0 := PicardGroup(ZFV);
    vprint User1: "PicardGroup finished", Cputime() - t0; t0 := Cputime();
    ZFVgens, gens_construction := CanonicalPicGenerators(ZFV);
    vprint User1: "CanonicalPicGenerators finished", Cputime() - t0; t0:=Cputime();
    igens := [pmap0(P0.i) : i in [1..Ngens(P0)]];
    vprint User1: "igens finished", Cputime() - t0;
    bases := [* *];
    basis_constructions := [* *];
    for i->S in oo do
        if i eq j then
            Sgens := ZFVgens;
        else
            vprint User1: "Starting PicardGroup", i; t0:=Cputime();
            P, pmap := PicardGroup(S);
            vprint User1: "PicardGroup finished", Cputime() - t0; t0:=Cputime();
            P0Pmap := hom<P0 -> P | [<P0.i, (S!!igens[i]) @@ pmap> : i in [1..Ngens(P0)]]>;
            Sgens := [P0Pmap(g) : g in ZFVgens];
            vprint User1: "Sgens finished", Cputime() - t0; t0:=Cputime();
        end if;
        basis, bcon := GensToBasis(oo[i], Sgens);
        Append(~bases, basis);
        Append(~basis_constructions, bcon);
    end for;
    return bases, basis_constructions;
end intrinsic;

intrinsic CanonicalPicBasis(S::AlgEtQOrd, gens::SeqEnum, basis_info::Tup) -> SeqEnum
{Given an order S, a sequence gens of ideals of the maximal order of S (as output by CanonicalPicGenerators(ZFV, gen_info)) that generate Pic(ZFV), and basis_info as output by the other version of CanonicalPicBasis, return a sequence of ideals of S that forms a basis for Pic(S)}
    invs, construction := Explode(basis_info);
    assert &and[#cons eq #gens : cons in construction];
    basis := [&*[gens[j]^construction[i][j] : j in [1..#gens]] : i in [1..#construction]];
    return [MakeSPrime(b) : b in basis];
end intrinsic;

function IntToInvVec(pos, invs)
    // Note that pos is 0-indexed!
    // We want to iterate in the order 000,001,002,003, etc so that a longer string in the iteration is just shifting by the same basis vector
    ans := [];
    for d in Reverse(invs) do
        r := pos mod d;
        Append(~ans, r);
        pos := (pos - r) div d;
    end for;
    assert pos eq 0; // fails if input too big
    return Reverse(ans);
end function;

intrinsic IdealFromPosition(pos::RngIntElt, basis::SeqEnum, invs::SeqEnum) -> AlgEtQIdl
{}
    coeffs := IntToInvVec(pos - 1, invs);
    assert #coeffs eq #basis;
    return &*[basis[j]^coeffs[j] : j in [1..#basis]];
end intrinsic;

intrinsic IdealFromPosition(pos::RngIntElt, ZFV::AlgEtQOrd, S::AlgEtQOrd, gen_info::SeqEnum, basis_info::Tup) -> AlgEtQIdl
{Given a an integer pos between 1 and #Pic(S) and saved information, computes an ideal that is equivalent in the Picard group to the one produced in position pos in the iteration.
gen_info - second part of output of CanonicalPicGenerators(ZFV)
Note that if you're calling this for many different pos, it's probably better to compute gens and basis and use another form of IdealFromPosition.
}
    gens := CanonicalPicGenerators(ZFV, gen_info);
    invs, construction := Explode(basis_info);
    basis := CanonicalPicBasis(S, gens, basis_info);
    return IdealFromPosition(pos, basis, invs);
end intrinsic;

intrinsic PicIteration(S::AlgEtQOrd, basis::SeqEnum, filter::UserProgram) -> SeqEnum
{Iterates over the elements of the Picard group in a consistent order, using a filter function on Pic(S).  basis_info should be an entry in the *first* part of the output of CanonicalPicBases(S), and filter should be take a single element of Pic(S) as input and return a boolean (the ideal is included if the output is true).  The output is a sequence of pairs <i, I>, where I is an ideal and i is the index of that ideal in the overall iteration.}
    P, pmap := PicardGroup(S);
    invs := AbelianInvariants(P);
    iter := [&+basis[i..#basis] : i in [1..#basis]];
    coeffs := [0 : i in invs];
    cur := P.0; // identity
    ans := [];
    ctr := 1;
    while true do
        if filter(cur) then
            Append(~ans, <pmap(cur), ctr>);
        end if;
        pos := #coeffs;
        while coeffs[pos] eq invs[pos] - 1 do
            coeffs[pos] := 0;
            pos -:= 1;
            if pos eq 0 then
                return ans;
            end if;
        end while;
        // If we weren't filtering, we could multiply by pmap(iter[pos]) rather than adding and eventually applying pmap(cur).  Hopefully the cost of applying pmap is dwarfed by the polarization calculation we have to do.
        cur +:= iter[pos];
        ctr +:= 1;
    end while;
end intrinsic;

intrinsic Random(G::GrpAuto : word_len:=40) -> GrpAutoElt
{}
    gens := [<g, Order(g)> : g in Generators(G)];
    gens := [pair : pair in gens | pair[2] ne 1];
    r := Identity(G);
    for i in [1..word_len] do
        j := Random(1,#gens);
        k := Random(0,gens[j][2]-1);
        r *:= gens[j][1]^k;
    end for;
    return r;
end intrinsic;

intrinsic TestCanonicalPicBases(ZFV::AlgEtQOrd)
{The algorithm for computing the Picard group of S uses randomness; here we check that two different runs of PicardGroup(S) yield the same choice of generators out of CanonicalPicBases.
Note that this will pull back large ideals if the Picard group is large, so is probably best restricted to small Pic(S)
}
    t0:=Cputime();
    oo := OverOrders(ZFV);
    printf "Finished computing %o overorders in %os\n", #oo, Cputime()-t0; t0:=Cputime();
    pics := [* *];
    pmaps1 := [* *];
    for S in oo do
        t0 := Cputime();
        P, pmap := PicardGroup(S);
        printf "Finished computing Picard group %o in %os\n", AbelianInvariants(P), Cputime()-t0; t0:=Cputime();
        Append(~pics, P);
        Append(~pmaps1, pmap);
    end for;
    G1 := CanonicalPicBases(ZFV);
    printf "Finished computing canonical basis in %o\n", Cputime()-t0; t0:=Cputime();
    pmaps2 := [* *];
    for i in [1..#oo] do
        P := pics[i]; pmap := pmaps1[i];
        A := AutomorphismGroup(P);
        printf "Finished computing automorphism group in %o\n", Cputime()-t0; t0:=Cputime();
        a := Random(A);
        pmap2 := a * pmap;
        Append(~pmaps2, pmap2);
        S := oo[i];
        S`PicardGroup := <P, pmap2>;
        printf "Finished resetting Picard group in %o\n", Cputime()-t0; t0:=Cputime();
    end for;
    G2 := CanonicalPicBases(ZFV);
    for i in [1..#oo] do
        G12 := [(G2[i][j] @ pmaps2[i] @@ pmaps1[i]) : j in [1..#G2[i]]];
        assert G12 eq G1[i];
    end for;
    printf "Test successful in %os: same generators chosen\n", Cputime() - t0;
end intrinsic;

