/* vim: set syntax=magma :*/

declare attributes AlgEtQOrd:CanonicalPicGenerators,CanonicalPicBasis,CanonicalPicBases,BasisBar,TraceDualPic;
// TODO add description of the attributes above.

// TODO add description of the functions below.

function asProdData(S)
    // This function takes as input an order in an etale algebra, and returns several sequences associated to the decomposition of the algebra into fields.
    // - O_asProd is a tuple expressing the maximal order containing S as a direct product of maximal orders of number fields
    // - F_asProd is a tuple expressing the conductor of S as a direct product of ideals in these maximal orders
    // - F_indexes as
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

function MakeOPrime(O, P, O_asProd, i)
    return Ideal(O, <(i eq j) select P else 1*O_asProd[j] : j in [1..#O_asProd]>);
end function;

function MakeSPrime2(S, P)
    return S!!P meet S;
end function;

function MakeSPrime(S, P, O_asProd, i)
    // Construct a prime of S given a prime P in position i of the product decomposition O_asProd of the maximal order
    O := MaximalOrder(Algebra(S));
    return MakeSPrime2(S, MakeOPrime(O, P, O_asProd, i));
end function;

function CanonicalPrimeIdealsOverPrime(i, p, S, O_asProd, F_asProd, F_indexes)
    OL := O_asProd[i];
    FL := F_asProd[i];
    Find := F_indexes[i];
    L := NumberField(OL);
    Lp := PrimeIdealsOverPrime(L, p);
    if Find mod p eq 0 then
        // Remove primes dividing the conductor
        Lp := [I : I in Lp | One(OL) in I+FL];
    // in the other case, we keep the last element, even though its lift is automatically in the span of the others, since it might have a better order
    end if;
    if #Lp eq 0 then
        return [];
    end if;
    OLp := [OL!!(Lp[1])];
    SLp := [MakeSPrime(S, Lp[1], O_asProd, i)];
    seen := {SLp[1]}; // we only care about the intersection with Z[F,V], and there will be collisions between primes of the maximal order
    for j in [2..#Lp] do
        Sprime := MakeSPrime(S, Lp[j], O_asProd, i);
        if not Sprime in seen then
            Append(~SLp, Sprime);
            Append(~OLp, OL!!(Lp[j]));
        end if;
    end for;
    if #SLp gt 1 then
        // Sort using the LMFDB label
        keys := [<StringToInteger(c) : c in Split(LMFDBLabel(OLp[z]), ".")> cat <z> : z in [1..#OLp]];
        Sort(~keys);
        SLp := [SLp[key[#key]] : key in keys];
    end if;
    return SLp;
end function;

intrinsic CanonicalPicGenerators(S::AlgEtQOrd) -> SeqEnum, SeqEnum, SeqEnum
{
//TODO
}
    if assigned S`CanonicalPicGenerators then
        return Explode(S`CanonicalPicGenerators);
    end if;
    P, pmap := PicardGroup(S);
    Pgens := [];
    construction := [];
    ideals := [];
    if #P eq 1 then
        S`CanonicalPicGenerators := <Pgens, construction>;
        return Pgens, construction;
    end if;
    O_asProd, F_asProd, F_indexes := asProdData(S);
    primes_above_p := AssociativeArray();
    primes_by_norm := [];
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
                primes_above_p[<i, p>] := CanonicalPrimeIdealsOverPrime(i, p, S, O_asProd, F_asProd, F_indexes);
            end for;
        end if;
        for i in [1..#O_asProd] do
            for pcnt->Sprime in primes_above_p[<i,p>] do
                // create a Oprime = \prod_j prime if i eq j else 1
                // where Norm(Oprime) = q = p^k
                if Index(S, Sprime) eq q then
                    plift := Sprime@@pmap;
                    if #sub<P|Pgens cat [plift]> gt #Psub then
                        Append(~Pgens, plift);
                        Append(~construction, <i, p, pcnt, Order(plift)>);
                        Append(~ideals, Sprime);
                        Psub := sub<P|Pgens>;
                        if #Psub eq #P then
                            S`CanonicalPicGenerators := <Pgens, construction>;
                            return Pgens, construction;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end while;
end intrinsic;

intrinsic CanonicalPicPrimaryBasis(ZFV::AlgEtQ) -> SeqEnum
{Produces a deterministically chosen primary abelian basis for Pic(ZFV)}
    return [];
end intrinsic;

intrinsic CanonicalPicGenerators(S::AlgEtQOrd, construction::SeqEnum) -> SeqEnum
{A version that produces the canonical generators using the saved construction, and returned as prime ideals in the maximal order of S together with their orders in Pic(S) (so that the computation of Pic(S) isn't required).
Note that the returned generators are not independent; see CanonicalPicBasis.
//TODO what is the 'saved construction'?
}
    O_asProd, F_asProd, F_indexes := asProdData(S);
    O := MaximalOrder(Algebra(S));
    gens := [];
    primes_above_p := AssociativeArray();
    for quad in construction do
        i, p, pcnt, ord := Explode(quad);
        if not IsDefined(primes_above_p, <i,p>) then
            primes_above_p[<i,p>] := CanonicalPrimeIdealsOverPrime(O_asProd[i], p, F_asProd[i], F_indexes[i]);
        end if;
        Lp := primes_above_p[<i,p>];
        Append(~gens, MakeOPrime(O, Lp[pcnt], O_asProd, i));
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
{Takes as input an order S in an etale algebra and a sequence gens of generators of Pic(S), and returns a basis of Pic(S) (aligning with the structure described by AbelianInvariants(Pic(S))).
//TODO there are two outputs. What is the second one?
}
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
                            cons := &+[c[#c+1-j] * Con.(tt[j]) : j in [1..#tt]];
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

intrinsic CanonicalPicBases(ZFV::AlgEtQOrd) -> List, List, List, List
{Find an abelian basis for the Picard group of each overorder of ZFV using a deterministic method.
//TODO Document the 'deterministic method'.
}
    if assigned ZFV`CanonicalPicBases then
        return Explode(ZFV`CanonicalPicBases);
    end if;
    vprint User1: "Starting OverOrders"; t0 := Cputime();
    oo := OverOrders(ZFV);
    vprint User1: "OverOrders finished", Cputime() - t0;
    j := Index(oo, ZFV);
    vprint User1: "Starting PicardGroup"; t0 := Cputime();
    P0, pmap0 := PicardGroup(ZFV);
    vprint User1: "PicardGroup finished", Cputime() - t0; t0 := Cputime();
    ZFVgens, gens_construction, gen_ideals := CanonicalPicGenerators(ZFV);
    vprint User1: "CanonicalPicGenerators finished", Cputime() - t0; t0:=Cputime();
    igens := [pmap0(P0.k) : k in [1..Ngens(P0)]];
    vprint User1: "igens finished", Cputime() - t0;
    bases := [* *];
    basis_constructions := [* *];
    pic_maps := [* *];
    basis_ideals := [* *];
    for i->S in oo do
        if i eq j then
            Sgens := ZFVgens;
            P := P0;
            P0Pmap := IdentityHomomorphism(P);
        else
            vprint User1: "Starting PicardGroup", i; t0:=Cputime();
            P, pmap := PicardGroup(S);
            vprint User1: "PicardGroup finished", Cputime() - t0; t0:=Cputime();
            // S!!igens[i] isn't prime, but that's fine: these still generate.
            P0Pmap := hom<P0 -> P | [<P0.k, (S!!igens[k]) @@ pmap> : k in [1..Ngens(P0)]]>;
            Sgens := [P0Pmap(g) : g in ZFVgens];
            vprint User1: "Sgens finished", Cputime() - t0; t0:=Cputime();
        end if;
        basis, bcon := GensToBasis(oo[i], Sgens);
        assert &and[Parent(b) eq P : b in basis];
        Append(~bases, basis);
        Append(~basis_constructions, bcon);
        Append(~pic_maps, P0Pmap);
        Sideals := [S!!gen_ideals[u] : u in [1..#gen_ideals]];
        Append(~basis_ideals, [&*[Sideals[u]^bcon[2][v][u] : u in [1..#gen_ideals]] : v in [1..#basis]])
    end for;
    ZFV`CanonicalPicBases := <bases, basis_constructions, pic_maps, basis_ideals>;
    for i in [1..#oo] do
        S := oo[i];
        P := PicardGroup(S);
        assert &and[Parent(b) eq P : b in bases[i]];
        S`CanonicalPicBasis := <bases[i], basis_constructions[i], pic_maps[i], basis_ideals[i]>;
    end for;
    return bases, basis_constructions, pic_maps, basis_ideals;
end intrinsic;

intrinsic CanonicalPicBasis(S::AlgEtQOrd) -> SeqEnum, SeqEnum, Map
{
//TODO
    }
    if not assigned S`CanonicalPicBasis then
        error "You must first call CanonicalPicBases(ZFV) on the Frobenius order ZFV";
    end if;
    return Explode(S`CanonicalPicBasis);
end intrinsic;

intrinsic CanonicalPicBasis(S::AlgEtQOrd, gens::SeqEnum, basis_info::Tup) -> SeqEnum
{Given an order S, a sequence gens of ideals of the maximal order of S (as output by CanonicalPicGenerators(ZFV, gen_info)) that generate Pic(ZFV), and basis_info as output by the other version of CanonicalPicBasis, return a sequence of ideals of S that forms a basis for Pic(S)}
    invs, construction := Explode(basis_info);
    assert &and[#cons eq #gens : cons in construction];
    basis := [&*[gens[j]^construction[i][j] : j in [1..#gens]] : i in [1..#construction]];
    return [MakeSPrime2(S, b) : b in basis];
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
{
//TODO
    }
    coeffs := IntToInvVec(pos - 1, invs);
    assert #coeffs eq #basis;
    return &*[basis[j]^coeffs[j] : j in [1..#basis]];
end intrinsic;

intrinsic IdealFromPosition(pos::RngIntElt, ZFV::AlgEtQOrd, S::AlgEtQOrd, gen_info::SeqEnum, basis_info::Tup) -> AlgEtQIdl
{Given a an integer pos between 1 and #Pic(S) and saved information, computes an ideal that is equivalent in the Picard group to the one produced in position pos in the iteration.
gen_info - second part of output of CanonicalPicGenerators(ZFV) //TODO I don't understand this line
//TODO what are gen_info and basis_info
Note that if you're calling this for many different pos, it's probably better to compute gens and basis and use another form of IdealFromPosition.
//TODO What are 'gens' and 'basis'. How do I compute them?
}
    gens := CanonicalPicGenerators(ZFV, gen_info);
    invs, construction := Explode(basis_info);
    basis := CanonicalPicBasis(S, gens, basis_info);
    return IdealFromPosition(pos, basis, invs);
end intrinsic;

intrinsic CanonicalPicardGroup(S::AlgEtQOrd) -> GrpAb, Map
{A version of PicardGroup, with the same semantics, but not depending on any random choices and stable across changes to Magma.  You must call CanonicalPicBases on ZFV first.}
    P, pmap := PicardGroup(S);
    basis, bcon, _, ideals := CanonicalPicBasis(S);
    invs, con := Explode(bcon);
    A := AbelianGroup(invs);
    AtoP := iso<A->P|basis>;
    new_pmap := map<P->Codomain(pmap)| rep:->&*[basis[i]^v[i] : i in [1..#basis]] where v:=Eltseq(rep@@AtoP),
                                       id:->id@@pmap>;
end intrinsic;

intrinsic PicIteration(S::AlgEtQOrd, basis::SeqEnum : filter:=0, include_pic_elt:=false) -> SeqEnum
{Iterates over the elements of the Picard group in a consistent order, using a filter function on Pic(S).  basis_info should be an entry in the *first* part of the output of CanonicalPicBases(S), and filter should take a single element of Pic(S) as input and return a boolean (the ideal is included if the output is true).  The output is a sequence of pairs <I,i>, where I is an ideal and i is the index of that ideal in the overall iteration.
// TODO the output consists of triples if include_pic_elt is true. Please add a comment about this vararg.
// TODO Is the Ideal in the output canonical? It should be for our purposes.
}
    P, pmap := PicardGroup(S);
    assert assigned S`PicardGroup;
    if #P eq 1 then
        if filter cmpeq 0 or filter(P.0) then
            if include_pic_elt then
                return [<OneIdeal(S), 1, P.0>];
            end if;
            return [<OneIdeal(S), 1>];
        else
            return [];
        end if;
    end if;
    invs := AbelianInvariants(P);
    vprint User1: "Iterating over Pic(S) with invariants", invs;
    coeffs := [0 : i in invs];
    ans := [];
    ctr := 1;
    Pelt := P.0; // identity
    Piter := [&+basis[i..#basis] : i in [1..#basis]];
    while true do
        if filter cmpeq 0 or filter(Pelt) then
            if include_pic_elt then
                Append(~ans, <pmap(Pelt), ctr, Pelt>);
            else
                Append(~ans, <pmap(Pelt), ctr>);
            end if;
        end if;
        pos := #coeffs;
        while true do
            if pos eq 0 then
                return ans;
            elif coeffs[pos] ne invs[pos] -1 then
                coeffs[pos] +:= 1;
                break;
            end if;
            coeffs[pos] := 0;
            pos -:= 1;
        end while;
        Pelt +:= Piter[pos];
        ctr +:= 1;
    end while;
end intrinsic;

intrinsic BasisBar(S::AlgEtQOrd) -> SeqEnum
{Returns the conjugates of the non-canonical basis elements.}
    if assigned S`BasisBar then
        return S`BasisBar;
    end if;
    assert IsConjugateStable(S);
    P, pmap := PicardGroup(S);
    bars := [ComplexConjugate(pmap(P.i)) @@ pmap : i in [1..Ngens(P)]];
    S`BasisBar := bars;
    return bars;
end intrinsic;

intrinsic TraceDualPic(S::AlgEtQOrd) -> SeqEnum
{
//TODO
}
    if assigned S`TraceDualPic then
        return S`TraceDualPic;
    end if;
    assert IsGorenstein(S);
    P, pmap := PicardGroup(S);
    tdp := TraceDualIdeal(S) @@ pmap;
    S`TraceDualPic := tdp;
    return tdp;
end intrinsic;

intrinsic PPolPossIteration(S::AlgEtQOrd) -> SeqEnum
{Called internally from PPolIteration
//TODO what does it do?
}
    vprint User1: "Looking up canonical Pic basis";
    basis := CanonicalPicBasis(S);
    if IsGorenstein(S) and IsConjugateStable(S) and #PicardGroup(S) gt 1 then
        basisbar := BasisBar(S);
        tdp := TraceDualPic(S);
        function bar(x)
            coeffs := Eltseq(x);
            assert #coeffs eq #basisbar;
            if #coeffs eq 0 then return PicardGroup(S).0; end if;
            return &+[coeffs[i] * basisbar[i] : i in [1..#coeffs]];
        end function;
        function filter(x)
            return x + bar(x) eq tdp;
        end function;
        vprint User1: "Iterating with trick";
        return PicIteration(S, basis : filter:=filter);
    else
        vprint User1: "Iterating without trick";
        return PicIteration(S, basis);
    end if;
end intrinsic;

intrinsic PPolIteration(ZFV::AlgEtQOrd) -> List
{Given the Frobenius order, returns a list of quadruples <we, pic_ctr, I, pol>, where I is an ideal in the weak equivalence class we with picard group counter pic_ctr, and pol is the reduced principal polarization for I.
//TODO as of now, I is canonical only up to iso. To be fixed.
}
    A := Algebra(ZFV);
    vprint User1: "Computing CM type..."; t0 := Cputime();
    prec := 30;
    while true do
        try
            PHI:=pAdicPosCMType(A);
            break;
        catch e // precision error can happen
            prec *:= 2;
        end try;
    end while;
    vprint User1: Sprintf("Done with CM type in %o; computing canonical bases...", Cputime(t0)); t0 := Cputime();
    bases := CanonicalPicBases(ZFV); // sets CanonicalPicBasis for overorders
    vprint User1: Sprintf("Done computing canonical Pic bases in %o; starting through over orders", Cputime(t0)); t0 := Cputime();
    ans := [* *];
    for Sctr->S in OverOrders(ZFV) do
        know_no_PP := not IsConjugateStable(S) or exists{ P : P in NonGorensteinPrimes(S) | IsConjugateStable(P) and CohenMacaulayTypeAtPrime(S,P) eq 2 };
        if know_no_PP then
            vprint User1: "Skipping over order #", Sctr;
            continue;
        end if; // if true, there can't be any PPAV with this endomorphism ring
        vprint User1: "Computing WKICM_bar for over order #", Sctr;
        wkimS := WKICM_bar(S);
        vprint User1: Sprintf("Done computing WKICM_bar at %o; computing possible picard iteration", Cputime(t0));
        ppol_poss := PPolPossIteration(S);
        vprint User1: Sprintf("Done computing picard iteration at %o; iterating", Cputime(t0));
        for WE in wkimS do
            we := WELabel(WE);
            for tup in ppol_poss do
                I, pic_ctr := Explode(tup);
                WEI := WE * I;
                vprint User1: Sprintf("Computing principal polarizations at %o", Cputime(t0));
                pp := PrincipalPolarizations(WEI, PHI);
                vprint User1: Sprintf("Done computing principal polarizations at %o; iterating", Cputime(t0));
                for pol in pp do
                    _, den, nums := CanonicalRepresentativePolarization(WEI, pol);
                    vprint User1: Sprintf("Done computing canonical representative at %o", Cputime(t0));
                    Append(~ans, <we, pic_ctr, I, den, nums>);
                end for;
            end for;
        end for;
    end for;
    return ans;
end intrinsic;

intrinsic Random(G::GrpAuto : word_len:=40) -> GrpAutoElt
{
//TODO
    }
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
Note that this will pull back large ideals if the Picard group is large, so is probably best restricted to small Pic(S).}
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

/*
    TODO Add a list of tests:
        - are the canonical gens chosen consistently?
        - is the sorting of PicIteration consistent?
        - are the canonical ideal reps chosen consistently?


*/
