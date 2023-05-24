/* vim: set syntax=magma :*/

// TODO Merge with polarizations.m ????

// declare attributes AlgEtQOrd : ???
declare attributes AlgEtQOrd: ICM_CanonicalRepresentatives;

import "polarizations.m" : transversal_US_USplus,transversal_USplus_USUSb, is_polarization;

transversal_USplus_USUSb_general:=function(S)
// Given an order S, it returns a transveral in S of the quotient S^*_+/<u\bar(u) : u in S^*> where
// S^*_+ is the subgroups of S^* consisting of totally real totally positive units.
    if not assigned S`transversal_USplus_USUSb then
        // Modify

        US,uS:=UnitGroup(S);
        USplus:=TotallyRealPositiveUnitGroup(S);
        USUSb:=sub< USplus | [ USplus!((g*ComplexConjugate(g))@@uS) : g in [uS(g) : g in Generators(US) ]]>;
        S`transversal_USplus_USUSb:=[ uS(t) : t in Transversal(USplus,USUSb)];
    end if;
    return S`transversal_USplus_USUSb;
end function;

is_weak_eq_same_mult_ring:=function(I,J)
// I and J have the same mult ring, and are defined over it
// Similar to the intrinsic IsWeakEquivalent but returns also the colon ideals
    cIJ:=ColonIdeal(I,J);
    cIJ:=ColonIdeal(J,I);
    id:=cIJ*cJI;
    test:=One(Algebra(I)) in id;
    return test,cIJ,cJI;
end function;

intrinsic ICM_CanonicalRepresentatives(ZFV::AlgEtQOrd) -> SeqEnum[AlgEtQIdl], Assoc
{}
    if assigned ZFV`ICM_CanonicalRepresentatives then
        return Explode(ZFV`ICM_CanonicalRepresentatives);
    end if;
    ans := [];
    icm_lookup := AssociativeArray();
    _ := CanonicalPicBases(ZFV); // sets bases
    for S in OverOrders(ZFV) do
        icm_lookup[S] := AssociativeArray();
        pic_iter := PicIteration(S, CanonicalPicBasis(ZFV) : include_pic_elt:=true);
        pic_iter := [<ZFV!!x[1], x[2], x[3]> : x in pic_iter];
        for WE in WKICM_barCanonicalRepresentatives(S) do
            ZFVWE := ZFV!!WE;
            for trip in pic_iter do
                I, ctr, Pelt := Explode(trip);
                WI := ZFVWE * I;
                icm_lookup[S][<W, Pelt>] := WI;
                Append(~ans, WI);
            end for;
        end for;
    end for;
    ZFV`ICM_CanonicalRepresentatives := <ans, icm_lookup>;
    return ans, icm_lookup;
end intrinsic;

intrinsic ICM_Identify(L::AlgEtQIdl, icm_lookup::Assoc) -> AlgEtQIdl, AlgEtQElt
{Given an ideal L, together with the lookup table output by ICM_CanonicalRepresentatives, returns the canonical representative I in the same class of the ICM as L, together with an element of the etale algebra x so that L = x*I}
    S := MultiplicatorRing(L);
    PS, pS := PicardGroup(S);
    wkS := WKICM_barCanonicalRepresentatives(S);
    for i->W in wkS do
        test_wk, cLW, _ := is_weak_eq_same_mult_ring(S!!L,W);
        if test_wk then
            // cLW=(L:W) is invertible, W*cLW = L
            g := cLW@@pS; // in Pic(S)
            I := icm_lookup[S][<W, g>];
            test, x := IsIsomorphic(L, I); // x*I = L
            assert test;
            return I, x;
        end if;
    end for;
end intrinsic;

intrinsic AllMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=0)->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the canonical representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
}
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    min_isog:=AssociativeArray();
    for I in isom_cl do
        min_isog[I] := AssociativeArray();
        for J in isom_cl do
            min_isog[I][J] := [];
        end for;
    end for;
    for J in isom_cl do
        // J is over ZFV
        Ls := MaximalIntemediateIdeals(J,N*J);
        for L in Ls do
            deg := Index(J, L);
            if degrees cmpne 0 and not (deg in degrees) then
                continue;
            end if;
            I, x := ICM_Identify(L, icm_lookup);
            Append(~min_isog[I][J], <deg, x, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L)
        end for;
    end for;
    return min_isog;
end intrinsic;

intrinsic IsogeniesByDegree(ZFV::AlgEtQOrd, degree_bounds::SeqEnum : important_pairs:=0) -> Assoc
{Given the ZFV order of a squarefree isogeny class, together with a sequence of integers, return an associative array A so that A[I][J][d] consists of all isogenies of degree d from I to J for all integers d dividing any element of degree_bounds.  Each isogeny is stored as a pair <x,L> where x is an element mapping I into J and L = x*I (which is a submodule of J of an appropriate index).}
    // imporant pairs, if given, should be a list of tuples <I,J> of canonical representatives (see note below for how they're used)
    N := LCM(degree_bounds);
    degrees := {};
    proper_degrees := {};
    for B in degree_bounds do
        for d in Divisors(B) do
            if d eq 1 then continue; end if;
            Include(~degrees, d);
            // When looking for isogenies from I to Iv, we only care about isogenies between other ideals in that they help build these.  Since we'll always be composing with an extra minimal isogeny, we can drop the degree bounds for isogenies from I to J when J ne Iv (see keep_degree function below)
            if d eq B then continue; end if;
            Include(~proper_degrees, d);
        end for;
    end for;
    function keep_degree(I,J,d)
        if important_pairs cmpeq 0 or <I,J> in important_pairs then
            return d in degrees;
        else
            return d in proper_degrees;
        end if;
    end function;
    min_isog := AllMinimalIsogenies(ZFV, N : degrees:=degrees);
    isog := AssociativeArray();
    isom_cl:=ICM_CanonicalRepresentatives(ZFV);
    for I in isom_cl do
        isog[I] := AssociativeArray();
        for J in isom_cl do
            isog[I][J] := AssociativeArray();
            for dxL in min_isog[J][I] do
                d, x, L := Explode(dxL);
                if keep_degree(I, J, d) then
                    if not IsDefined(isog[I][J], d) then
                        isog[I][J][d] := [];
                    end if;
                    Append(~isog[I][J][d], <x, L>);
                end if;
            end for;
        end for;
    end for;
    while true do
        added_something := false;
        for J in isom_cl do
            for I in isom_cl do
                for K in isom_cl do
                    for m -> known in isog[I][K] do
                        for yL0 in known do
                            y, L0 := Explode(yL0);
                            for dxL in min_isog[K][J] do
                                d, x := Explode(dxL);
                                dm := d*m;
                                if keep_degree(I, J, dm) then
                                    L := x * L0;
                                    if not IsDefined(isog[I][J], dm) then
                                        isog[I][J][dm] := [<x*y, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M) : M in isog[I][J][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[I][J][dm], <x*y, L>);
                                            added_something := true;
                                        end if;
                                    end if;
                                end if;
                            end for;
                        end for;
                    end for;
                end for;
            end for;
        end for;
        if not added_something then
            break;
        end if;
    end while;
    return isog;
end intrinsic;

intrinsic AllPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes.
//TODO
.}

    all_pols:=AssociativeArray(); // the output
    all_isog:=IsogeniesByDegree(ZFV,degree_bounds : important_pairs:=[ < J , can_reps_of_duals[J][2] > : J in isom_cl ]);
    for J in all_isog do
        Jpols:=AssociativeArray(); // will contain all pols find, indexed by degree.
        S:=MultiplicatorRing(J);
        US_over_USplus:=transversal_US_USplus(S);
        Jv:=TraceDualIdeal(ComplexConjugate(J));
        // I am looking for pol such that pol*J c Jv
        // JJ:=canonical rep of Jv
        test,JJ_to_Jv := IsIsomorphic(Jv,JJ); // JJ*JJ_to_Jv eq Jv
        assert test;
        for d ->isog_J_JJ_d in all_isog[J][JJ] do
            pols_deg_d:=[];
            for f in isog_J_JJ_d do
                isog:=f*JJ_to_JV;
                got_one:=false;
                for v in US_over_USplus do
                    pp:=isog*v;
                    if is_polarization(pp,PHI) then
                        got_one:=true;
                        break v;
                    end if;
                end for;
                if got_one then
                    pols_deg_d cat:= [ pp*t : t in transversal_USplus_USUSb_general(S) ]; // this might contains isomorphic copies
                end if;
            end for;
            pols_deg_d_up_to_iso:={};
            for x0 in pols_deg_d do
                pol,seq:=CanonicalRepresentativePolarizationGeneral(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,seq>); //isomorphic pols will have the same canonical rep
            end for;
            assert forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Jv,pol[1]*J) }; // sanity check
            Jpols[d]:=[ < pol[1] , pol[2] , DecompositionKernelOfIsogeny(J,Jv,pol[1]) > : pol in pols_deg_d_up_to_iso ];
        end for;
        all_pols[J]:=Jpols;
    end for;
    return all_pols;
end intrinsic;

intrinsic CanonicalRepresentativePolarizationGeneral(I::AlgEtQIdl,x0::AlgEtQElt) -> AlgEtQElt,SeqEnum[FldRatElt]
{Given an ideal I and an element x0 representing a polarization for I, we want to look at the set x0*u*\bar(u) where u runs over the units of (I:I)=S. We compute the image of this set via the Log map. We use ShortestVectors on this lattice, pullback the output in the algebra, computhe the action of the torsion units of S on these elements, represent them with respect to [V^(g-1),...,V,1,F,...,F^g], sort them with respec to the lexigographic order of their coefficients and take the smallest.}
// this is very similar to the code of CanonicalRepresentativePolarization
    S:=MultiplicatorRing(I);
    test,Sb:=IsConjugateStable(S);
    if test then 
        return CanonicalRepresentativePolarization(I,x0);
    end if;

    A:=Algebra(x0);
    g:=Dimension(A) div 2;
    F:=PrimitiveElement(A);
    q:=Truncate(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];

    if g eq #Components(A) then // then sub below would be the trivial group and the code would not modify x0. Early exit
        y0 := AbsoluteCoordinates([x0],basis);
        den := LCM([Denominator(c) : c in y0[1]]);
        nums := [den * c : c in y0[1]];
        return x0, den, nums;
    end if;

    homs:=HomsToC(A); 
    prec:=Precision(Codomain(homs[1]));
    // are the homs sorted in conjugate pairs?
    assert forall{ k : k in [1..g] | Abs(homs[2*k-1](F) - ComplexConjugate(homs[2*k](F))) lt 10^-(prec div 2)};

    homs:=[homs[2*k-1] : k in [1..g]]; //one per conjugate pair to define the Log map

    // this bit is different from CanonicalRepresentativePolarization
    SSb:=S*Sb; // the smallest order containing both S and Sb
    U,u:=UnitGroup(SSb);
    US,uS:=UnitGroup(S);
    gens_US:=[ uS(g) : g in Generators(US) ];
    sub:=sub< U | [(g*ComplexConjugate(g))@@u : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
    gens_sub:=[ u(g) : g in Generators(sub) ];
    // end of differences, except gens_sub_inS has been renamed to gens_sub (since they are in SSb, not necessarily in S).


    rnk_sub:=#gens_sub;
    assert rnk_sub eq g-#Components(A);
    img_gens_sub:=Matrix([[ Log(Abs(h(g))) : h in homs ] : g in gens_sub ]); // apply Log map
    L:=Lattice(img_gens_sub);
    img_x0:=Vector([ Log(Abs(h(x0))) : h in homs ]);
    closest_vects:=ClosestVectors(L,-img_x0); //note the minus sign!
    all_coords:=[ Coordinates(cv) : cv in closest_vects];
    candidates:=[ x0*&*[ gens_sub[i]^coord[i] : i in [1..rnk_sub] ] : coord in all_coords ]; 
    // A priori, I believe that I should act on candidates with the torsion units of the totally real totally positive units in S
    // But there is only 1 (which also the torsion subgroup of sub = < u*\bar u>

    // Now, I sort the candidats with respect to lexicographic order of the coefficients wrt to [V^(g-1),...,V,1,F,...,F^g],
    // and take the smallest.
    sort_keys_candidates:=[ AbsoluteCoordinates([c],basis)[1] : c in candidates ];
    ParallelSort(~sort_keys_candidates,~candidates);
    den := LCM([Denominator(c) : c in sort_keys_candidates[1]]);
    nums := [den*c : c in sort_keys_candidates[1]];

    return candidates[1], den, nums;
end intrinsic;
