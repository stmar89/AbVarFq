/* vim: set syntax=magma :*/

// TODO Merge with polarizations.m ????

// declare attributes AlgEtQOrd : ???

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

intrinsic AllMinimalIsogeniesTo(ZFV::AlgEtQOrd , N :: RngIntElt)->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the canonical representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
}
    isom_cl:=ICM(ZFV); // TODO use canonical reps
    all_min_isog_to:=AssociativeArray();
    for J in isom_cl do
        // J is over R
        Ls:=MaximalIntemediateIdeals(J,N*J);
        MinimalIsogeniesToJ:=AssociativeArray();
        for I in isom_cl do
            MinimalIsogeniesToJ[I] := [];
        end for;
        for L in Ls do
            deg:=Index(J,L);
            S:=MultiplicatorRing(L);
            PS,pS:=PicardGroup(S); // TODO this should be with canonical generators of Pic (with DLP)
            wkS:=WKICM_bar(S);
            for i in [1..#wkS] do
                W:=wkS[i]; // we assume here that W is a canonical representative of its weak equivalence class
                test_wk,cLW,_:=is_weak_eq_same_mult_ring(S!!L,W) 
                if test_wk then
                    // cLW=(L:W) is invertible, W*cLW = L
                    g:=cLW@@pS; // in Pic(S)
                    // TODO produce label of (W,g)
                    test,x:=IsIsomorphic(cLW,pS(g)); // x*pS(g) = cLW
                    assert test;
                    //if not IsDefined(MinimalIsogeniesToJ,<W,g>) then
                    //    MinimalIsogeniesToJ[<W,g>]:=[];
                    //end if;
                    Append(~MinimalIsogeniesToJ[<W,g>],<deg,x>); // TODO: Change <W,g> index to I; might want to store L and S
                                                                 // W*cLW = L c J, x*W*pS(g) = W*cLW = L c J, 
                                                                 // so x is a minimal isogeny from I:=W*pS(g) to J of degree deg=J/L 
                                                                 // we might want to replace W,g in the tuble with the label of 
                                                                 // W*pS(g)=:I which is the canonical representative of 
                                                                 // the corresponding isomorphism class
                    break i;
                end if;
            end for;
        end for;
        all_min_isog_to[J]:=MinimalIsogeniesToJ;
    end for;
end intrinsic;

intrinsic AllPolarizations( ZFV :: AlgEtQOrd , PHI :: AlgEtQCMTYpe , N::RngIntElt : max_depth:=2 )->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic posirive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes. The entry indexed by J will contain all polarizations that are composition of at most "max_depth" minimal isogenies, where "max_depth" is passed as a var arg (default value 2), the isogenies have degree bounded by the integer N, minimal means that it cannot be factor into a composition of two isogenies of degree gt than 1.}

    A:=Algebra(ZFV);
    all_min_isog_to:=AllMinimalIsogeniesTo(ZFV, N);
    all_pols:=AssociativeArray();
    isom_cl:= //canonical reps of ICM(ZFV);

    // we init the output 
    for Jv in isom_cl do
        Jpols:=AssociativeArray(); // will contain all pols find, sorted by degree.
        all_pols[Jv]):=Jpols;
    end for;
    
    can_reps_of_duals:=AssociativeArray();
    for Jv in isom_cl do
        J:=TraceDualIdeal(ComplexConjugate(Jv));
        // I am looking for pol such that pol*J c Jv
        // JJ:=canonical rep of J
        test,J_to_JJ := IsIsomorphic(JJ,J); // this is sort of depth = 0, i.e. principal polarizations.
                                            // since we have already run this code we don't test if we get polarizations.
        assert test;
        S:=MultiplicatorRing(J);
        can_reps_of_duals[Jv] := < J,JJ,S,J_to_JJ >;  
    end for;

    for current_depth in [1..max_depth] do
        for Jv in isom_cl do
            Jpols:=all_pols[Jv];
            J,JJ,S,J_to_JJ := Explode(can_reps_of_duals[Jv]);
            cc := [<JJ,1,[J_to_JJ]>]; // JJ is the canonical representative for J
            for d in [1..current_depth-1] do
                newcc := [];
                for triple in cc do
                    I, d, flist := Explode(triple);
                    if d lt current_depth then
                        for II in isom_cl do
                            for g in all_min_isog_to[II][I] do
                                Append(~newcc, <II, d*g[1], flist cat [g[2]]>);
                            end for;
                        end for;
                    else
                    // at d = current_depth we want an isogeny landing in Jv
                        for g in all_min_isog_to[Jv][I] do
                            Append(~newcc, <Jv, d*g[1], flist cat [g]>);
                        end for;
                    end if;
                end for;
                cc := newcc;
            end for;
            // now we check if the concatented isogenies give polariations
            for triple in cc do
                _,d,flist := Explode(triple);
                isog:=&*flist;
                assert Index(Jv,isog*J) eq d;
                US_over_USplus:=transversal_US_USplus(S);
                got_one:=false;
                for v in US_over_USplus do
                    pp:=isog*v;
                    if is_polarization(pp,PHI) then
                        got_one:=true;
                        break v;
                    end if;
                end for;
                if got_one then
                    if not IsDefined(Jpols,d) then
                        Jpols[d]:=[];
                    end if;
                    Jpols[d] cat:= [ pp*t : t in transversal_USplus_USUSb_general(S) ]; // this might contains isomorphic copies
                end if;
            end for;
            all_pols[Jv]:=Jpols; 
        end for; 
    end for;

    for Jv in isom_cl do
        Jpols:=all_pols[Jv];
        keys:=Sort(Setseq(Keys(Jpols)); 
        for d in keys do
            Jpols[d]:=Setseq(Seqset([ CanonicalRepresentativePolarizationGeneral(J,x0) : x0 in Jpols[d] ])); 
                // remove isomorphic pols by computing the canonical rep for each one and removing duplicates
            assert forall{ pol : pol in Jpols[d] | d eq Index(Jv,pol*J) }; // sanity check
        end for;
        // TODO add kernels????
        all_pols[Jv]:=Jpols; 
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
