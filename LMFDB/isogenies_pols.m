/* vim: set syntax=magma :*/

// TODO Merge with polarizations.m ????
//

declare verbose AllPolarizations,1;

// declare attributes AlgEtQOrd : ???
declare attributes AlgEtQOrd: ICM_CanonicalRepresentatives, RepresentativeMinimalIsogeniesTo;
declare attributes AlgEtQIdl: IsomLabel, WErep, PElt;

import "polarizations.m" : transversal_US_USplus,transversal_USplus_USUSb, is_polarization;

transversal_USplus_USUSb_general:=function(S)
// Given an order S, it returns a transveral in S of the quotient S^*_+/<u\bar(u) : u in S^*> where
// S^*_+ is the subgroups of S^* consisting of totally real totally positive units.
// It is very similar to transversal_USplus_USUSb, but works also when S is no conjugate stable.
    if not assigned S`transversal_USplus_USUSb then
        test,Sb:=IsConjugateStable(S);
        if test then
            _:=transversal_USplus_USUSb(S); // this caches the attribute
        else
            SSb:=S*Sb; // the smallest order containing both S and Sb
            U,u:=UnitGroup(SSb);
            US,uS:=UnitGroup(S);
            gens_US:=[ uS(g) : g in Generators(US) ];
            USUSb:=sub< U | [(g*ComplexConjugate(g))@@u : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
            USplus:=TotallyRealPositiveUnitGroup(S);
            USplus_USUSb:=sub<U | [ (uS(g))@@u : g in Generators(USplus) ] cat Setseq(Generators(USUSb)) >;
            USUSb:=sub< USplus_USUSb | [ USplus_USUSb!g : g in Generators(USUSb) ]>;
            S`transversal_USplus_USUSb:=[ u(t) : t in Transversal(USplus_USUSb,USUSb)];
        end if;
    end if;
    return S`transversal_USplus_USUSb;
end function;

is_weak_eq_same_mult_ring:=function(I,J)
// I and J have the same mult ring, and are defined over it
// Similar to the intrinsic IsWeakEquivalent but returns also the colon ideals
    cIJ:=ColonIdeal(I,J);
    cJI:=ColonIdeal(J,I);
    id:=cIJ*cJI;
    test:=One(Algebra(I)) in id;
    return test,cIJ,cJI;
end function;

// TODO move the next intrisic to a different package?
intrinsic ICM_CanonicalRepresentatives(ZFV::AlgEtQOrd) -> SeqEnum[AlgEtQIdl], Assoc
{Given the Frobenius order of a squafree isogeny class it returns the canonical representatives of the isomorphsim classes. Each ideal has a label attached to it.}
    if assigned ZFV`ICM_CanonicalRepresentatives then
        return Explode(ZFV`ICM_CanonicalRepresentatives);
    end if;
    ans := [];
    icm_lookup := AssociativeArray();
    _ := CanonicalPicBases(ZFV); // sets bases
    for S in OverOrders(ZFV) do
        basis, _, proj := CanonicalPicBasis(S);
        icm_lookup[S] := AssociativeArray();
        pic_iter := PicIteration(S, basis : include_pic_elt:=true);
        pic_iter := [<ZFV!!x[1], x[2], x[3]> : x in pic_iter];
        for WE in WKICM_barCanonicalRepresentatives(S) do
            ZFVWE := ZFV!!WE;
            for trip in pic_iter do
                I, ctr, Pelt := Explode(trip);
                WI := ZFVWE * I;
                if assigned WE`WELabel then
                    WI`IsomLabel := Sprintf("%o.%o", WE`WELabel, ctr);
                end if;
                WI`WErep := ZFVWE;
                WI`Pelt := Pelt@@proj;
                icm_lookup[S][<WE, Pelt>] := WI;
                Append(~ans, WI);
            end for;
        end for;
    end for;
    ZFV`ICM_CanonicalRepresentatives := <ans, icm_lookup>;
    return ans, icm_lookup;
end intrinsic;

// TODO move the next intrisic to a different package?
intrinsic ICM_Identify(L::AlgEtQIdl, icm_lookup::Assoc) -> AlgEtQIdl, AlgEtQElt, AlgEtQOrd, AlgEtQIdl, GrpAbElt
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
            return I, x, S, W, g;
        end if;
    end for;
end intrinsic;

intrinsic CanonicalCosetRep(g::GrpAbElt, H::GrpAb) -> GrpAbElt, GrpAb
{Given an element g and a subgroup H of an ambient abelian group G, finds a canonically chosen representative of g+H (and also returns H itself for convenience).  The output only depends on g+H.}
    if Order(g) eq 1 then
        return g, H;
    end if;
    G := Parent(g);
    if (#H)^2 le #G then
        // iterate over H and find the smallest element
        best := g; first := Eltseq(g);
        for h in H do
            eh := Eltseq(h);
            if eh lt first then
                best := h;
                first := eh;
            end if;
        end for
        return best, H;
    else
        // iterate over G until you find an element of g+H
        for h in G do
            // iterating over abelian groups happens in a strange order, but that's okay for us as long as it's consistent.
            if h - g in H then
                return h;
            end if;
        end for;
    end if;
end intrinsic;


//TODO The code of the next few intrinsic is very complicated (eg many nested for loops). Needs more explaination.

intrinsic RepresentativeMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=[])->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the canonical representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
}
    if not assigned ZFV`RepresentativeMinimalIsogeniesTo then
        ZFV`RepresentativeMinimalIsogeniesTo := AssociativeArray();
    end if;
    if IsDefined(ZFV`RepresentativeMinimalIsogeniesTo, <N, degrees>) then
        return ZFV`RepresentativeMinimalIsogeniesTo[<N, degrees>];
    end if;
    if not assigned ZFV`CanonicalPicBases then
        _ = CanonicalPicBases(ZFV);
    end if;
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    // It should be possible to implement this function without enumerating the whole ICM, but instead just enumerating weak equivalence classes.
    // But we need to call ICM_Identify, which currently relies on the lookup table constructed in ICM_CanonicalRepresentatives, so we don't try to do this now.
    min_isog := AssociativeArray();
    we_reps := &cat[[icm_lookup[S][<WE, P.0>] : WE in WKICM_barCanonicalRepresentatives(S) where P := PicardGroup(S)] : S in OverOrders(ZFV)];
    we_hashes := [myHash(J) : J in we_reps];
    for i->I in we_reps do
        min_isog[we_hashes[i]] := AssociativeArray();
        for j->J in we_reps do
            min_isog[we_hashes[i]][we_hashes[j]] := [];
        end for;
    end for;
    for J in isom_cl do
        S := MultiplicatorRing(J);
        P := PicardGroup(S);
        _, _, P0Pmap := CanonicalPicBasis(S);
        WE := J`WErep;
        hshJ := myHash(J);
        Ls := MaximalIntermediateIdeals(J, N*J);
        for L in Ls do
            deg := Index(J, L);
            if degrees ne [] and not (deg in degrees) then
                continue;
            end if;
            I, x, IS, IWE, Ig := ICM_Identify(L, icm_lookup);
            assert2 Index(J, x*I) eq deg;
            Ig, Ker := CanonicalCosetRep(Ig@@P0Pmap, Kernel(P0Pmap));
            Append(~min_isog[myHash(IWE)][hshJ], <deg, x, Ig, Ker, I, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L); I = IWE * Ig as canonical representatives
        end for;
    end for;
    ZFV`RepresentativeMinimalIsogeniesTo[<N, degrees>] := min_isog;
    return min_isog;
end intrinsic;

intrinsic RepresentativeIsogenies(ZFV::AlgEtQOrd, degree_bounds::SeqEnum)->Assoc
{}
    N := LCM(degree_bounds);
    degrees := {};
    for B in degree_bounds do
        for d in Divisors(B) do
            if d eq 1 then continue; end if;
            Include(~degrees, d);
        end for;
    end for;
    t0:=Cputime();
    min_isog := RepresentativeMinimalIsogenies(ZFV, N : degrees:=degrees);
    vprintf AllPolarizations : "time spent on AllMinimalIsogenies %o\n",Cputime(t0);
    isog := AssociativeArray();
    isom_cl, icm_lookup :=ICM_CanonicalRepresentatives(ZFV);
    we_reps := &cat[[icm_lookup[S][<WE, P.0>] : WE in WKICM_barCanonicalRepresentatives(S) where P := PicardGroup(S)] : S in OverOrders(ZFV)];
    we_hashes := [myHash(J) : J in we_reps];
    we_proj := &cat[[P0Pmap : WE in WKICM_barCanonicalRepresentatives(S) where _,_,P0Pmap := CanonicalPicBasis(S)] : S in OverOrders(ZFV)];
    isog := AssociativeArray();
    while true do
        added_something := false;
        for i->I in we_reps do
            hshI := we_hashes[i]; projI := we_proj[i];
            SI := MultiplicatorRing(I);
            for j->J in we_reps do
                hshJ := we_hashes[j]; projJ := we_proj[j];
                for k->K in we_reps do
                    hshK := we_hashes[k]; projK := we_proj[k];
                    for m->known in isog[hshK][hshJ] do
                        for yL0 in known do
                            y, g, G, L0 := Explode(yL0);
                            for data in min_isog[hshI][hshK] do
                                d, x, h, H := Explode(data);
                                if d*m in degrees then
                                    gh, GH := CanonicalCosetRep(g+h, G+H);
                                    I0 := icm_lookup[SI][<I, projI(gh)>];
                                    xy := x*y;
                                    L := (xy) * I0;
                                    if not IsDefined(isog[hshI][hshJ], dm) then
                                        isog[hshI][hshJ][dm] := [<xy, gh, GH, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M[4]) : M in isog[hshI][hshJ][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[hshI][hshJ][dm], <xy, gh, GH, L>);
                                            assert2 Index(J, L) eq dm;
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

intrinsic NonprincipalPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes.
//TODO
.}
    t_tot := Cputime();
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    can_reps_of_duals := AssociativeArray();
    all_pols := AssociativeArray(); // the output
    t0 := Cputime();
    isog := RepresentativeIsogenies(ZFV, degree_bounds);
    vprintf AllPolarizations : "time spent on IsogeniesByDegree: %o\n", Cputime(t0);
    t_can := 0;
    for I in isom_cl do
        // I am looking for pol such that pol*I c Iv
        S := MultiplicatorRing(I);
        Iv := TraceDualIdeal(ComplexConjugate(I));
        J, J_to_Iv := ICM_Identify(Iv, icm_lookup);
        WI := I`WErep; Ipic := I`Pelt;
        WJ := J`WErep; Jpic := J`Pelt;
        for d -> isog_I_J_d in isog[myHash(WI)][myHash(WJ)] do
            for data in isog_I_J_d do
                x, h, H, L := Explode(data);
                // x is the element inducing the isogeny from WI+h to WJ with image L, H is the subgroup of Pic(ZFV) that we can translate our domain by
                // So x also maps WI+h+Jpic to WJ+Jpic = J, so we just need to see if I can be reached from WI+h+Jpic using the subgroup H
                if Ipic - Jpic - h in H then
                    // This isogeny has the right domain and codomain to be a polarization.
                    got_one := false;
                    for v in transveral_US_USplus(S) do
                        pp := x*v; // TODO: need to think about how to use IsPrincipal appropriately here.
                        if is_polarization(pp, PHI) then
                            got_one := true;
                            break;
                        end if;
                    end for;
                    if got_one then
                        pols_deg_d cat:= [ pp*t : t in transversal_USplus_USUSb_general(S) ]; // this might contains isomorphic copies
                    end if;
                end if;
            end for;
            t_can_Jd:=Cputime();
            // TODO: Below here still needs adaptation
            pols_deg_d_up_to_iso:={};
            for x0 in pols_deg_d do
                pol,seq:=CanonicalRepresentativePolarizationGeneral(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,seq>); //isomorphic pols will have the same canonical rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert2 forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Jv,pol[1]*J) }; // sanity check
            Jpols[d]:=[ < pol[1] , pol[2] , DecompositionKernelOfIsogeny(J,Jv,pol[1]) > : pol in pols_deg_d_up_to_iso ];
        end for;
        all_pols[J]:=Jpols;
    end for;
    vprintf AllPolarizations : "time spent on computing canonical reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
    return all_pols;
end intrinsic;

// Old version for comparison; use RepresentativeMinimalIsogenies instead
intrinsic AllMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=0)->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the canonical representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
}
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    min_isog:=AssociativeArray();
    for I in isom_cl do
        min_isog[myHash(I)] := AssociativeArray();
        for J in isom_cl do
            min_isog[myHash(I)][myHash(J)] := [];
        end for;
    end for;
    for J in isom_cl do
        // J is over ZFV
        Ls := MaximalIntermediateIdeals(J,N*J);
        for L in Ls do
            deg := Index(J, L);
            if degrees cmpne 0 and not (deg in degrees) then
                continue;
            end if;
            I, x := ICM_Identify(L, icm_lookup);
            assert2 Index(J,x*I) eq deg;
            Append(~min_isog[myHash(I)][myHash(J)], <deg, x, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L)
        end for;
    end for;
    return min_isog;
end intrinsic;

// Old version for comparison; use PotentialPolarizations instead
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
    t0:=Cputime();
    min_isog := AllMinimalIsogenies(ZFV, N : degrees:=degrees);
    vprintf AllPolarizations : "time spent on AllMinimalIsogenies %o\n",Cputime(t0);
    isog := AssociativeArray();
    isom_cl:=ICM_CanonicalRepresentatives(ZFV);
    for I in isom_cl do
        isog[myHash(I)] := AssociativeArray();
        for J in isom_cl do
            isog[myHash(I)][myHash(J)] := AssociativeArray();
            // for dxL in min_isog[J][I] do // I THINK THIS IS WRONG
            for dxL in min_isog[myHash(I)][myHash(J)] do
                d, x, L := Explode(dxL);
                if keep_degree(I, J, d) then
                    if not IsDefined(isog[myHash(I)][myHash(J)], d) then
                        isog[myHash(I)][myHash(J)][d] := [];
                    end if;
                    assert2 Index(J,L) eq d;
                    assert2 x*I eq L;
                    Append(~isog[myHash(I)][myHash(J)][d], <x, L>);
                end if;
            end for;
        end for;
    end for;
    while true do
        added_something := false;
        for J in isom_cl do
            for I in isom_cl do
                for K in isom_cl do
                    for m -> known in isog[myHash(I)][myHash(K)] do
                        for yL0 in known do
                            y, g, L0 := Explode(yL0);
                            for dxL in min_isog[myHash(K)][myHash(J)] do
                                d, x := Explode(dxL);
                                dm := d*m;
                                if keep_degree(I, J, dm) then
                                    L := x * L0;
                                    if not IsDefined(isog[myHash(I)][myHash(J)], dm) then
                                        isog[myHash(I)][myHash(J)][dm] := [<x*y, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M[2]) : M in isog[myHash(I)][myHash(J)][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[myHash(I)][myHash(J)][dm], <x*y, L>);
                                            assert2 Index(J,x*y*I) eq dm;
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
    t_tot:=Cputime();
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    can_reps_of_duals:=AssociativeArray();
    all_pols:=AssociativeArray(); // the output
    for J in isom_cl do
        Jpols:=AssociativeArray(); // will contain all pols find, indexed by degree.
        Jv:=TraceDualIdeal(ComplexConjugate(J));
        // I am looking for pol such that pol*J c Jv
        JJ,JJ_to_Jv:=ICM_Identify(Jv,icm_lookup);
        can_reps_of_duals[J]:=<JJ,JJ_to_Jv,Jv>;
    end for;
    t0:=Cputime();
    all_isog:=IsogeniesByDegree(ZFV,degree_bounds : important_pairs:=[ < J , can_reps_of_duals[J][1] > : J in isom_cl ]);
    vprintf AllPolarizations : "time spent on IsogeniesByDegree: %o\n",Cputime(t0);
    t_can:=0;
    for J in isom_cl do
        S:=MultiplicatorRing(J);
        JJ,JJ_to_Jv,Jv:=Explode(can_reps_of_duals[J]);
        for d ->isog_J_JJ_d in all_isog[myHash(J)][myHash(JJ)] do
            pols_deg_d:=[];
            for f in isog_J_JJ_d do
                isog:=f[1]*JJ_to_Jv;
                assert2 Index(JJ,f[1]*J) eq d;
                assert2 Index(Jv,isog*J) eq d;
                got_one:=false;
                for v in transversal_US_USplus(S) do
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
            t_can_Jd:=Cputime();
            pols_deg_d_up_to_iso:={};
            for x0 in pols_deg_d do
                pol,seq:=CanonicalRepresentativePolarizationGeneral(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,seq>); //isomorphic pols will have the same canonical rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert2 forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Jv,pol[1]*J) }; // sanity check
            Jpols[d]:=[ < pol[1] , pol[2] , DecompositionKernelOfIsogeny(J,Jv,pol[1]) > : pol in pols_deg_d_up_to_iso ];
        end for;
        all_pols[J]:=Jpols;
    end for;
    vprintf AllPolarizations : "time spent on computing canonical reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
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

/* TESTS
    TODO Add tests. Some ideas:
        For AllPolarizations: - compute some output using slow naive numeration process of sublattices of the dual variety.
                              - Compare with Example 7.2 in https://arxiv.org/abs/1805.10223
                                f := x^4 + 2*x^3 - 7*x^2 + 22*x + 121;
                              - not sure what to do for minimal isogenies...maybe compute some 
                                for elliptic curves and check for volcanoes?
*/


