/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Isogeny functions and polarizations for fractional ideals
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose IsogeniesPolarizations, 1;


/////////////////////////////////////////////////////
// Isogenies
/////////////////////////////////////////////////////

intrinsic IsogeniesManyOfDegree(AIS::SeqEnum[AbelianVarietyFq], AJ::AbelianVarietyFq, N::RngIntElt) -> SeqEnum[HomAbelianVarietyFq]
{Given a sequence of source squarefree abelian varieties AIS, a target sqaurefree abelian varity AJ and a positive integet N, it returns for each AI in AIS if there exist an isogeny AI->AJ of degree N. For each AI in AIS, if there exists and isogeny AI->AJ, it is also returned a list of representatives of the isomorphism classes of pairs [*hom_x , K*] where: hom_x:AI->AJ, and K=xI subset J, with I and J the fractional ideals representing AI and AJ and x the element representing the isogeny.}
    
    I:=IsogenyClass(AJ);
    vprintf IsogeniesPolarizations : "IsogeniesMany AbVarFq\n";
    require IsSquarefree(I) and (IsOrdinary(I) or IsCentelegheStix(I)): "implemented only for Squarefree isogeny classes ";
    DJ:=DirectSumRepresentation(DeligneModule(AJ))[1]; // squarefree case
    J:=DJ[1]; mJ:=DJ[2];
    UA:=UniverseAlgebra(AJ);
	isogenies_of_degree_N := [* [* *] : i in [1..#AIS] *];
	for K in IdealsOfIndex(J, N) do
		for i := 1 to #AIS do
            if IsogenyClass(AIS[i]) eq IsogenyClass(AJ) then
                DISi:=DirectSumRepresentation(DeligneModule(AIS[i]))[1]; //squarefree case
                ISi:=DISi[1]; mISi:=DISi[2];
                test,x:=IsIsomorphic(K, ISi); //x*ISi=K
                assert x*ISi eq K;
                if test then
                    hom_x:=Hom(AIS[i],AJ, hom<UA->UA | [ x*a : a in AbsoluteBasis(UA) ] >);
                    hom_x`IsIsogeny:=<true, N>;
                    if N eq 1 then
                        hom_x`IsIsomorphism:=true;
                    end if;
                    Append(~isogenies_of_degree_N[i], [*hom_x, K*]);
                end if;
            else 
                Append(~isogenies_of_degree_N[i], [* *]);
            end if;
		end for;
	end for;
	return isogenies_of_degree_N;
end intrinsic;

intrinsic IsogeniesOfDegree(A::AbelianVarietyFq, B::AbelianVarietyFq, N::RngIntElt)->BoolElt,SeqEnum[HomAbelianVarietyFq]
{Given a source abelian variety A, a target abelian varity B and a positive integet N, it returns if there exist an isogeny A->B of degree N. If so it is also returned a list of representatives of the isormopshim classes of pairs [*hom_x , K*] where: hom_x:A->A, and K=xI subset J, with I and J the fractional ideals representing A and B and x the element representing the isogeny. At the moment it is implement ed only for squarefree abelin varieties.}
	isogenies_of_degree_N := IsogeniesManyOfDegree([A], B, N);
	return #isogenies_of_degree_N[1] ge 1, isogenies_of_degree_N[1];
end intrinsic;

/////////////////////////////////////////////////////
// Polarizations
/////////////////////////////////////////////////////

intrinsic IsPolarization(pol::HomAbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt
{Returns whether the hommorphisms is known to be a polarizations for the CM-type phi.}
    A:=Domain(pol);
    require IsSquarefree(IsogenyClass(A)) : "implemented only for square-free ordinary abelian varieties";
    if CheckOrdinary then
        require IsOrdinary(A) : "the input needs to be ordinary.";
    end if;
    x0:=MapOnUniverseAlgebras(pol)(1); //the element of the UniverseAlgebra representing the map
    //pol is a polarization if x0 is totally imaginary and \Phi-positive
    C := [g(x0): g in Homs(phi)];
    if (x0 eq -ComplexConjugate(x0) and forall{c : c in C | Im(c) gt 0}) then
        return true;
    else
        return false;
    end if;
end intrinsic;

intrinsic IsPrincipallyPolarized(A::AbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]
{Returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations.}
    require IsSquarefree(IsogenyClass(A)) : "implemented only for squarefree isogeny classes";
    if CheckOrdinary then
        require IsOrdinary(A) : "the input needs to be ordinary.";
    end if;
	S:=EndomorphismRing(A);
	if S eq ComplexConjugate(S) then
		return IsPolarized(A,phi,1);
	else
		return false,[];
	end if;
end intrinsic;

intrinsic PolarizationsOfDegree(A::AbelianVarietyFq,PHI::AlgEtQCMType,N::RngIntElt : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]
{Returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations.}
    require IsSquarefree(IsogenyClass(A)) : "implemented only for ordinary squarefree isogeny classes";
    if CheckOrdinary then
        require IsOrdinary(A) : "the input needs to be ordinary.";
    end if;
    if not IsSquare(N) then // the degree of a pol is always a square
        return false,[]; 
    end if;
    UA:=UniverseAlgebra(A);
    S:=EndomorphismRing(A);
    assert UA eq Algebra(S);
    Av:=DualAbelianVariety(A);
    phi:=Homs(PHI);
    assert Domain(phi[1]) eq UA;

	boolean, isogenies_of_degree_N := IsogeniesOfDegree(A, Av, N);
	if not boolean then
		return false, [];
	end if;
    

    zbS:=ZBasis(S);
    T:=Order(zbS cat [ ComplexConjugate(z) : z in zbS ]);
    UT,uT:=UnitGroup(T); //uT:UT->T
    US,uS:=UnitGroup(S); //uS:US->S
    gensUinS:=[uS(US.i):i in [1..Ngens(US)]];
    USUSb:=sub<UT|[(g*ComplexConjugate(g))@@uT:g in gensUinS]>;
    USinUT:=sub<UT|[g@@uT:g in gensUinS]>;
    Q,q:=quo< USinUT | USinUT meet USUSb >; // q:=USinUT->Q
                                            // Q = S*/<v bar(v) : v in S*> meet S*
    QinT:=[ uT(UT!(b@@q)) : b in Q];
	pols_deg_N_allKs :=[]; // it will contain pols for each K up to iso. 
                           // note that given a and a' with aI=K and a'I=K', a and a' might be isomorphic.
                           // we get rid of these 'doubles' later

	for elt in isogenies_of_degree_N do
		// x*I = J
		x := (MapOnUniverseAlgebras(elt[1]))(One(UA));
		J := elt[2];
		for uu in QinT do
			pol := (x*(UA ! uu));
			//pol is a polarization if totally imaginary and \Phi-positive
			C := [g(pol): g in phi];
			if (ComplexConjugate(pol) eq (-pol)) and (forall{c : c in C | Im(c) gt 0}) then
				Append(~pols_deg_N_allKs, pol);
			end if;
		end for;
	end for;
    
    // now we remove the isomorphic polarizations with different 'kernels'
    polarizations_of_degree_N:=[];
    for a in pols_deg_N_allKs do
        if not exists{ a1 : a1 in polarizations_of_degree_N | 
                            (a/a1) in T and (a1/a) in T and // a/a1 is a unit in T=S bar(S) 
                            ((a/a1)@@uT) in USUSb } then
            Append(~polarizations_of_degree_N, a);
        end if;
    end for;
    output:=[];
    for a in polarizations_of_degree_N do
        pol:=Hom(A,Av,Hom(UA,UA,[ a*b : b in AbsoluteBasis(UA)]));
        pol`IsIsogeny:=<true,N>;
        Append(~output,pol);
    end for;
	if #output ge 1 then
		return true, output;
	else
		return false,[];
	end if;
end intrinsic;

intrinsic PolarizedAutomorphismGroup(mu::HomAbelianVarietyFq : CheckOrdinary:=true) -> GrpAb
{returns the automorphisms of a polarized abelian variety}
    A:=Domain(mu);
    require IsSquarefree(IsogenyClass(A)) : "implemented only for ordinary squarefree isogeny classes";
    if CheckOrdinary then
        require IsOrdinary(A) : "the input needs to be ordinary.";
    end if;
    S:=EndomorphismRing(A);
	return TorsionSubgroup(UnitGroup2(S));
end intrinsic;

/* TEST

//TODO move this tests somewher else ?
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    
    //////////////////////////////////
    //Example 7.2
    //////////////////////////////////
    
    _<x>:=PolynomialRing(Integers());
    h:=x^4+2*x^3-7*x^2+22*x+121;
    AVh:=IsogenyClass(h);
    iso:=ComputeIsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for iA in [1..#iso] do
        A:=iso[iA];
        N:=0;
        repeat
            printf ".";
            N+:=1;
            test,pols_deg_N:=IsPolarized(A,PHI,N);
        until test;
        for pol in pols_deg_N do
            PeriodMatrix(pol,PHI);
            aut:=#PolarizedAutomorphismGroup(pol);
        end for;
        iA,#pols_deg_N,N,aut;
    end for;

    //////////////////////////////////    
    //Example 7.3
    //////////////////////////////////
    
    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    iso:=ComputeIsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        test,princ_pols:=IsPrincipallyPolarized(A,PHI);
        for pol in princ_pols do
            assert IsPolarization(pol,PHI);
            PolarizedAutomorphismGroup(pol);
        end for;
    end for;

*/




