/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Isogeny functions and polarizations for fractional ideals
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose IsogeniesPolarizations, 1;

/////////////////////////////////////////////////////
// Isogenies
/////////////////////////////////////////////////////

intrinsic IsogeniesMany(AIS::SeqEnum[AbelianVarietyFq], AJ::AbelianVarietyFq, N::RngIntElt) -> SeqEnum[HomAbelianVarietyFq]
{
    Given a sequence of source squarefree abelian varieties AIS, a target sqaurefree abelian varity AJ and a positive integet N, it returns for each AI in AIS if there exist an isogeny AI->AJ of degree N. 
    For each AI in AIS, if there exists and isogeny AI->AJ, it is also returned a list of representatives of the isormopshim classes of pairs [*hom_x , K*] where:
     hom_x:AI->AJ, and
     K=xI subset J, with I and J the fractional ideals representing AI and AJ and x the element representing the isogeny.
}

    vprintf IsogeniesPolarizations : "IsogeniesMany AbVarFq\n";
    require IsSquarefree(IsogenyClass(AJ)) : "implemented only for Squarefree isogeny classes ";
    DJ:=DeligneModuleAsDirectSum(AJ)[1]; // squarefree case
    J:=DJ[1]; mJ:=DJ[2];
    UA:=UniverseAlgebra(AJ);
	isogenies_of_degree_N := [* [* *] : i in [1..#AIS] *];
	for K in IdealsOfIndex(J, N) do
		for i := 1 to #AIS do
            if IsogenyClass(AIS[i]) eq IsogenyClass(AJ) then
                DISi:=DeligneModuleAsDirectSum(AIS[i])[1]; //squarefree case
                ISi:=DISi[1]; mISi:=DISi[2];
                test, x := IsIsomorphic2(K, ISi); //x*ISi=K
                if test then
                    hom_x:=Hom(AIS[i],AJ, hom<UA->UA | [ x*UA.i : i in [1..Dimension(UA)] ] >);
                    hom_x`IsIsogeny:=<true, N>;
                    if N eq 1 then
                        hom_x`IsIsomorphism:=true;
                    end if;
                    Append(~isogenies_of_degree_N[i], [*hom_x, K*]);
                end if;
            end if;
		end for;
	end for;
	return isogenies_of_degree_N;
end intrinsic;

intrinsic Isogenies(A::AbelianVarietyFq, B::AbelianVarietyFq, N::RngIntElt)->BoolElt,SeqEnum[HomAbelianVarietyFq]
{
    Given a source abelian variety A, a target abelian varity B and a positive integet N, it returns if there exist an isogeny A->B of degree N.
    If so it is also returned a list of representatives of the isormopshim classes of pairs [*hom_x , K*] where:
     hom_x:A->A, and
     K=xI subset J, with I and J the fractional ideals representing A and B and x the element representing the isogeny.
     At the moment it is implement ed only for squarefree abelin varieties.
}
	isogenies_of_degree_N := IsogeniesMany([A], B, N);
	return #isogenies_of_degree_N[1] ge 1, isogenies_of_degree_N[1];
end intrinsic;

/////////////////////////////////////////////////////
// Dual Abelian Variety 
/////////////////////////////////////////////////////

intrinsic DualAbelianVariety(A::AbelianVarietyFq)->AbelianVarietyFq
{ given an abelian vareity A returns the dual abelian variety }
    require IsOrdinary(A) : "implemented only for ordinary isogeny classes";
    B:=DeligneModuleZBasis(A);
    n:=#B;
    Q:=MatrixRing(RationalField(), n)![Trace(B[i]*B[j]): i, j in [1..n] ];
    QQ:=Q^-1;
    BB:=[&+[ (QQ[i,j]*B[j]): j in [1..n]] : i in [1..n]] ;
    BBc:=[ ComplexConjugate(b) : b in BB ];
    Av:=AbelianVariety(IsogenyClass(A),BBc); //the direct sum of ideal is not computed here
    return Av;
end intrinsic;

/////////////////////////////////////////////////////
// Polarizations
/////////////////////////////////////////////////////

intrinsic IsPrincipallyPolarized(A::AbelianVarietyFq, phi::AlgAssCMType)->BoolElt, SeqEnum[HomAbelianVarietyFq]
{returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations}
    return IsPrincPolarized(A,phi);
end intrinsic;

intrinsic IsPrincPolarized(A::AbelianVarietyFq, phi::AlgAssCMType)->BoolElt, SeqEnum[HomAbelianVarietyFq]
{returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations}
    require IsOrdinary(A) and IsSquarefree(IsogenyClass(A)) : "implemented only for ordinary squarefree isogeny classes";
	S:=EndomorphismRing(A);
	if S eq ComplexConjugate(S) then
		return IsPolarized(A, phi , 1);
	else
		return false,[];
	end if;
end intrinsic;

intrinsic IsPolarized(A::AbelianVarietyFq, PHI::AlgAssCMType , N::RngIntElt)->BoolElt, SeqEnum[HomAbelianVarietyFq]
{returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations}
    
    require IsOrdinary(A) and IsSquarefree(IsogenyClass(A)) : "implemented only for ordinary squarefree isogeny classes";
    UA:=UniverseAlgebra(A);
    S:=EndomorphismRing(A);
    assert UA eq Algebra(S);
    Av:=DualAbelianVariety(A);
    phi:=Homs(PHI);
    assert Domain(phi[1]) eq UA;

	boolean, isogenies_of_degree_N := Isogenies(A, Av, N);
	if not boolean then
		return false, [];
	end if;
    

    zbS:=ZBasis(S);
    T:=Order(zbS cat [ ComplexConjugate(z) : z in zbS ]);
    UT,uT:=UnitGroup2(T); //uT:UT->T
    US, uS := UnitGroup2(S); //uS:US->S
    gensUinS:=[ uS(US.i) : i in [1..Ngens(US)]];
    USUSb:=sub< UT | [ (g*ComplexConjugate(g))@@uT : g in gensUinS ]>;
    USinUT:=sub<UT | [ g@@uT : g in gensUinS ]>;
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
        pol:=Hom(A,Av,hom<UA->UA | [ a*UA.i : i in [1..Dimension(UA)]]>);
        pol`IsIsogeny:=<true,N>;
        //pol`IsPolarization:=<true,PHI>;
        Append(~output,pol);
    end for;
	if #output ge 1 then
		return true, output;
	else
		return false,[];
	end if;
end intrinsic;

intrinsic PolarizedAutomorphismGroup(mu::HomAbelianVarietyFq) -> GrpAb
{returns the automorphisms of a polarized abelian variety}
    A:=Domain(mu);
    require IsOrdinary(A) and IsSquarefree(IsogenyClass(A)) : "implemented only for ordinary squarefree isogeny classes";
    S:=EndomorphismRing(A);
	return TorsionSubgroup(UnitGroup2(S));
end intrinsic;

/////////////////////////////////////////////////////
// OLD functions. Kept for retro-compatibility
/////////////////////////////////////////////////////

intrinsic IsogeniesMany(IS::SeqEnum[AlgAssVOrdIdl], J::AlgAssVOrdIdl, N::RngIntElt) -> BoolElt, List
{Given a sequence of source abelian varieties IS, a target abelian varity J and a positive integet N, it returns for each I in IS if there exist an isogeny I->J of degree N. 
 For each I in IS, if there exists and isogeny I->J, it is also returned a list of pairs [*x,K*] where K=xI subset J (up to isomorphism).}
//by Edgar Costa, modified by Stefano
	vprintf IsogeniesPolarizations : "IsogeniesMany\n";
	isogenies_of_degree_N := [* [* *] : i in [1..#IS] *];
	for K in IdealsOfIndex(J, N) do
		for i := 1 to #IS do
			test, x := IsIsomorphic2(K, IS[i]); //x*IS[i]=K
			if test then
				Append(~isogenies_of_degree_N[i], [*x, K*]);
			end if;
		end for;
	end for;
	return isogenies_of_degree_N;
end intrinsic;

intrinsic Isogenies(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl, N::RngIntElt)->BoolElt, List
{Given a source abelian variety I, a target abelian varity J and a positive integet N, it returns if there exist an isogeny I->J of degree N.
 If so it is also returned a list of pairs [*x,K*] where K=xI subset J (up to isomorphism).}
//by Edgar Costa, modified by Stefano
	isogenies_of_degree_N := IsogeniesMany([I], J, N);
	return #isogenies_of_degree_N[1] ge 1, isogenies_of_degree_N[1];
end intrinsic;

intrinsic IsPrincPolarized(I::AlgAssVOrdIdl , phi::SeqEnum[Map])->BoolElt, SeqEnum[AlgAssElt]
{returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations}
	S:=MultiplicatorRing(I);
	if S eq ComplexConjugate(S) then
		return IsPolarized(I, phi , 1);
	else
		return false,[];
	end if;
end intrinsic;

intrinsic IsPolarized(I0::AlgAssVOrdIdl, phi::SeqEnum[Map], N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
{returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations}
	S := MultiplicatorRing(I0);
	I := ideal<S|ZBasis(I0)>;
	A := Algebra(S);
	prec:=Precision(Codomain(phi[1]));
	RR := RealField(prec); //precision added
	Itbar := ComplexConjugate(TraceDualIdeal(I));

	boolean, isogenies_of_degree_N := Isogenies(I, Itbar, N);
	if not boolean then
		return false, [];
	end if;

    zbS:=ZBasis(S);
    T:=Order(zbS cat [ ComplexConjugate(z) : z in zbS ]);
    UT,uT:=UnitGroup2(T); //uT:UT->T
    US, uS := UnitGroup2(S); //uS:US->S
    gensUinS:=[ uS(US.i) : i in [1..Ngens(US)]];
    USUSb:=sub< UT | [ (g*ComplexConjugate(g))@@uT : g in gensUinS ]>;
    USinUT:=sub<UT | [ g@@uT : g in gensUinS ]>;
    Q,q:=quo< USinUT | USinUT meet USUSb >; // q:=USinUT->Q
                                            // Q = S*/<v bar(v) : v in S*> meet S*
    QinT:=[ uT(UT!(b@@q)) : b in Q];
	pols_deg_N_allKs :=[]; // it will contain pols for each K up to iso. 
                           // note that given a and a' with aI=K and a'I=K', a and a' might be isomorphic.
                           // we get rid of these 'doubles' later

	for elt in isogenies_of_degree_N do
		// x*I = J
		x := elt[1];
		J := elt[2];
		assert J subset Itbar;
		for uu in QinT do
			pol := (x*(A ! uu));
			//pol is a polarization if totally imaginary and \Phi-positive
			C := [g(pol): g in phi];
			if (ComplexConjugate(pol) eq (-pol)) and (forall{c : c in C | Im(c) gt (RR ! 0)}) then
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

	if #polarizations_of_degree_N ge 1 then
		return true, polarizations_of_degree_N;
	else
		return false,[];
	end if;
end intrinsic;

intrinsic AutomorphismsPol(I::AlgAssVOrdIdl) -> GpAb
{returns the automorphisms of a polarized abelian variety}
    // add a map 
	//require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	return TorsionSubgroup(UnitGroup2(MultiplicatorRing(I)));
end intrinsic;


/* TEST
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    
    //////////////////////////////////
    //Example 7.2
    //////////////////////////////////
    
    _<x>:=PolynomialRing(Integers());
    h:=x^4+2*x^3-7*x^2+22*x+121;
    AVh:=IsogenyClass(h);
    iso:=ComputeIsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        N:=0;
        repeat
            printf ".";
            N+:=1;
            test,pols_deg_N:=IsPolarized(A,PHI,N);
        until test;
        N;
        for pol in pols_deg_N do
            PolarizedAutomorphismGroup(pol);
        end for;
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
            PolarizedAutomorphismGroup(pol);
        end for;
    end for;


    //////////////////////////////////    
    //Example 7.4
    //////////////////////////////////
    
    _<x>:=PolynomialRing(Integers());
    h:=x^8-5*x^7+13*x^6-25*x^5+44*x^4-75*x^3+1177*x^2-135*x+81;
    AVh:=IsogenyClass(h);
    iso:=ComputeIsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        test,princ_pols:=IsPrincipallyPolarized(A,PHI);
        for pol in princ_pols do
            PolarizedAutomorphismGroup(pol);
        end for;
    end for;







*/




