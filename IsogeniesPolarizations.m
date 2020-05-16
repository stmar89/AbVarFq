/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Isogeny functions and polarizations for fractional ideals
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose IsogeniesPolarizations, 1;

//TODO all these intrinsic should have as input AbelianVarietiesFq
//TODO add DualAbelianVariety
//TODO IsIsomorphic, FrobeniusEndomorphism, IsTwist and similar (everything that returns a Map) should return an HomAbelianVarieties. This might break the examples posted on the webpage
//TODO TEST
// I SHOULD create a new type..HomAbVarFq or something like that with domain, codomain, image, kernel and actual map
// TODO Evaluate hom on points

/////////////////////////////////////////////////////
// NewType: HomAbelianVarietyFqA
// a morphism of abelin varieties over Fq
/////////////////////////////////////////////////////

declare type HomAbelianVarietyFq;
declare attributes HomAbelianVarietyFq : Domain,
                                         Codomain,
                                         // Image, //does it makes sense?
                                         // Kernel, //what should this be? 
                                         MapOnUniverseAlgebras,
                                         IsIsogeny, // a pair < true/false, Degee >
                                         IsIsomorphism,
                                         IsEndomorphism,
                                         IsAutomorphism;

/////////////////////////////////////////////////////
// Access, Print 
/////////////////////////////////////////////////////

intrinsic Print(m::HomAbelianVarietyFq)
{ print the morphism abelian variety }
    printf "Morphism from  %o to %o",Domain(m),Codomain(m);
end intrinsic;

intrinsic Domain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the domain the morphism}
    return m`Domain;
end intrinsic;

intrinsic Codomain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the codomain the morphism}
    return m`Codomain;
end intrinsic;

intrinsic MapOnUniverseAlgebras(m::HomAbelianVarietyFq)->Map
{returns underlying homormorphism of Deligne Moduels as a Z[F,V]-linear hom on the UniverseAlgebras}
    return m`MapOnUniverseAlgebras;
end intrinsic;

intrinsic IsEndomorphism(m::HomAbelianVarietyFq)->BoolElt 
{returns whether the morphism is an endomorphism}
    if not assigned m`IsEndomorphism then
        m`IsEndomorphism:=Domain(m) eq Codomain(m);
    end if;
    return m`IsEndomorphism;
end intrinsic;

intrinsic IsIsogeny(m::HomAbelianVarietyFq)->BoolElt,RngInt
{returns whether the morphism is an isogeny and if so it returns also the degree}
    if not assigned m`IsIsogeny then
        if IsogenyClass(Domain(m)) ne IsogenyClass(Codomain(m)) then
            false,_;
        else
            h:=MapOnUniverseAlgebras(m);
            A:=UniverseAlgebra(Domain(m));
            //TODO
        end if;
    end if;
    return m`IsIsogeny[1],m`IsIsogeny[2];
end intrinsic;

// TODO IsIsogeny, Degree, IsIsomorphsim, IsAutomrophism, IsPolarization, Kernel,

/////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////

intrinsic Hom(A::AbelianVarietyFq,B::AbelianVarietyFq,map::Map)->HomAbelianVarietyFq
{ creates a morphisms of belin varieties A->B determined by map, where map is a morphisms of the universe algebras of A and B }
    FA:=FrobeniusEndomorphism(A);
    FB:=FrobeniusEndomorphism(B);
    UA:=UniverseAlgebra(A);
    require UA eq Domain(map) and UniverseAlgebra(B) eq Codomain(map) and 
            forall{ i : i in Dimension(UA) | map(FA(UA.i)) eq FB(map(UA.i)) } //the map must be Frobanius-linear
                      : "the map does not define a morphism of abelian varieties";
    //the test might be time consuming .... maybe it should be moved to an assert2 ?
    // also in the squarefree case it is superfluous ...
    hom:=New(HomAbelianVarietyFq);
    hom`Domain:=A;
    hom`Codomain:=B;
    hom`MapOnUniverseAlgebras:=map;
    return hom;
end intrinsic;

/////////////////////////////////////////////////////
// Isogenies
/////////////////////////////////////////////////////

intrinsic IsogeniesMany(AIS::SeqEnum[AbelianVarietyFq], AJ::AbelinVarietyFq, N::RngIntElt) -> BoolElt, Seq[HomAbelianVarietyFq]
{
    Given a sequence of source squarefree abelian varieties AIS, a target sqaurefree abelian varity AJ and a positive integet N, it returns for each AI in AIS if there exist an isogeny AI->AJ of degree N. 
    For each AI in AIS, if there exists and isogeny AI->AJ, it is also returned a list of representatives of the isormopshim classes of pairs [*hom_x , K*] where:
     hom_x:AI->AJ, and
     K=xI subset J, with I and J the fractional ideals representing AI and AJ and x the element representing the isogeny.
}

    vprintf IsogeniesPolarizations : "IsogeniesMany AbVarFq\n";
    require IsSquarefree(IsogenyClass(AJ)) : "implemented only for Squarefree isogeny classes ";
    J,mJ:=DeligneModuleAsDirectSum(AJ)[1]; // squarefree case
    UA:=UniverseAAlgebra(AJ);
	isogenies_of_degree_N := [* [* *] : i in [1..#AIS] *];
	for K in IdealsOfIndex(J, N) do
		for i := 1 to #AIS do
            if IsogenyClass(AIS[i]) eq IsogenyClass(AJ) then
                ISi,mIi:=DeligneModuleAsDirectSum(AIS[i])[1]; //squarefree case
                test, x := IsIsomorphic2(K, ISi); //x*ISi=K
                if test then
                    hom_x:=Hom(AIS[i],AJ, hom<UA->UA | [ x*UA.i : i in [1..Dimension(UA)] ] >);
                    hom_x`IsIsogeny:=true;
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

intrinsic Isogenies(A::AbelianVarietyFq, B::AbelianVarietyFq, N::RngIntElt)->BoolElt, List
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

intrinsic DualAbelianVariety(A::AbelianVarietyFq)->Av::AbelianVarietyFq
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


//TODO : need dualabvar


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
    // TODO correct this function
    //
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

	U, m := UnitGroup2(S); //m:U->S
	// B = Subgroup of S^* generated by u*\bar{u} : u in S^*
	relB := Seqset([ (( m(U.i)*(ComplexConjugate(A!m(U.i))) ) )@@m : i in [1..Ngens(U)] ] ); //B is generated by u*\bar{u}
	UqB, q := quo<U|relB>; // UqB = U/B, q:U->UqB
	UqBinS := [ m(u@@q) :  u in UqB ]; //elements of U/B as elements of the order S
	polarizations_of_degree_N :=[];

	for elt in isogenies_of_degree_N do
		// x*I = J
		x := elt[1];
		J := elt[2];
		assert (J) subset Itbar;
		for uu in UqBinS do
			pol := (x*(A ! uu));
			assert (pol*I) eq J;
			//pol is a polarization if totally imaginary and \Phi-positive
			C := [g(pol): g in phi];
			if (ComplexConjugate(pol) eq (-pol)) and (forall{c : c in C | Im(c) gt (RR ! 0)}) then
				Append(~polarizations_of_degree_N, pol);
			end if;
		end for;
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

