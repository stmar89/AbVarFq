/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Abelian varieties and Isogeny classes
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

/* REFERENCES:
[Wat69] W. C. Waterhouse. Abelian varieties over finite fields. Ann. Sci. École Norm. Sup. (4), 2:521–560, 1969. 45, 53, 54
*/

/* TODO:
    DeligneModule shoud be of Type AlgEtQMod. No further attributes related to it. Also, it should be used only when IsOrdinary or IsCentelegheStix
*/

/////////////////////////////////////////////////////
// New Type AbelianVarietyFq
/////////////////////////////////////////////////////

declare type AbelianVarietyFq;
declare attributes AbelianVarietyFq : IsogenyClass,
                                      DeligneModuleZBasis,
                                      DeligneModuleAsDirectSum, //not all DeligneModules can be written as a direct sum. but if this is the case, here we store a sequence of pairs <J,m>, where J is a fractional Z[F,V] ideal and m is a map from the Algebr(J) to the UniverseAlgebra of the isogeny class.
                                      DeligneModuleAsBassMod, //when ZFV is Bass then we can also attach a BassMod
                                      EndomorphismRing,
                                      FrobeniusEndomorphism,
                                      GroupOfRationalPoints,
                                      Polarizations;
intrinsic Print(I::AbelianVarietyFq)
{ print the abelian variety }
    printf "Abelian variety over FF_%o",FiniteField(I);
end intrinsic;

/////////////////////////////////////////////////////
// Creation functions of AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic AbelianVariety( AVh::IsogenyClassFq , I::AlgAssVOrdIdl )->AbelianVarietyFq
{ returns the abelian variety defined by a fractional ideal I of the Z[F,V] order of the isogeny class AV(h), where h is the characteristic polynomial of the Frobenius } 
    R,delta:=ZFVOrder(AVh);
    require R eq Order(I) : "the fractional ideal is not defined over the order Z[F,V] of the given isogeny class";
    UA:=UniverseAlgebra(AVh);
    require UA eq Algebra(R) : "one cannot define an abelian variety using a fractional ideal for the given isogeny class";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    map:=hom<Algebra(R)-> UA | [UA.i : i in [1..Dimension(UA)] ]>; // this is the identity map
    AV`DeligneModuleAsDirectSum:=[ <I,map> ];
    AV`DeligneModuleZBasis:=[ map(z) : z in ZBasis(I) ];
    return AV;
end intrinsic;

intrinsic AbelianVariety( AVh::IsogenyClassFq , seq::SeqEnum[AlgAssVOrdIdl] )-> AbelianVarietyFq
{ returns the abelian variety defined by a direct sum of s fractional ideals  of the Z[F,V] order of the isogeny class AV(g^s), where g is the square-free characteristic polynomial of the Frobenius } 
    R,delta:=ZFVOrder(AVh);
    g:=DefiningPolynomial(Algebra(R));
    s:=#seq;
    require forall{ I : I in seq | R eq Order(I) } : "the sequence of fractional ideals does not define an abelin variety in the given isogeny class";
    require WeilPolynomial(AVh) eq g^s : "the given isogeny class is not a pure-power";
    UA:=UniverseAlgebra(AVh);
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    DM:=[]; 
    for i in [1..s] do
        I:=seq[i];
        i0:=Degree(g)*(i-1)+1;
        assert (UA.i0^2 eq UA.i0); //it should be an orthogonl idempotent
        map:=hom<Algebra(R)->UA | [UA.i : i in [i0..i0+Degree(g)-1] ]>; // embedding of Ag->Ag^s into the ith component
        Append(~DM,<I,map>);
    end for;    
    AV`DeligneModuleAsDirectSum:=DM;
    AV`DeligneModuleZBasis:=&cat[ [ M[2](z) : z in ZBasis(M[1]) ] : M in DM];
    return AV;
end intrinsic;

intrinsic AbelianVariety( AVh::IsogenyClassFq , seq::SeqEnum[AlgAssElt] )-> AbelianVarietyFq
{ returns the abelian variety defined defined by elements of the universal algebra contained in seq } 
    R,delta:=ZFVOrder(AVh);
    UA:=UniverseAlgebra(AVh);
    require forall{ g : g in seq | Parent(g) eq UA } : " the elements are not in the UniverseAlgebra(A)";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    is_lattice:=Rank( Matrix( seq ) ) eq Dimension(UA) ;
    require is_lattice : "the elements in seq do not generate a lattice in the UniverseAlgebra(A) ";
    // here we do not compute the direct sum decomposition, which is implemented only for squarefree and power-of-bass
    // if you need it, you can call DeligneModuleAsDirectSum
    AV`DeligneModuleZBasis:=seq;
    return AV;
end intrinsic;

intrinsic AbelianVariety( AVh::IsogenyClassFq , seq::SeqEnum[Tup] )-> AbelianVarietyFq
{ given an isogeny class and sequence of pairs  <J_i,v_i> returns the abelin variety in the given isogeny class defined by the Deligne Module J_1v_1+...+J_sv_s }
    R,delta:=ZFVOrder(AVh);
    g:=DefiningPolynomial(Algebra(R));
    UA:=UniverseAlgebra(AVh);
    s:=#seq;
    require forall{ J : J in seq | R eq Order(J[1]) and Parent(J[2]) eq UA } : "the sequence of fractional ideals does not define an abelin variety in the given isogeny class";
    require WeilPolynomial(AVh) eq g^s : "the given isogeny class is not a pure-power";
    
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    DM:=[]; 
    for i in [1..s] do
        Ji:=seq[i,1];
        vi:=seq[i,2];
        i0:=Degree(g)*(i-1)+1;
        assert (UA.i0^2 eq UA.i0); //it should be an orthogonl idempotent
        map:=hom<Algebra(R)-> UA | [UA.i*vi : i in [i0..i0+Degree(g)] ]>; // embedding of Ag->Ag^s defined by 1:->vi
        Append(~DM,<Ji,map>);
    end for;    
    AV`DeligneModuleAsDirectSum:=DM;
    AV`DeligneModuleZBasis:=&cat[ [ M[2](z) : z in ZBasis(M[1]) ] : M in DM];
    return AV;
end intrinsic;

intrinsic AbelianVariety( AVh::IsogenyClassFq , M::BassMod )-> AbelianVarietyFq
{ given an isogeny class and a BassMod it returns the corresponding abelian variety. }
    R,delta:=ZFVOrder(AVh);
    g:=DefiningPolynomial(Algebra(R));
    UA:=UniverseAlgebra(AVh);
    require Order(M) eq R and UniverseAlgebra(M) eq UA : "the given BassMod does not define an abelian variety in the given isogeny class";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    AV`DeligneModuleAsDirectSum:=DirectSumRep(M);
    AV`DeligneModuleZBasis:=GensOverZ(M);
    AV`DeligneModuleAsBassMod:=M;
    return AV;
end intrinsic;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( A::AbelianVarietyFq) -> IsogenyClassFq
{ returns the isogeny class of the given abelian variety }
    return A`IsogenyClass;
end intrinsic;

intrinsic WeilPolynomial(A::AbelianVarietyFq )-> RngUpolElt
{ given an isogeny class AV(h) returns the Weil polynomial h defining it }
    return WeilPolynomial(IsogenyClass(A));
end intrinsic;

intrinsic DeligneModuleZBasis( A :: AbelianVarietyFq) -> SeqEnum[AlgAssElt]
{ returns the DeligneModule defining the variety A }
    return A`DeligneModuleZBasis;
end intrinsic;

intrinsic FiniteField( A :: AbelianVarietyFq )-> RngInt
{ given an isogeny class AV(h) returns the size of the finite field of definition }
    return FiniteField(IsogenyClass(A));
end intrinsic;

intrinsic CharacteristicFiniteField( A :: AbelianVarietyFq )-> RngInt
{ given an isogeny class AV(h) returns the characteristic of the finite field of definition }
    return CharacteristicFiniteField(IsogenyClass(A));
end intrinsic;

intrinsic Dimension( A :: AbelianVarietyFq )-> RngInt
{ given an isogeny class AV(h) returns the dimension }
    return Dimension(IsogenyClass(A));
end intrinsic;

intrinsic UniverseAlgebra( A :: AbelianVarietyFq) -> AlgAss
{ returns the UniverseAlgebra where the DeligneModule lives in }
    return UniverseAlgebra(IsogenyClass(A));
end intrinsic;

intrinsic ZFVOrder( A :: AbelianVarietyFq) -> AlgAssVOrd,Map
{ returns the ZFV of the isogeny class of A }
    return ZFVOrder(IsogenyClass(A));
end intrinsic;

intrinsic EndomorphismRing(A::AbelianVarietyFq)-> AlgAssVOrd
{ returns Endomrophism ring of the abelian variety }
    require IsSquarefree(IsogenyClass(A)) : "at the moment it is implemented only for squarefree abelian varieties";
    if not assigned A`EndomorphismRing then
        A`EndomorphismRing:=MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]);
    end if;
    return A`EndomorphismRing;
end intrinsic;

intrinsic BassModule(A::AbelianVarietyFq)-> BassMod
{ given an abelian variety in a PowerOfBass-isogeny class it returns the associated BassMod }
    require IsPowerOfBass(IsogenyClass(A)) : "the isogeny class must a PowerOfBass";
    if not assigned A`DeligneModuleAsBassMod then
        R,mR:=ZFVOrder(A);
        if assigned A`DeligneModuleAsDirectSum then
            A`DeligneModuleAsBassMod:=BassModule(R,mR,A`DeligneModuleAsDirectSum);
        else
            M:=BassModule(R,mR,A`DeligneModuleZBasis);
            A`DeligneModuleAsDirectSum := DirectSumRep(M);
            A`DeligneModuleAsBassMod:=M;
        end if;
    end if;
    return A`DeligneModuleAsBassMod;
end intrinsic;

/////////////////////////////////////////////////////
// DeligneModule as Direct Sum
//////////////////////////////////////////////////////

intrinsic DeligneModuleAsDirectSum( A :: AbelianVarietyFq) -> SeqEnum[Tup]
{ returns the DeligneModule defining the variety A given as a sequence of pairs <J,m> where J is a fractional Z[F,V] ideal and m is a map from Algebra(J) to the UniverseAlgebra of the isogeny class }
    if not assigned A`DeligneModuleAsDirectSum then
        assert assigned A`DeligneModuleZBasis;
        I:=IsogenyClass(A);
        require IsSquarefree(I) or IsPowerOfBass(I) : " we don't know a method to determine if a direct sumi represenatation exists and how to compute it :-) ";
        R,mR:=ZFVOrder(A);
        if IsSquarefree(I) then
            id:=ideal<R|A`DeligneModuleZBasis>;
            UA:=UniverseAlgebra(A);
            assert UA eq Algebra(R);
            one:=hom<UA->UA | [UA.i : i in [1..Dimension(UA)]]>;
            A`DeligneModuleAsDirectSum:=[<id,one>];
        else // PowerOfBass case
            M:=BassModule(R,mR,A`DeligneModuleZBasis);
            A`DeligneModuleAsDirectSum := DirectSumRep(M);
            A`BassMod:=M;
        end if;
    end if;
    return A`DeligneModuleAsDirectSum;
end intrinsic;

/////////////////////////////////////////////////////
// Equality and isomorphism testing for AbelianVarietyFq
/////////////////////////////////////////////////////

isHNFeq:=function(gensM,gensN)
// input: two sequence of AlgAssElt
// returns: whether the vectors generate the same Z-module
    assert forall{ g : g in gensM cat gensN | Parent(g) eq Parent(gensM[1])  };
    M_mat:=Matrix([ ChangeUniverse(Eltseq(g),Rationals()) : g in gensM ]);
    N_mat:=Matrix([ ChangeUniverse(Eltseq(g),Rationals()) : g in gensN ]);
    d_M:=Denominator(M_mat);
    d_N:=Denominator(N_mat);
    if not d_M eq d_N then 
    	return false;
    else
	    M_matZ:=ChangeRing(d_M*M_mat,Integers()); 
	    N_matZ:=ChangeRing(d_N*N_mat,Integers());
	    HNF_M:=Matrix([r : r in Rows(HermiteForm(M_matZ)) | not IsZero(r)]);
	    HNF_N:=Matrix([r : r in Rows(HermiteForm(N_matZ)) | not IsZero(r)]);
	    return HNF_M eq HNF_N;
    end if;
end function;

isUAeq:=function(gensM,gensN)
// given generators in the Universal Algebra, we check if they generate the same Z-module
    return isHNFeq(
            [ ChangeUniverse(Eltseq(g),Rationals()) : g in gensM ], 
            [ ChangeUniverse(Eltseq(g),Rationals()) : g in gensN ]
                );
end function;

intrinsic 'eq'( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt
{ checks if two abelin varieties are equal the equal }
    if IsogenyClass(A1) eq IsogenyClass(A2) then
        gens1:=DeligneModuleZBasis(A1);
        gens2:=DeligneModuleZBasis(A2);
        return isHNFeq(gens1,gens2);
    else
        vprintf AbelianVarieties : "eq : the abelian varities are not in the same isogeny class \n";
        return false;
    end if;
end intrinsic;

intrinsic IsIsomorphic( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt,HomAbelianVarietyFq
{ checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism from the common UniverseAlgebra  }
    vprintf AbelianVarieties,1 : " IsIsomorphic :";
    if IsogenyClass(A1) eq IsogenyClass(A2) then
        if IsSquarefree(IsogenyClass(A1)) then
            ZFV,mZFV:=ZFVOrder(A1);
            DM1:=DeligneModuleAsDirectSum(A1);
            DM2:=DeligneModuleAsDirectSum(A2);
            s:=#DM1;
            assert s eq #DM2;
            assert s eq 1;
            I1:=DM1[1,1];
            v1:=DM1[1,2](One(Algebra(ZFV)));
            I2:=DM2[1,1];
            v2:=DM2[1,2](One(Algebra(ZFV)));
            test,iso_0:=IsIsomorphic2(I1,I2);
            if test then
                assert I1 eq iso_0*I2;
                iso:=v2/(iso_0*v1);
                map:=hom<UniverseAlgebra(A1)->UniverseAlgebra(A2) | x:->iso*x, y:->y/iso >;
                assert isUAeq(DeligneModuleZBasis(A2),[ map(g) : g in  DeligneModuleZBasis(A1)]);
                return true,Hom(A1,A2,map);
            else
                return false,_;
            end if;
        elif IsPowerOfBass(IsogenyClass(A1)) then
            test,map:=IsIsomorphic(BassModule(A1),BassModule(A2));
            if test then
                return test,Hom(A1,A2,map);
            else
                return test,_;
            end if;
        else
            error "the isomorphism testing is implemented only for squarefree and power-of-Bass isogeny classes"; 
        end if; 
    else
        vprintf AbelianVarieties : "IsIsomorphic : the abelian varities are not in the same isogeny class \n";
        return false,_;
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// Compute all isomorphism classes in a given Isogeny class
/////////////////////////////////////////////////////

intrinsic ComputeIsomorphismClasses( AVh::IsogenyClassFq )->SeqEnum[AbelianVarietyFq]
{ computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class }
    if not assigned AVh`IsomorphismClasses then
        h:=WeilPolynomial(AVh);
        R,map:=ZFVOrder(AVh);
        if IsOrdinary(AVh) or IsCentelegheStix(AVh) then
            if IsSquarefree(AVh) then
                icm:=ICM(R);
                AVh`IsomorphismClasses:=[ AbelianVariety(AVh,I) : I in icm ];
            elif IsPowerOfBass(AVh) then
                all_bc:=AllBassClasses(R,map);
                AVh`IsomorphismClasses:=[ AbelianVariety(AVh,bc) : bc in all_bc ];
            else
                error "implemented only for squarefree and power-of-Bass isogeny classes"; 
            end if;
//        elif IsAlmostOrdinary(AVh) and IsSquarefree(AVh) and IsOdd(FiniteField(AVh)) then
//            import "AlmOrd.m" : overorders_maximal_at_ss ; //needed for the almost ordinary case
//            AVh`IsomorphismClasses:=[ ComputeIsomorphismClassesWithEndomorphismRing(S) : S in overorders_maximal_at_ss(AVh)];
        else
                error "not implemented for such an isogeny class"; 
        end if;
    end if;
    return AVh`IsomorphismClasses;
end intrinsic;

intrinsic ComputeIsomorphismClassesWithEndomorphismRing( AVh::IsogenyClassFq , S::AlgAssVOrd )->SeqEnum[AbelianVarietyFq]
{ computes a list of representatives of isomorphisms classes of abelian varieties with endomorphism ring S in the given squarefree isogeny class }
    require IsSquarefree(AVh) : "the given isogeny class is not squarefree ";
    R,_:=ZFVOrder(AVh);
    require R subset S : "the given order is not the endomorphism ring of an abelian variety in the given isogeny class";
    if assigned AVh`IsomorphismClasses then
        isoS:=[ A : A in ComputeIsomorphismClasses(AVh) | EndomorphismRing(A) eq S ];
    else
        isoS:=[ AbelianVariety(AVh,R!I) : I in ICM_bar(S) ];
    end if;
    return isoS;
end intrinsic;

/////////////////////////////////////////////////////
// other useful instrinsics for Weil polynomials
/////////////////////////////////////////////////////

intrinsic LPolyToWeilPoly(l::RngUPolElt) -> RngUPolElt
{given an L-polynomial l(T) returns the associated Weil polynomial w(T):=T^(2g)*l(1/T)}
    return Parent(l)!Reverse(Coefficients(l));
end intrinsic;

intrinsic WeilPolyToLPoly(w::RngUPolElt) -> RngUPolElt
{given a Weil polynomial w(T) returns the associated L-polynomial l(T):=T^(2g)*l(1/T)}
    return Parent(w)!Reverse(Coefficients(w));
end intrinsic;




intrinsic IsWeil(f::RngUPolElt : Precision:=30) -> BoolElt,RngIntElt,RngIntElt,RngIntElt
{Returns whether f is a q-WeilPolynomial, q,p and e, where q=p^e is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "Precision" given as optional parameter (default precision is 30)}
	require forall{c :c in Coefficients(f) | IsIntegral(c)} and IsEven(Degree(f)): "the input must be an integral polynomial of even degree";
	roots:=Roots(f,ComplexField(Precision));
	q:=Abs(Integers() ! (Coefficients(f)[1]^(2/Degree(f)))); // the Abs is necessary for poly like (x^2-3), 
                                                             // which is a Weil poly, but not a Char poly
    ispp,p,e:=IsPrimePower(q);
	if not ispp then
		return false,_,_,_;
	else
		if forall{r : r in roots | Abs(r[1]*ComplexConjugate(r[1]) - q) lt 10^(-(Precision/2))} then
			return true,q,p,e;
		else 
			return false,_,_,_;
		end if;
	end if;
end intrinsic;

function is_char_poly_irred(f,p,d : Precision:=100)
// Given an irreducible q-Weil polynomial f, returns the exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
// This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}
	Qp:=pAdicField(p,Precision);
	Rp<y>:=PolynomialRing(Qp);
	g:= Rp ! f;
	gfact:=[h[1] : h in Factorization(g)];
	if #RealRoots(f,RealField(Precision),10^(2-Precision)) gt 0 then
		e:=LCM(  [Denominator((Valuation(Coefficients(h)[1])/d)) : h in gfact] cat [2]  ); //the extra 1/2 comes from the real prime, see the reference.
	else
		e:=LCM(  [Denominator((Valuation(Coefficients(h)[1])/d)) : h in gfact]  );
	end if;
	if e eq 1 then 
		return true,e; 
	else 
		return false,e;
	end if;
end function;

intrinsic IsCharacteristicPoly(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt
{ Given polynomial f, returns whether f is the characteristic polynomial of Frobenius of some isogeny class, together with the minimal exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}

    testWeil,q,p,d:=IsWeil(f : Precision:=Precision);
	require testWeil: "the input must be a q-Weil polynomial";
    fac:=Factorization(f);
    exps:=[];
    tests:=[];
    for g in fac do
        _,eg:=is_char_poly_irred(g[1],p,d);
        Append(~exps,eg);
        Append(~tests,g[2] mod eg eq 0);
    end for;
    return &and(tests),LCM(exps);
end intrinsic;

/* TESTS
 
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    time IsogenyClass(f);
    time ZFVOrder(IsogenyClass(f));
    time pRank(IsogenyClass(f));
    time pRank(IsogenyClass(f : Check:=false ));
    IsOrdinary(f);
    
    AVf:=IsogenyClass(f);
    IsOrdinary(AVf);
    _:=ComputeIsomorphismClasses(AVf);
    time #ComputeIsomorphismClasses(AVf);
    for A,B in ComputeIsomorphismClasses(AVf) do t,s:=IsIsomorphic(A,B); end for;

    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    time AVf:=IsogenyClass(f^3 );
    time AVf:=IsogenyClass(f^3 : Check:=false );
    FrobeniusEndomorphism(AVf);
    iso:=ComputeIsomorphismClasses(AVf);
    time #ComputeIsomorphismClasses(AVf); //it should be 0
    for A in iso do
        FrobeniusEndomorphism(A);
    end for;
    for A,B in iso do 
        t,s:=IsIsomorphic(A,B);
    end for;

    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    h:=x^2-x+2;
    AVf:=IsogenyClass(h*f^2);
    iso:=ComputeIsomorphismClasses(AVf); //this should give an error
    ZFV:=ZFVOrder(AVf);


*/
