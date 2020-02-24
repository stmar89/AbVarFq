/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Abelian varieties and Isogeny classes
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

/* REFERENCES:
[Wat69] W. C. Waterhouse. Abelian varieties over finite fields. Ann. Sci. École Norm. Sup. (4), 2:521–560, 1969. 45, 53, 54
*/

/* TODO:
- pRank, Functor
- projection and inclusions of isogenyclasses
*/


/////////////////////////////////////////////////////
// defining the type IsogenyClassFq
/////////////////////////////////////////////////////

declare type IsogenyClassFq;
declare attributes IsogenyClassFq : WeilPolynomial, //the characteristic polynomial of the Frobenius
                                    FiniteField, // the prime power q=p^e
                                    CharacteristicFiniteField, // the prime p
                                    Dimension, // the dimension
                                    UniverseAlgebra, //the AlgAss that contains all the DeligneModules. eg. if h=g1^s1*g2^s2 then it equals (Q[x]/g1)^s1 x (Q[x]/g2)^s2 
                                    ZFV, //a pair <Z[F,q/F], delta>, where F is the Frobenius endomorphism and delta:Q(F)->EndomorphismAlgebra which gives the (diagonal) action of the Frobenius on the endomorphism algebra. 
                                    IsomorphismClasses, //a sequence of DeligneModules representing the isomorphism classes inside the isogeny class
                                    CMType; //the same as above
// TODO
//                                  pRank, // the p-rank
//                                  Functor, //a string describing which functor is used to describe the category "Deligne", "Centeleghe-Stix", "Oswal=Shankar"

/////////////////////////////////////////////////////
// Creation and access functions of IsogenyClassFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( h::RngUPol ) -> IsogenyClassFq
{ given a WeilPolynomial h creates the isogeny class determined by h via Honda-Tate theory }
    test_weil,q,p:=IsWeil(h);
    require test_weil : "the given polynomial is not a Weil polynomial";
    fac:=Factorization(h);
    require forall{f : f in fac | IsCharactersiticPolynomial(f[1]^f[2]) } : "the given polynomial does not define an isogeny class";

    I:=New(IsogenyClassFq);
    I`WeilPolynomial:=h;
    I`FiniteField:=q;
    I`CharacteristicFiniteField:=p;
    I`Dimension:=Degree(h) div 2;
    //TODO pRank and functor
    nf_h:=&cat[[ NumberField(f[1]) : i in [1..f[2]] ] : f in fac]; 
    Ah:=AssociativeAlgebra(nf_h);
    I`UniverseAlgebra:=Ah;
    if IsSquarefree(h) then
        Ag:=Ah;
        delta:=hom<Ag->Ah | [Ah.i : i in [1..Dimension(Ah)]] >; //this is just the identity
    else
        nf_g:=&cat[[ NumberField(f[1]) ] : f in fac]; 
        Ag:=AssociativeAlgebra(nf_g);
        i:=0;
        img:=[];
        for f in fac do
            img cat:=[ &+[ Ah.(i+j) : k in [1..f[2]]] : j in [1..Degree(f[1])] ];
            i:=i+Degree(f[1])*f[2];
        end for;
        delta:=hom<Ag->Ah | img >;
    end if;
    F:=PrimitiveElement(Ag); //the Frobenius
    ZFV:=Order([F,q/F]);
    I`ZFV:=<ZFV,delta>;
    return I;
end intrinsic;

intrinsic WeilPolynomial( I::IsogenyClassFq )-> RngUpol
{ given an isogeny class AV(h) returns the Weil polynomial h defining it }
    return I`WeilPolynomial;
end intrinsic;

intrinsic FiniteField( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the size of the finite field of definition }
    return I`FiniteField;
end intrinsic;

intrinsic CharacteristicFiniteField( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the characteristic of the finite field of definition }
    return I`CharacteristicFiniteField;
end intrinsic;

intrinsic Dimension( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the dimension }
    return I`Dimension;
end intrinsic;

intrinsic UniverseAlgebra( I::IsogenyClassFq )-> AlgAss
{ given an isogeny class AV(h) returns the algebra where all the Deligne modules live in }
    return I`UniverseAlgebra;
end intrinsic;

intrinsic ZFV(I::IsogenyClassFq)-> AlgAssVOrd,Map
{ given an isogeny class AV(h) returns the algebra where all the Deligne modules live in }
    return I`ZFV[1],I`ZFV[2];
end intrinsic;

intrinsic Print(I::IsogenyClassFq)
{ print the isogeny class}
    printf "Isogeny class of abelian varieties over FF_%o defined by the Weil polynomial %o",FiniteField(I),WeilPolynomial(I);
end intrinsic;

intrinsic 'eq'(AVh1::IsogenyClassFq , AVh2::IsogenyClassFq ) -> BoolElt
{ checks if two isogeny classes are the equal }
    if WeilPolynomial(AVh1) eq WeilPolynomial(AVh2) then
        assert2 UniverseAlgebra(AVh1) eq UniverseAlgebra(AVh2);
        assert2 ZFV(AVh1) eq ZFV(AVh2);
        return true;
    else
        return false;
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// defining the type AbelianVarietyFq
/////////////////////////////////////////////////////

declare type AbelianVarietyFq;
declare attributes AbelianVarietyFq : IsogenyClass,
                                      DeligneModuleZBasis,
                                      DeligneModuleAsDirectSum, //not all DeligneModules can be written as a direct sum. but if this is the case, here we store a sequence of pairs <J,m>, where J is a fractional Z[F,V] ideal and m is a map from the Algebr(J) to the UniverseAlgebra of the isogeny class.
                                      GroupOfRationalPoints,
                                      Polarizations,
                                      DualVariety;

/////////////////////////////////////////////////////
// Creation  functions of AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic AbelianVarietyFq( AVh::IsogenyClassFq , I::AlgAssVOrdIdl )->AbelianVarietyFq
{ returns the abelian variety defined by a fractional ideal I of the Z[F,V] order of the isogeny class AV(h), where h is the characteristic polynomial of the Frobenius } 
    R,delta:=ZFV(AVh);
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


intrinsic AbelianVarietyFq( AVh::IsogenyClassFq , seq::SeqEnum[AlgAssVOrdIdl] )-> AbelianVarietyFq
{ returns the abelian variety defined by a direct sum of s fractional ideals  of the Z[F,V] order of the isogeny class AV(g^s), where g is the square-free characteristic polynomial of the Frobenius } 
    R,delta:=ZFV(AVh);
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
        map:=hom<Algebra(R)->UA | [UA.i : i in [i0..i0+Degree(g)] ]>; // embedding of Ag->Ag^s into the ith component
        Append(~DM,<I,map>);
    end for;    
    AV`DeligneModule:=DM;
    AV`DeligneModuleZBasis:=&cat[ [ M[2](z) : z in ZBasis(M[1]) ] : M in DM];
    return AV;
end intrinsic;

intrinsic AbelianVarietyFq( AVh::IsogenyClassFq , seq::SeqEnum[Tup] )-> AbelianVarietyFq
{ given an isogeny class and sequence of pairs  <J_i,v_i> returns the abelin variety in the given isogeny class defined by the Deligne Module J_1v_1+...+J_sv_s }
    R,delta:=ZFV(AVh);
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
        Append(~DM,<I,map>);
    end for;    
    AV`DeligneModule:=DM;
    AV`DeligneModuleZBasis:=&cat[ [ M[2](z) : z in ZBasis(M[1]) ] : M in DM];
    return AV;
end intrinsic;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( A::AbelianVarietyFq) -> IsogenyClassFq
{ returns the isogeny class of the given abelian variety }
    return A`IsogenyClass;
end intrinsic;

intrinsic DeligneModuleZBasis( A :: AbelianVarietyFq) -> SeqEnum[AlgAssElt]
{ returns the DeligneModule defining the variety A }
    return A`DeligneModuleZBasis;
end intrinsic;

intrinsic DeligneModuleAsDirectSum( A :: AbelianVarietyFq) -> SeqEnum[Tup]
{ returns the DeligneModule defining the variety A given as a sequence of pairs <J,m> where J is a fractional Z[F,V] ideal and m is a map from Algebra(J) to the UniverseAlgebra of the isogeny class }
    return A`DeligneModuleAsDirectSum;
end intrinsic;

intrinsic FiniteField( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the size of the finite field of definition }
    return IsogenyClass(A)`FiniteField;
end intrinsic;

intrinsic CharacteristicFiniteField( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the characteristic of the finite field of definition }
    return IsogenyClass(A)`CharacteristicFiniteField;
end intrinsic;

intrinsic Dimension( I::IsogenyClassFq )-> RngInt
{ given an isogeny class AV(h) returns the dimension }
    return IsogenyClass(A)`Dimension;
end intrinsic;


intrinsic UniverseAlgebra( A :: AbelianVarietyFq) -> AlgAss
{ returns the UniverseAlgebra where the DeligneModule lives in }
    return IsogenyClass(A)`Universelgebra;
end intrinsic;

intrinsic ZFV( A :: AbelianVarietyFq) -> AlgAssVOrd,Map
{ returns the ZFV of the isogeny class of A }
    return IsogenyClass(A)`ZFV;
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

intrinsic 'eq'( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt
{ checks if two abelin varieties are equal the equal }
    if IsogenyClass(A1) eq IsogenyClass(A2) then
        gens1:=DeligneModuleAsZBasis(A1);
        gens2:=DeligneModuleAsZBasis(A2);
        return isHNFeq(gens1,gens2);
    else
        vprintf AbelianVarieties : "eq : the abelian varities are not in the same isogeny class \n";
        return false;
    end if;
end intrinsic;

intrinsic IsIsomorphic( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt
{ checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism from the common UniverseAlgebra  }
    if IsogenyClass(A1) eq IsogenyClass(A2) then
        h:=WeilPolynomial(A1);
        ZFV,mZFV:=ZFV(A1);
        g:=DefiningPolynomial(Algebra(ZFV));
        DM1:=DeligneModuleAsDirectSum(A1);
        DM2:=DeligneModuleAsDirectSum(A2);
        s:=#DM1;
        assert s eq #DM2;
        if IsSquarefree(h) then
            assert s eq 1;
            I1:=DM1[1,1];
            v1:=DM1[1,2];
            I2:=DM2[1,1];
            v2:=DM2[1,2];
            test,iso_0:=IsIsomorphic2(I1,I2);
            if test then
                assert I1 eq iso_0*I2;
                iso:=v2/(iso_0*v2);
                map:=hom<UniverseAlgebra(A1)->UniverseAlgebra(A2) | x:->iso*x, y:->y/iso >;
                return true,map;
            else
                return false,_;
            end if;
        elif h eq g^s and Bass(ZFV) then
            one:=One(Algebra(ZFV));
            BC1:=[ <M[1],M[2](one)> : M in DM1 ];
            BC2:=[ <M[1],M[2](one)> : M in DM2 ];
            return IsBassIsomorphicWithMap(BC1,BC2);
        else
            error "the isomorphism testing is implemented only for squarefree and power-of-Bass isogeny classes"; 
        end if; 
    else
        vprintf AbelianVarieties : "IsIsomorphic : the abelian varities are not in the same isogeny class \n";
        return false;
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// other useful instrinsics for Weil polynomials
/////////////////////////////////////////////////////

intrinsic LPolyToWeilPoly(l::RngUPolElt) -> RngUPolElt
{given an L-polynomial l(T) returns the associated Weil polynomial w(T):=T^(2g)*l(1/T)}
	R:=Parent(l);
	T:=R.1;
	coeff:=Coefficients(l);
	deg:=Degree(l);
	w:=&+([T^(deg-i)*coeff[i+1] : i in [0..deg]]);
	assert IsWeil(w);
	return w;
end intrinsic;

intrinsic WeilPolyToLPoly(w::RngUPolElt) -> RngUPolElt
{given a Weil polynomial w(T) returns the associated L-polynomial l(T):=T^(2g)*l(1/T)}
	require IsWeil(w): "the input must be a Weil polynomial";
	R:=Parent(w);
	T:=R.1;
	coeff:=Coefficients(w);
	deg:=Degree(w);
	l:=&+([T^(deg-i)*coeff[i+1] : i in [0..deg]]);
	return l;
end intrinsic;

intrinsic IsWeil(f::RngUPolElt : Precision:=3000) -> BoolElt,RngIntElt,RngIntElt,RngIntElt
{Returns whether f is a q-WeilPolynomial, q,p and e, where q=p^e is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "Precision" given as optional parameter (default precision is 30)}
	require forall{c :c in Coefficients(f) | IsIntegral(c)} and IsEven(Degree(f)): "the input must be an integral polynomial of even degree";
	roots:=Roots(f,ComplexField(Precision));
	q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
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

intrinsic IsOrdinary(f::RngUPolElt) -> BoolElt
{returns if the input polynomial is an Ordinary q-Weil polynomial, where q is a power of a prime number p, that is if the mid coefficient is coprime with p}
test,q:=IsWeil(f);
	require test:"the input must be a q-Weil polynomial for some prime power q";
	deg:=Degree(f);
	coeff:=Coefficients(f);
	return IsCoprime(coeff[deg div 2 +1],q);
end intrinsic;

intrinsic IsCharacteristicPoly(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt,RngIntElt,RngIntElt
{Given an irreducible q-Weil polynomial f, returns the exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}
    testWeil,q,p,d:=IsWeil(f : prec:=Precision);
	require IsIrreducible(f) and testWeil: "the input must be an irreducible q-Weil polynomial";
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
end intrinsic;

