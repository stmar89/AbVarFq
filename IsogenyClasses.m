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
- Functor
- projection and inclusions of isogenyclasses
*/


/////////////////////////////////////////////////////
// New Type IsogenyClassFq
/////////////////////////////////////////////////////

declare type IsogenyClassFq;
declare attributes IsogenyClassFq : 
           WeilPolynomial,  // The characteristic polynomial of the Frobenius
           WeilPolynomialFactorization,
           FiniteField,     // The prime power q=p^e
           CharacteristicFiniteField, // The prime p
           Dimension,       // The dimension
           NumberOfPoints,  // Number of points
           UniverseAlgebra, // An AlgEtQ constructed from the Weil polynomial. 
                            // eg. if h=g1^s1*g2^s2 then it equals (Q[x]/g1)^s1 x (Q[x]/g2)^s2 
                            // In the ordinary or Centeleghe-Stix case, it contains the Deligne modules.
           ZFV,             // A pair <Z[F,q/F], delta>, where F is a root of the Weil poly h(x) in Q[x]/h,
                            // and delta:Q[F]->EndomorphismAlgebra which gives the (diagonal) action of 
                            // the Frobenius on the endomorphism algebra. 
           FrobeniusEndomorphismOnUniverseAlgebra, 
                            // An endomorphism of the UniverseAlgebra representing the Frobenius.
           IsomorphismClasses, 
                            // A sequence of of representatives of the isomorphism classes
           IsSquarefree,    // If the Weil polynomial is squarefree. By a Theorem of Tate this is equivalent to 
                            // to have commutative End^0. In this case, we have End^0 = Algebra(ZFV) = Q[F].
           IsPowerOfBass,   // If UniverseAlgebra = Q[F]^s for some s, and ZFV is Bass. 
           pRank;           // The p-rank
//         Functor, //a string describing which functor is used to describe the category "Deligne", "Centeleghe-Stix", "Oswal-Shankar"

/////////////////////////////////////////////////////
// Creation and access functions of IsogenyClassFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( h::RngUPolElt : Check:=true ) -> IsogenyClassFq
{Given a WeilPolynomial h creates the isogeny class determined by h via Honda-Tate theory. The Check parameter (Default true) allows to decide whether to test if the polynomial defines an isogeny class (see IsCharacteristicPoly).}
    if Check then
        require IsCharacteristicPoly(h) : "the given polynomial does not define an isogeny class";
    end if;

    I:=New(IsogenyClassFq);
    I`WeilPolynomial:=h;
    if assigned fac then
        I`WeilPolynomialFactorization:=fac;
    end if;
    return I;
end intrinsic;

intrinsic WeilPolynomial( I::IsogenyClassFq )-> RngUpolElt
{Given an isogeny class AV(h) returns the Weil polynomial h defining it.}
    return I`WeilPolynomial;
end intrinsic;

intrinsic WeilPolynomialFactorization( I::IsogenyClassFq )-> RngUpolElt
{Given an isogeny class AV(h) returns the factorization over Q of Weil polynomial h defining it.}
    if not assigned I`WeilPolynomialFactorization then
        I`WeilPolynomialFactorization:=Factorization(WeilPolynomial(I));
    end if;
    return I`WeilPolynomialFactorization;
end intrinsic;

intrinsic UniverseAlgebra( I::IsogenyClassFq )-> AlgEtQ
{Given an isogeny class AV(h), defined by the Weil polynomial h with factorization over Q equal to h=g1^s1*...*gn^sn, it returns the algebra V=prod_i=1^n (Q[x]/gi)^si.}
    if not assigned I`UniverseAlgebra then
        nf_h:=&cat[[ NumberField(f[1]) : i in [1..f[2]] ] : f in WeilPolynomialFactorization(I)]; 
        Ah:=EtaleAlgebra(nf_h);
        I`UniverseAlgebra:=Ah;
    end if;
    return I`UniverseAlgebra;
end intrinsic;

intrinsic ZFVOrder(I::IsogenyClassFq)-> AlgEtQOrd,Map
{Given an isogeny class AV(h) defined by the Weil polynomial h with factorization over Q equal to h=g1^s1*...*gn^sn, returns the order Z[F,q/F]  in the algebra Q[F]=Q[x]/g where g = prod_i gi.}
    if not assigned I`ZFV then
        h:=WeilPolynomial(I); 
        fac:=WeilPolynomialFactorization(I);
        Ah:=UniverseAlgebra(I);
        if IsSquarefree(h) then
            I`IsSquarefree:=true;
            Ag:=Ah;
            delta:=hom<Ag->Ah | [Ah.i : i in [1..Dimension(Ah)]] >; //this is just the identity
        else
            nf_g:=&cat[[ NumberField(f[1]) ] : f in fac]; 
            Ag:=EtaleAlgebra(nf_g);
            i:=0;
            img:=[];
            abs:=AbsoluteBasis(Ah);
            for f in fac do
                img cat:=[ &+[ abs[i+j+k*Degree(f[1])] : k in [0..f[2]-1]] : j in [1..Degree(f[1])] ];
                i:=i+Degree(f[1])*f[2];
            end for;
            delta:=Hom(Ag,Ah,img);
            assert delta(One(Ag)) eq One(Ah); 
        end if;
        F:=PrimitiveElement(Ag); //the Frobenius
        q:=FiniteField(I);
        ZFV:=Order([F,q/F]);
        I`ZFV:=<ZFV,delta>;
    end if;
    return I`ZFV[1],I`ZFV[2];
end intrinsic;

intrinsic FiniteField( I::IsogenyClassFq )-> RngInt
{Given an isogeny class AV(h) returns the size of the finite field of definition.}
    if not assigned I`FiniteField then 
        h:=WeilPolynomial(I);
        I`FiniteField:=Integers() ! (ConstantCoefficient(h)^(2/Degree(h)));
    end if;
    return I`FiniteField;
end intrinsic;

intrinsic CharacteristicFiniteField( I::IsogenyClassFq )-> RngInt
{Given an isogeny class AV(h) returns the characteristic of the finite field of definition.}
    if not assigned I`CharacteristicFiniteField then
        test,p,_:=IsPrimePower(FiniteField(I));
        assert test;
        I`CharacteristicFiniteField:=p;
    end if;
    return I`CharacteristicFiniteField;
end intrinsic;

intrinsic Dimension( I::IsogenyClassFq )-> RngInt
{Given an isogeny class AV(h) returns the dimension.}
    if not assigned I`Dimension then
        I`Dimension:=Degree(WeilPolynomial(I)) div 2;
    end if;
    return I`Dimension;
end intrinsic;

intrinsic NumberOfPoints( I::IsogenyClassFq )-> RngInt
{Given an isogeny class AV(h) returns the number of rational points of the abelian varities in the isogeny class.}
    if not assigned I`NumberOfPoints then
        I`NumberOfPoints := Evaluate(WeilPolynomial(I),1);
    end if;
    return I`NumberOfPoints;
end intrinsic;

intrinsic FrobeniusEndomorphism(I::IsogenyClassFq)-> Map
{Given an isogeny class AV(h) returns the Frobenius endomorphism (acting on the UniverseAlgebra).}
    if not assigned I`FrobeniusEndomorphismOnUniverseAlgebra then
        UA:=UniverseAlgebra(I);
        R,mR:=ZFVOrder(I);
        FUA:=mR(PrimitiveElement(Algebra(R)));
        abs:=AbsoluteBasis(UA);
        F:=Hom(UA,UA,[FUA*abs[i] : i in [1..Dimension(UA)] ]);
        I`FrobeniusEndomorphismOnUniverseAlgebra:=F;
    end if;
    return I`FrobeniusEndomorphismOnUniverseAlgebra;
end intrinsic;

intrinsic IsSquarefree(I::IsogenyClassFq)-> BoolElt
{Given an isogeny class AV(h) returns whether h is squarefree.}
    if not assigned I`IsSquarefree then
        I`IsSquarefree:=IsSquarefree(WeilPolynomial(I));
    end if;
    return I`IsSquarefree;
end intrinsic;

intrinsic IsPowerOfBass(I::IsogenyClassFq)-> BoolElt
{Given an isogeny class AV(h) returns whether h is a pure power and ZFV is a Bass Order.}
    if not assigned I`IsPowerOfBass then
        h:=WeilPolynomial(I);
        ZFV:=ZFVOrder(I);
        g:=DefiningPolynomial(Algebra(ZFV));
        I`IsPowerOfBass:=( (Degree(h) mod Degree(g)) eq 0 ) and IsBass(ZFV);
        assert I`IsPowerOfBass select h eq g^(Degree(h) div Degree(g)) else true;
    end if;
    return I`IsPowerOfBass;
end intrinsic;

intrinsic Print(I::IsogenyClassFq)
{Prints the isogeny class.}
    printf "Isogeny class of abelian varieties over FF_%o defined by the Weil polynomial %o",FiniteField(I),WeilPolynomial(I);
end intrinsic;

intrinsic 'eq'(AVh1::IsogenyClassFq , AVh2::IsogenyClassFq ) -> BoolElt
{Checks if the Weil polynomials are the same. It controls that the Universe algbras and ZFV orders are equal as well (to avoid double definitions).}
    if WeilPolynomial(AVh1) eq WeilPolynomial(AVh2) then
        assert UniverseAlgebra(AVh1) eq UniverseAlgebra(AVh2);
        assert ZFVOrder(AVh1) eq ZFVOrder(AVh2);
        return true;
    else
        return false;
    end if;
end intrinsic;



/////////////////////////////////////////////////////
// pRank and related
/////////////////////////////////////////////////////

intrinsic IsOrdinary(AVf::IsogenyClassFq) -> BoolElt
{Returns if the isogeny class is ordinary.}
    if assigned AVf`pRank then 
        return pRank(AVf) eq Dimension(AVf);
    else
        f:=WeilPolynomial(AVf);
        coeff:=Coefficients(f);
        test:=IsCoprime(coeff[Degree(f) div 2 +1], coeff[1] );
        if test then
            AVf`pRank:=Dimension(AVf);
        end if;
        return test;
    end if;
end intrinsic;

intrinsic IsOrdinary(A::AbelianVarietyFq) -> BoolElt
{Returns if the abelian variety is ordinary.}
	return IsOrdinary(IsogenyClass(A));
end intrinsic;

intrinsic IsOrdinary(f::RngUPolElt : Precision:=100) -> BoolElt
{Returns if the input polynomial is an Ordinary q-Weil polynomial, where q is a power of a prime number p, that is if the mid coefficient is coprime with p.}
    testWeil,_,p,_:=IsWeil(f : Precision:=Precision);
	require testWeil:"the input must be a q-Weil polynomial for some prime power q";
	deg:=Degree(f);
	coeff:=Coefficients(f);
	return IsCoprime(coeff[deg div 2 +1],p);
end intrinsic;

intrinsic pRank(I::IsogenyClassFq)->RngIntElt
{Returns the p-Rank of the isogeny class.}
    if not assigned I`pRank then
        f:=WeilPolynomial(I);
        p:=CharacteristicFiniteField(I);  
        vv:=InnerVertices(NewtonPolygon(f,p));
        I`pRank:=Degree(f)-vv[#vv,1];
    end if;
    return I`pRank;
end intrinsic;

intrinsic pRank(A::AbelianVarietyFq)->RngIntElt
{Returns the p-Rank of the isogeny class.}
    return pRank(IsogenyClass(A));
end intrinsic;

intrinsic IsAlmostOrdinary(I::IsogenyClassFq)->BoolElt
{Returns whether the isogeny class is almost ordinary.}
    return pRank(I) eq Dimension(I)-1;
end intrinsic;

intrinsic IsAlmostOrdinary(A::AbelianVarietyFq)->BoolElt
{Returns whether the abelian variety is almost ordinary.}
    return pRank(A) eq Dimension(A)-1;
end intrinsic;

intrinsic IsCentelegheStix(I::IsogenyClassFq : Precision:=30 )->BoolElt 
{Returns whether the isogeny class is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.}
    q:=FiniteField(I);
    if IsPrime(q) then
        h:=WeilPolynomial(I);
        rr:=Roots(h,ComplexField(Precision));
        return forall{ r : r in rr | not Abs(Im(r[1])) lt 10^-(Precision div 2) }; // no real roots
    else 
        return false;
    end if;
end intrinsic;

intrinsic IsCentelegheStix(I::AbelianVarietyFq : Precision:=30 )->BoolElt
{Returns whether the abelian variety is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.}
    return IsCentelegheStix(IsogenyClass(I));
end intrinsic;
