/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Stefano Marseglia, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// 
// Distributed under the terms of the GNU Lesser General Public License (L-GPL)
//      http://www.gnu.org/licenses/
// 
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation; either version 3.0 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA
// 
// Copyright 2024, S. Marseglia
/////////////////////////////////////////////////////

/////////////////////////////////////////////////////
// Abelian varieties and Isogeny classes
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

/* TODO:
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
           ZFV,             // A pair <Z[F,q/F], delta>, where F is a root of the Weil poly h(x) in Q[x]/h,
                            // and delta:Q[F]->EndomorphismAlgebra which gives the (diagonal) action of 
                            // the Frobenius on the endomorphism algebra. 
           IsomorphismClasses, 
                            // A sequence of of representatives of the isomorphism classes
           IsSquarefree,    // If the Weil polynomial is squarefree. By a Theorem of Tate this is equivalent to 
                            // to have commutative End^0. In this case, we have End^0 = Algebra(ZFV) = Q[F].
           IsPurePower,     // If h=g^s for some s, where h is the Weil poly and g is squarefree
           IsPowerOfBass,   // If IsPurePower and ZFV is Bass. 
           IsCentelegheStix,// If the isogeny class is over Fp and the char poly has no real roots
           pRank;           // The p-rank
//         Functor, //a string describing which functor is used to describe the category "Deligne", "Centeleghe-Stix", "Oswal-Shankar"

/////////////////////////////////////////////////////
// Testing if a poly is a Weil/char poly
/////////////////////////////////////////////////////

intrinsic IsWeil(f::RngUPolElt : prec:=Precision(GetDefaultRealField())) -> BoolElt,RngIntElt,RngIntElt,RngIntElt
{Returns whether f is a q-WeilPolynomial, q,p and e, where q=p^e is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "prec" given as optional parameter (default precision is 30)}
	require forall{c :c in Coefficients(f) | IsIntegral(c)} and IsEven(Degree(f)): "the input must be an integral polynomial of even degree";
	roots:=Roots(f,ComplexField(prec));
	q:=Abs(Integers() ! (Coefficients(f)[1]^(2/Degree(f)))); // the Abs is necessary for poly like (x^2-3), 
                                                             // which is a Weil poly, but not a Char poly
    ispp,p,e:=IsPrimePower(q);
	if not ispp then
		return false,_,_,_;
	else
		if forall{r : r in roots | Abs(r[1]*ComplexConjugate(r[1]) - q) lt 10^(-(prec/2))} then
			return true,q,p,e;
		else 
			return false,_,_,_;
		end if;
	end if;
end intrinsic;

function is_char_poly_irred(f,p,d : prec:=100)
// Given an irreducible q-Weil polynomial f, returns the exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
// This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}
	Qp:=pAdicField(p,prec);
	Rp<y>:=PolynomialRing(Qp);
	g:= Rp ! f;
	gfact:=[h[1] : h in Factorization(g)];
	if #RealRoots(f,RealField(prec),10^(2-prec)) gt 0 then
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

intrinsic IsCharacteristicPoly(f::RngUPolElt : prec:=100) -> BoolElt,RngIntElt
{ Given polynomial f, returns whether f is the characteristic polynomial of Frobenius of some isogeny class, together with the minimal exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}

    testWeil,q,p,d:=IsWeil(f : prec:=prec);
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

intrinsic ZFVOrder(I::IsogenyClassFq)-> AlgEtQOrd,Map
{Given an isogeny class AV(h) defined by the Weil polynomial h with factorization over Q equal to h=g1^s1*...*gn^sn, returns the order Z[F,q/F]  in the algebra Q[F]=Q[x]/g where g = prod_i gi.}
    if not assigned I`ZFV then
        h:=WeilPolynomial(I); 
        fac:=WeilPolynomialFactorization(I);
        fac_sqfree:=&*[f[1]:f in fac];
        E:=EtaleAlgebra(fac_sqfree);
        F:=PrimitiveElement(E); //the Frobenius
        q:=FiniteField(I);
        ZFV:=Order([F,q/F]);
        I`ZFV:=ZFV;
    end if;
    return I`ZFV;
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

intrinsic IsSquarefree(I::IsogenyClassFq)-> BoolElt
{Given an isogeny class AV(h) returns whether h is squarefree.}
    if not assigned I`IsSquarefree then
        I`IsSquarefree:=IsSquarefree(WeilPolynomial(I));
    end if;
    return I`IsSquarefree;
end intrinsic;

intrinsic IsPurePower(I::IsogenyClassFq)-> BoolElt
{Given an isogeny class AV(h) returns whether h is a pure power.}
    if not assigned I`IsPurePower then
        h:=WeilPolynomial(I);
        g:=DefiningPolynomial(Algebra(ZFVOrder(I)));
        I`IsPurePower:=h eq g^(Degree(h) div Degree(g));
    end if;
    return I`IsPurePower;
end intrinsic;

intrinsic IsPowerOfBass(I::IsogenyClassFq)-> BoolElt
{Given an isogeny class AV(h) returns whether h is a pure power and ZFV is a Bass Order.}
    if not assigned I`IsPowerOfBass then
        ZFV:=ZFVOrder(I);
        I`IsPowerOfBass:=IsPurePower(I) and IsBass(ZFV);
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

intrinsic IsOrdinary(f::RngUPolElt : prec:=100) -> BoolElt
{Returns if the input polynomial is an Ordinary q-Weil polynomial, where q is a power of a prime number p, that is if the mid coefficient is coprime with p.}
    testWeil,_,p,_:=IsWeil(f : prec:=prec);
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

intrinsic IsCentelegheStix(I::IsogenyClassFq : prec:=Precision(GetDefaultRealField()) )->BoolElt 
{Returns whether the isogeny class is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.}
    if not assigned I`IsCentelegheStix then
        q:=FiniteField(I);
        if IsPrime(q) then
            h:=WeilPolynomial(I);
            rr:=Roots(h,ComplexField(prec));
            I`IsCentelegheStix:=forall{r : r in rr |not Abs(Im(r[1])) lt 10^-(prec div 2) }; // no real roots
        else 
            I`IsCentelegheStix:=false;
        end if;
    end if;
    return I`IsCentelegheStix;
end intrinsic;

intrinsic IsCentelegheStix(I::AbelianVarietyFq : prec:=Precision(GetDefaultRealField()) )->BoolElt
{Returns whether the abelian variety is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.}
    return IsCentelegheStix(IsogenyClass(I));
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
