/* vim: set syntax=magma :*/

freeze;

declare verbose AbelianVarieties, 1;
/////////////////////////////////////////////////////
// Abelian varieties with squarefree polynomial, polarizations for the ordinary case and automorphisms
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

import "usefulfunctions.m": AllPossibilities;

/* LIST of functions:
intrinsic HasComplexConjugate(A::AlgAss) -> BoolElt
intrinsic ComplexConjugate(x::AlgAssElt) -> AlgAssElt
intrinsic ComplexConjugate(O::AlgAssVOrd) -> AlgAssVOrd
intrinsic ComplexConjugate(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
intrinsic IsPrincPolarized(I::AlgAssVOrdIdl , phi::SeqEnum[Maps])->BoolElt, SeqEnum[AlgAssElt]
intrinsic IsogeniesMany(IS::SeqEnum[AlgAssVOrdIdl], J::AlgAssVOrdIdl, N::RngIntElt) -> BoolElt, SeqEnum[AlgAssElt]
intrinsic Isogenies(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl, N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
intrinsic IsPolarized(I0::AlgAssVOrdIdl , phi::SeqEnum[Map], N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
intrinsic LPolyToWeilPoly(l::RngUPolElt) -> RngUPolElt
intrinsic WeilPolyToLPoly(w::RngUPolElt) -> RngUPolElt
intrinsic IsWeil(f::RngUPolElt) -> BoolElt,RngIntElt
intrinsic IsOrdinary(f::RngUPolElt) -> BoolElt
intrinsic IsCharacteristicPoly(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt
intrinsic AutomorphismsPol(I::AlgAssVOrdIdl) -> GpAb
cm_type_internal:=function(A,prec)
intrinsic CMType(A::AlgAss)->SeqEnum
*/

/* REFERENCES:
[Wat69] W. C. Waterhouse. Abelian varieties over finite fields. Ann. Sci. École Norm. Sup. (4), 2:521–560, 1969. 45, 53, 54
*/

/* TODO:
- check the Isogeny functions. Edgar Costa added a require on the MultiplicatorRing that I don't understand.
- Drew suggested to use a minimal set of generators for ideals rather than a ZBasis. I need to think about how to produce it.
- create an AbelianVariety container including info about the isogeny class, functor, representative of the isom class, polarizations, ....
*/

intrinsic HasComplexConjugate(A::AlgAss) -> BoolElt
{returns if the algebra is the product of CM fields}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	return forall{L : L in A`NumberFields | HasComplexConjugate(L[1])};
end intrinsic;

intrinsic ComplexConjugate(x::AlgAssElt) -> AlgAssElt
{if A is a product of CM fields, it returns the complex conjugate of the argument}
	A:=Parent(x);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	require HasComplexConjugate(A) : "it is not a product of CM fields";
	comp:=Components(x);
	x_conj:=Zero(A);
	for i in [1..#A`NumberFields] do
		L:=A`NumberFields[i];
		x_conj:=x_conj+L[2](ComplexConjugate(comp[i]));
	end for;
	return x_conj;
end intrinsic;

intrinsic ComplexConjugate(O::AlgAssVOrd) -> AlgAssVOrd
{if A is a product of CM fields, it returns the complex conjugate of the argument}
	A:=Algebra(O);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	require HasComplexConjugate(A) : "it is not a product of CM fields";
	return Order([ ComplexConjugate(x) : x in ZBasis(O) ]);
end intrinsic;

intrinsic ComplexConjugate(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{if A is a product of CM fields, it returns the complex conjugate of the argument}
	O:=Order(I);
	A:=Algebra(O);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	require HasComplexConjugate(A) : "it is not a product of CM fields";
	Ob:=ComplexConjugate(O);
	return ideal<Ob|[ ComplexConjugate(x) : x in ZBasis(I) ]>;
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

intrinsic IsogeniesMany(IS::SeqEnum[AlgAssVOrdIdl], J::AlgAssVOrdIdl, N::RngIntElt) -> BoolElt, List
{Given a sequence of source abelian varieties IS, a target abelian varity J and a positive integet N, it returns for each I in IS if there exist an isogeny I->J of degree N. 
 For each I in IS, if there exists and isogeny I->J, it is also returned a list of pairs [*x,K*] where K=xI subset J (up to isomorphism).}
//by Edgar Costa, modified by Stefano
	vprintf AbelianVarieties : "IsogeniesMany\n";
	isogenies_of_degree_N := [* [* *] : i in [1..#IS] *];
	for K in IdealsOfIndex(J, N) do
		for i := 1 to #IS do
			test, x := IsIsomorphic2(K, IS[i]); //x*I=K
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

intrinsic IsPolarized(I0::AlgAssVOrdIdl, phi::SeqEnum[Map], N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
{returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations}
	require IsFiniteEtale(Algebra(I0)): "the algebra of definition must be finite and etale over Q";
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

intrinsic IsWeil(f::RngUPolElt : Precision:=30) -> BoolElt,RngIntElt
{Returns whether f is a q-WeilPolynomial and q, where q is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "Precision" given as optional parameter (default precision is 30)}
	require forall{c :c in Coefficients(f) | IsIntegral(c)} and IsEven(Degree(f)): "the input must be an integral polynomial of even degree";
	roots:=Roots(f,ComplexField(Precision));
	q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
	if not IsPrimePower(q) then
		return false,_;
	else
		if forall{r : r in roots | Abs(r[1]*ComplexConjugate(r[1]) - q) lt 10^(-(Precision/2))} then
			return true,q;
		else 
			return false,_;
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

intrinsic IsCharacteristicPoly(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt
{Given an irreducible q-Weil polynomial f, returns the exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}
	testWeil,q:=IsWeil(f : prec:=Precision);
	require IsIrreducible(f) and testWeil: "the input must be an irreducible q-Weil polynomial";
	fac:=Factorization(q);
	p:=fac[1,1]; d:=fac[1,2]; //q=p^d, with p a prime
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

intrinsic AutomorphismsPol(I::AlgAssVOrdIdl) -> GpAb
{returns the automorphisms of a polarized abelian variety}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	return TorsionSubgroup(UnitGroup2(MultiplicatorRing(I)));
end intrinsic;

cm_type_internal:=function(A,prec)
// "prec" is a precision parameter
	P<x>:=PolynomialRing(Integers());
	fA:=P!DefiningPolynomial(A);
	q:=Integers() ! ( Coefficients(fA)[1]^(2/Degree(fA)) );
	_,p:=IsPrimePower(q);
	M:=NumberField(P!DefiningPolynomial(SplittingField(fA))); //this is the compositum
	frob_in_M:=[[-Coefficients(h[1])[1] : h in Factorization(PolynomialRing(M)!DefiningPolynomial(L[1])) ] : L in A`NumberFields ]; //conjugates of the Frobenius in M
	//here we use Montes algorithm. One need to Attach +IdealsNF.m !!!!
	fac:=Factorization(ideal(M,p)); //the assignement is just to avoid the printing
	PM:=M`PrimeIdeals[p,1]; // we choose a prime of M above p
	Cvalues_p_pos:=[ [Conjugates(c : Precision:=prec)[1] : c in fr | PValuation(c,PM) gt 0]  : fr in frob_in_M ]; // note that the function PValuation is also from the +IdealsNF.m package
	homsA:=HomsToC(A : Precision:=prec);
	all_cm_types:=[ListToSequence(cm) : cm in AllPossibilities([ [homsA[2*k-1],homsA[2*k]] : k in [1..Degree(fA) div 2 ]])];
	FA:=PrimitiveElement(A);
	cm_p_pos:=[];
	for cm in all_cm_types do
		cm_values0:=[ h(FA) : h in cm];
		cm_values:=[];
		deg_prev:=0;
		for i1 in [1..#A`NumberFields] do
			deg1:=Degree(A`NumberFields[i1,1]) div 2;
			Append(~cm_values,cm_values0[deg_prev+1..deg_prev+deg1]);
			deg_prev:=deg_prev+deg1;
		end for;
		if forall{ i : i in [1..#cm_values] | forall{ d : d in cm_values[i] | exists{ c : c in Cvalues_p_pos[i] | Abs(d-c) lt 10^(2-prec) } } } then
		Append(~cm_p_pos,cm);
		end if;
	end for;
	A`CMType:=cm_p_pos;
	return cm_p_pos;
end function;

intrinsic CMType(A::AlgAss : Precision:=30 , TestOrdinary:=true)->SeqEnum[Maps]
{given a product of CM number fields A=Q[x]/(f), where f is q-Weil polynomial, returns a subset of HomsToC consisting of one map A->C per conjugate pair such that the induced p-adic valuation v on \bar(Q_p) in C is such that v(a)>0, where a is a root of f. If f is ordinary then it should return only one output. Otherwise more. The precision of the computations is set by the optional parameter "Precision" (Default Value 30).}
	f:=DefiningPolynomial(A);
	test_Weil,q:=IsWeil(f);
	require test_Weil: "the defining polynomial must be a q-Weil polynomial";
	if TestOrdinary then
		require IsOrdinary(f): "The isogeny class is not ordinary";
	end if;
	if assigned A`CMType then 
		return A`CMType;
	else
		require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
		require HasComplexConjugate(A): "it must be a product of CM number fields";
		return cm_type_internal(A, Precision);
	end if;
end intrinsic;
