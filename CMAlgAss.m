/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Complex Multiplication for AlgAss
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

//
//TODO the computation of the CM-type should be updates using the instrinsics in padictocc.m
//TODO intrinsics for CM-type should have as input an isogeny class
//TODO CMType should be a New Type ?

declare verbose CMAlgAss, 1;
declare attributes AlgAss : CMType;

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


/////////////////////////////////////////////////////
// old way to compute the CM-type for both ordinary and non-ordinary abelian varieties
/////////////////////////////////////////////////////


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
    all_cm_types:=[[phi : phi in cm] : cm in CartesianProduct(< [homsA[2*k-1],homsA[2*k]] : k in [1..Degree(fA) div 2 ]>)];
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




