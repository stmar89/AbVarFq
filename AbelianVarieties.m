/* vim: set syntax=magma :*/

freeze;

declare verbose AbelianVarieties, 1;
/////////////////////////////////////////////////////
// Abelian varieties with squarefree polynomial, polarizations for the ordinary case and automorphisms
// Stefano Marseglia, Stockholm University, stefanom@math.su.se
// http://staff.math.su.se/stefanom/
/////////////////////////////////////////////////////

import "usefulfunctions.m": AllPossibilities;

/*
version 0.6->0.7 : modifications in the computation of the CM-type. I use the SplittingField(f) for f, which returns the Compositum of the SplittingFields of the irreducible factors of f. Then I compute in it the roots of f. Finally we use Montes algorithm to factor p and compute the cm-type with positive p-adic valuations.
version 0.5->0.6 : correction in CM-type. The mistake was that in the non-irreducible case, the compotutation of the cm-types of the various components should not be performed independently, but in compositum of the splittingfields.
                   This is because if there are inclusions between the components then the choice of the embeddings is not free.
version 0.4->0.5 : CMType has been improved: to compute the factorization of p in the SplittingField(f) we use the Decomposition of p in the pMaximalOrder instead of that in the MaximalOrder, which is much faster to compute. (Thanks to Carlo Sircana for the idea)
version 0.3->0.4 : CMType has been improved (we use SplittingField(f) instead of SplittingField(K) and we do not compute the Automorphisms of KK)
version 0.2->0.3 : the part about complex multiplication has been moved from Ordersext_0.10
                   when for an S-ideal I, ComplexConjugate generates the ideal over \bar(S) (which is the same when S=\bar(S)).
                   in IsPrincPolarized we check if the endom ring is complex conjugate stable
                   assert Itbar eq TraceDualIdeal(ComplexConjugate(I)) has been modified, since the ideals will have different order of definition
version 0.1->0.2 : IsPolarized introduced and IsPrincPolarized modified as a consequence.
                   CMType has now an optional input TestOrdinary set to True by default.
                   Cleaning of the code. publication on the webpage 13/04
*/

/* LIST of functions:
intrinsic HasComplexConjugate(A::AlgAss) -> BoolElt
intrinsic ComplexConjugate(x::AlgAssElt) -> AlgAssElt
intrinsic ComplexConjugate(O::AlgAssVOrd) -> AlgAssVOrd
intrinsic ComplexConjugate(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
intrinsic IsPrincPolarized(I::AlgAssVOrdIdl , phi::SeqEnum[Maps])->BoolElt, SeqEnum[AlgAssElt]
intrinsic IsPolarized(I0::AlgAssVOrdIdl , phi::SeqEnum[Map], N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
intrinsic LPolyToWeilPoly(l::RngUPolElt) -> RngUPolElt
intrinsic WeilPolyToLPoly(w::RngUPolElt) -> RngUPolElt
intrinsic IsWeil(f::RngUPolElt) -> BoolElt,RngIntElt
intrinsic IsOrdinary(f::RngUPolElt) -> BoolElt
intrinsic IsCharacteristicPoly(f::RngUPolElt) -> BoolElt,RngIntElt
intrinsic AutomorphismsPol(I::AlgAssVOrdIdl) -> GpAb
intrinsic CMType(A::AlgAss)->SeqEnum
*/

/* REFERENCES:
[Wat69] W. C. Waterhouse. Abelian varieties over finite fields. Ann. Sci. École Norm. Sup. (4), 2:521–560, 1969. 45, 53, 54
*/

/* TODO:
-Reorganize the packages in such a way that it is easier to save the isogeny class of abelian varieties;
-Add saving functions;
-Add function that from a weil poly spits out the iso classes and the principally polarized classes with automorphisms;
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
//the old code has been removed
    S:=MultiplicatorRing(I);
    if S eq ComplexConjugate(S) then
        return IsPolarized(I, phi , 1);
    else
        return false,[];
    end if;
end intrinsic;




intrinsic IsogeniesMany(IS::SeqEnum[AlgAssVOrdIdl], J::AlgAssVOrdIdl, N::RngIntElt) -> BoolElt, SeqEnum[AlgAssElt]
  {returns if the abelian variety has an isogeny of degree N and if so it returns also all the non isomorphic isogenous varieties and the isomorphism}
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

intrinsic Isogenies(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl, N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
  {returns if the abelian variety has an isogeny of degree N and if so it returns also all the non isomorphic isogenous varieties and the isomorphism}
  require MultiplicatorRing(I) eq MultiplicatorRing(J):  "the MultiplicatorRing's are not the same";
  potential_isogenies_of_degree_N := IsogeniesMany([I], J, N);
  return #potential_isogenies_of_degree_N[1] ge 1, potential_isogenies_of_degree_N[1];
end intrinsic;

intrinsic IsPolarized(I0::AlgAssVOrdIdl, phi::SeqEnum[Map], N::RngIntElt)->BoolElt, SeqEnum[AlgAssElt]
  {returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations}
  //31 Jan 2018.
  require IsFiniteEtale(Algebra(I0)): "the algebra of definition must be finite and etale over Q";
  S := MultiplicatorRing(I0);
  I := ideal<S|ZBasis(I0)>;
  A := Algebra(S);
  RR := RealField();
  Itbar := ComplexConjugate(TraceDualIdeal(I));
  assert ideal<S meet ComplexConjugate(S) | ZBasis(Itbar)> eq ideal<S meet ComplexConjugate(S) | ZBasis(TraceDualIdeal(ComplexConjugate(I)))>;

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
    for uu in UqBinS do
      pol := (x*(A ! uu));
      assert (pol*I) eq J;
      assert (pol*I) subset Itbar;
      //pol is a polarization if totally imaginary and \Phi-positive
      C := [g(pol): g in phi];
      if (ComplexConjugate(pol) eq (-pol)) and (forall{c : c in C | Im(c) gt (RR ! 0)}) then
        assert (pol*I) subset Itbar;
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

intrinsic IsWeil(f::RngUPolElt) -> BoolElt,RngIntElt
{Returns whether f is a q-WeilPolynomial and q, where q is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2)}

  require BaseRing(Parent(f)) eq Integers() and IsEven(Degree(f)): "the input must be an integral polynomial of even degree";
  roots:=Roots(f,ComplexField());
  q:=roots[1,1]*ComplexConjugate(roots[1,1]);
  if not IsReal(q) then
      return false,_;
  else
      qq:=Round(RealField() ! q);
      if Abs(qq-q) lt 10^-5 and forall{r : r in roots | Abs(r[1]*ComplexConjugate(r[1]) - q) lt 10^-5  } then //the precision should be enough.
          return true,qq;
      else return false,_;
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

intrinsic IsCharacteristicPoly(f::RngUPolElt) -> BoolElt,RngIntElt
{Given an irreducible q-Weil polynomial f, returns the exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].}
  testWeil,q:=IsWeil(f);
require IsIrreducible(f) and testWeil: "the input must be an irreducible q-Weil polynomial";
  fac:=Factorization(q);
  p:=fac[1,1]; d:=fac[1,2]; //q=p^d, with p a prime
  Qp:=pAdicField(p);
  Rp<y>:=PolynomialRing(Qp);
  g:= Rp ! f;
  gfact:=[h[1] : h in Factorization(g)];
  if #RealRoots(f,RealField(),10) gt 0 then
    e:=LCM(  [Denominator((Valuation(Coefficients(h)[1])/d)) : h in gfact] cat [2]  ); //the extra 1/2 comes from the real prime, see the reference.
  else
    e:=LCM(  [Denominator((Valuation(Coefficients(h)[1])/d)) : h in gfact]  );
  end if;
  if e eq 1 then return true,e; else return false,e; end if;
end intrinsic;

intrinsic AutomorphismsPol(I::AlgAssVOrdIdl) -> GpAb
{returns the automorphisms of a polarized abelian variety}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    return TorsionSubgroup(UnitGroup2(MultiplicatorRing(I)));
end intrinsic;

cm_type_internal:=function(A)
	P<x>:=PolynomialRing(Integers());
	fA:=P!DefiningPolynomial(A);
	q:=Integers() ! ( Coefficients(fA)[1]^(2/Degree(fA)) );
	p:=Factorization(q)[1,1];
	M:=NumberField(P!DefiningPolynomial(SplittingField(fA)));
	frob_in_M:=[[-Coefficients(h[1])[1] : h in Factorization(PolynomialRing(M)!DefiningPolynomial(L[1])) ] : L in A`NumberFields ];
	//here we use Montes algorithm. One need to Attach +IdealsNF.m !!!!
	Factorization(ideal(M,p));
	PM:=M`PrimeIdeals[p,1]; // we choose a prime of M above p
	Cvalues_p_pos:=[ [Conjugates(c)[1] : c in fr | PValuation(c,PM) gt 0]  : fr in frob_in_M ]; // note that the function PValuation is also from the +IdealsNF.m package
	homsA:=HomsToC(A);
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
	  if forall{ i : i in [1..#cm_values] | forall{ d : d in cm_values[i] | exists{ c : c in Cvalues_p_pos[i] | Abs(d-c) lt 10^-8  } } } then
	      Append(~cm_p_pos,cm);
	  end if;
	end for;

      A`CMType:=cm_p_pos;
      return cm_p_pos;
end function;

intrinsic CMType(A::AlgAss : TestOrdinary:=true)->SeqEnum[Maps]
{given a product of CM number fields A=Q[x]/(f), where f is q-Weil polynomial, returns a subset of HomsToC consisting of one map A->C per conjugate pair such that the induced p-adic valuation v on \bar(Q_p) in C is such that v(a)>0, where a is a root of f. If f is ordinary then it should return only one output. Otherwise more.}
  f:=DefiningPolynomial(A);
  q:=Integers() ! ( Coefficients(f)[1]^(2/Degree(f)) );
  require &and[ Abs(Abs(x[1])-Sqrt(q)) lt 10^(-10)  : x in Roots(f,ComplexField())]: "the defining polynomial must be a q-Weil polynomial";
  if TestOrdinary then
    require IsOrdinary(f): "The isogeny class is not ordinary";
  end if;
  if assigned A`CMType then return A`CMType;
  else
      require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
      require HasComplexConjugate(A): "it must be a product of CM number fields";
      return cm_type_internal(A);
  end if;
end intrinsic;
