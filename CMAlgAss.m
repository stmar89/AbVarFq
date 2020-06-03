/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Complex Multiplication for AlgAss
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

declare verbose CMAlgAss, 1;

declare attributes AlgAss : HasComplexConjugate;

intrinsic HasComplexConjugate(A::AlgAss) -> BoolElt
{returns if the algebra is the product of CM fields}
    if not assigned A`HasComplexConjugate then
        A`HasComplexConjugate:=forall{L : L in A`NumberFields | HasComplexConjugate(L[1])};
    end if;
	return A`HasComplexConjugate;
end intrinsic;

intrinsic ComplexConjugate(x::AlgAssElt) -> AlgAssElt
{if A is a product of CM fields, it returns the complex conjugate of the argument}
	A:=Parent(x);
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
	require HasComplexConjugate(A) : "it is not a product of CM fields";
	return Order([ ComplexConjugate(x) : x in ZBasis(O) ]);
end intrinsic;

intrinsic ComplexConjugate(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{if A is a product of CM fields, it returns the complex conjugate of the argument}
	O:=Order(I);
	A:=Algebra(O);
	require HasComplexConjugate(A) : "it is not a product of CM fields";
	Ob:=ComplexConjugate(O);
	return ideal<Ob|[ ComplexConjugate(x) : x in ZBasis(I) ]>;
end intrinsic;

/////////////////////////////////////////////////////
// CMType for AlgAss
/////////////////////////////////////////////////////

declare type AlgAssCMType;
declare attributes AlgAssCMType : Homs, // homs from Q(Frob) of the isogeny class to CC
                                  CMPosElt; // a totally imaginary element b in Q(Frob), which is positive for the cm-type. such b is not unique: b and b' define the same cm-type iff b/b' is totally positive


/////////////////////////////////////////////////////
// Creation, print, access and equality testing for CMType for IsogenyClassFq
/////////////////////////////////////////////////////

intrinsic CreateCMType(seq::SeqEnum[Map]) -> AlgAssCMType
{ given a sequence seq of homomorphisms from a CM-algebra to CC, one per conjugate pair, it returns the corresponding CMType }
    A:=Domain(seq[1]);
    assert &and[Domain(s) eq A : s in seq[2..#seq]];
    g:=Dimension(A) div 2;
    assert #seq eq g;
    F:=PrimitiveElement(A);
    CC_vals:=[ h(F) : h in seq ];
    assert forall{ c : c in CC_vals | not exists{ d : d in CC_vals | Abs( ComplexConjugate(c)-d) lt 10^(2-Precision(d)) }  };
    PHI:=New(AlgAssCMType);
    PHI`Homs:=seq;
    return PHI;
end intrinsic;

intrinsic CreateCMType( b::AlgAssElt  ) -> AlgAssCMType
{ given a totally imginary element b, it returns the CMType PHI for which b is PHI-positive }
    assert not IsZeroDivisor2(b) and (b eq -ComplexConjugate(b));
    PHI:=New(AlgAssCMType);
    PHI`CMPosElt:=b;
    return PHI;
end intrinsic;

intrinsic Print( PHI :: AlgAssCMType)
{ print the AlgAssCMType }
    printf "CMType of the Associative Algebra %o determined by the element %o",Domain(Homs(PHI)[1]),CMPosElt(PHI);
end intrinsic;

intrinsic CMPosElt( PHI::AlgAssCMType )->AlgAssElt
{ given a CMType PHI returns a totally imaginary PHI-positive element (which uniquely determines PHI) }
    if not assigned PHI`CMPosElt then
        A:=Domain(Homs(PHI)[1]);
        F:=PrimitiveElement(A);
        V:=ComplexConjugate(F);
        e:=F-V;
        if forall{ff: ff in Homs(PHI) | Im(ff(e)) gt 0 } then cmposelt:=e; 
        elif forall{ff: ff in Homs(PHI) | Im(ff(-e)) gt 0} then cmposelt:=-e;
        else 
          R:=EquationOrder(A);  
          bb:=5;
          cnter:=0;
          go:=false;
          repeat
            e1:=Random(OneIdeal(R) : bound:=bb);
            e:=e1-ComplexConjugate(e1);
            if not IsZeroDivisor2(e) and forall{ff: ff in Homs(PHI) | Im(ff(e)) gt 0} then
                go:=true;
            else
                cnter +:=1;
            end if;
            if cnter eq 100 then
                bb:= 2*bb;
                cnter:=1;
            end if;
          until go;
          cmposelt:=e;
        end if;    
        PHI`CMPosElt:=cmposelt;
    end if;
    return PHI`CMPosElt;
end intrinsic;

intrinsic Homs( PHI::AlgAssCMType : Precision:=30 )->SeqEnum[Map]
{ given a AlgAssCMType PHI returns the sequence of maps to CC defining it  }
    if not assigned PHI`Homs then
        b:=CMPosElt(PHI);
        A:=Parent(b); 
        homs:=HomsToC(A : Precision:=Precision);
        phi:=[ ff : ff in homs | Im(ff( b )) gt 0 ];
        assert #phi eq #homs div 2;
        PHI`Homs:=phi;    
    end if;
    return PHI`Homs;
end intrinsic;

intrinsic 'eq'(PHI1 :: AlgAssCMType, PHI2::AlgAssCMType : Precision:=30)->BoolElt
{ returns whether two cm types are equal }
    A:=Domain(Homs(PHI1)[1]);
    assert forall{ phi : phi in Homs(PHI1) cat Homs(PHI2) | Domain(phi) eq A };
    homs:=HomsToC(A : Precision:=Precision);
    b1:=CMPosElt(PHI1);
    b2:=CMPosElt(PHI2);
    if b1 eq b2 then
        return true;
    else
        b:=b1/b2;
        return forall{ h : h in homs | Re(h(b)) gt 0 };
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// pAdicPosCMType for ordinary IsogenyClassFq
/////////////////////////////////////////////////////

declare attributes IsogenyClassFq : pAdicPosCMType; //this will be of type 'AlgAssCMType'
declare attributes AlgAssCMType : pAdicData; // it stores a tuple < p,rrtspp,rtsCC > where p is a prime and rtspp and rtsCC are p-adic and complex roots of the defining polynomial sorted according to a Galois-equivariant bijection. This boils down to determine the restriction of an embedding \bar Qp into CC.

intrinsic pAdicPosCMType(AVh::IsogenyClassFq : precpAdic := 30, precCC := 30 ) -> AlgAssCMType
{ given an ordinary isogeny class AVh, it computes a AlgAssCMType of the Algebra determined by the Frobenius of AVh such that the Frobenius has positive p-adic valuation according to some embedding of \barQp in C.
  The varargs precpAdic and precCC specify (minimum) output padic and complex precision.}
    if not assigned AVh`pAdicPosCMType then
        require IsSquarefree(AVh) and IsOrdinary(WeilPolynomial(AVh)) : "implemented only for squarefree and ordinary isogeny classes";
        h:=WeilPolynomial(AVh);
        p:=CharacteristicFiniteField(AVh);
        rtspp,rtsCC:=pAdicToComplexRoots(PolynomialRing(Rationals())!h,p : precpAdic := precpAdic, precCC:=precCC ); //from paddictocc.m. works only for ordinary
        // rtspp and rtsCC are the padic and CC roots of h, sorted G-eqivariantly.
        A:=Algebra(ZFVOrder(AVh));
        homs:=HomsToC(UniverseAlgebra(AVh) : Precision:=precCC );
        FA:=PrimitiveElement(A);
        homs_FA:=[Parent(rtsCC[1])!h(FA) : h in homs ];
        cmtype_homs:=[ ];
        for ir in [1..#homs_FA] do
            r:=homs_FA[ir];
            assert exists(ind){ irCC : irCC in [1..#rtsCC] | Abs(r-rtsCC[irCC]) lt 10^(2-precCC) };
            if Valuation(rtspp[ind]) gt 0 then
                Append(~cmtype_homs,homs[ir]);
            end if;
        end for;
        assert #cmtype_homs eq (Degree(h) div 2);
        // creation AlgAssCMType
        PHI:=CreateCMType(cmtype_homs);
        if not assigned PHI`pAdicData then
            PHI`pAdicData:=[< p, rtspp, rtsCC >];
        else
            assert not exists{ data : data in PHI`pAdicData | data[1] eq p }; //to avoid computing different p-adic data for the same p.
            Append(PHI`pAdicData,< p, rtspp, rtsCC >);
        end if;
        AVh`pAdicPosCMType:=PHI;
    end if;
    return AVh`pAdicPosCMType;
end intrinsic;

/////////////////////////////////////////////////////
// AllCMType 
/////////////////////////////////////////////////////

intrinsic AllCMTypes(AVh::IsogenyClassFq : precCC := 30 ) -> SeqEnum[AlgAssCMType]
{ returns all the AlgAssCMTypes of Q(Frob) }
    A:=Algebra(ZFVOrder(AVh));
    cc:=CartesianProduct(Partition([ h: h in HomsToC(A : Precision:=precCC )],2));
    cc:=[ [ci : ci in c] : c in cc ]; //from tuple to seq
    return [ CreateCMType(c) : c in cc ];
end intrinsic;

/////////////////////////////////////////////////////
// OLD CODE: kept for retro-compatibility.
// old way to compute the CM-type for both ordinary and non-ordinary abelian varieties
// this is quite slow beause it requires to compute a splitting field
/////////////////////////////////////////////////////

declare attributes AlgAss : CMType;

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

intrinsic CMType(A::AlgAss : Precision:=30 , TestOrdinary:=true)->SeqEnum[Map]
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



/*
//TESTS
//

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    _<x>:=PolynomialRing(Integers());
    polys:=[
    x^4+x^2+529,
    x^4+11*x^3+73*x^2+319*x+841,
    x^4-4*x^3+8*x^2-116*x+841,
    x^4+4*x^3+8*x^2+116*x+841,
    x^4-17*x^2+841,
    x^4-x^3+26*x^2-31*x+961,
    x^4-6*x^3+43*x^2-186*x+961,
    x^4-4*x^3+8*x^2-124*x+961,
    x^4+2*x^3+52*x^2+62*x+961,
    x^4+x^3+26*x^2+31*x+961
    ];

    for f in polys do
        AVf:=IsogenyClass(f);
        all:=AllCMTypes(AVf);
        for PHI in all do
            _:=CMPosElt(PHI);
            _:=Homs(PHI);
        end for;
        for PHI,PSI in all do
            _:=PHI eq PSI;
        end for;
        pPHI:=pAdicPosCMType(AVf);
        assert pPHI in all;
    end for;




*/
