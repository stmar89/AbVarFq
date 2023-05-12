/* vim: set syntax=magma :*/

declare attributes AlgEtQOrd : PrincipalPolarizationsIsogenyClass,
                               transversal_US_USplus,
                               transversal_USplus_USUSb;

transversal_US_USplus:=function(S)
    if not assigned S`transversal_US_USplus then
        US,uS:=UnitGroup(S);
        USplus:=TotallyRealPositiveUnitGroup(S);
        S`transversal_US_USplus:=[ uS(t) : t in Transversal(US,USplus)];
    end if;
    return S`transversal_US_USplus;
end function;

transversal_USplus_USUSb:=function(S)
    if not assigned S`transversal_USplus_USUSb then
        US,uS:=UnitGroup(S);
        USplus:=TotallyRealPositiveUnitGroup(S);
        USUSb:=sub< USplus | [ USplus!((g*ComplexConjugate(g))@@uS) : g in [uS(g) : g in Generators(US) ]]>;
        S`transversal_USplus_USUSb:=[ uS(t) : t in Transversal(USplus,USUSb)];
    end if;
    return S`transversal_USplus_USUSb;
end function;

intrinsic PrincipalPolarizations(I::AlgEtQIdl,PHI::AlgEtQCMType)->SeqEnum[AlgEtQElt]
{Given an ideal I and a CM-Type PHI, returns all the principal polarizations with respect to PHI.}

    is_polarization:=function(l,PHI)
    // l an element of K, PHI a CMType
        test1:=l eq -ComplexConjugate(l);
        test2:=forall{phi : phi in Homs(PHI) | Im(phi(l)) gt 0 };
        return test1 and test2;
    end function;

    //TODO Document me 
    Iv:=TraceDualIdeal(ComplexConjugate(I));
    test,iso:=IsIsomorphic(I,Iv);
    if not test then
        Ipols:=[];
    else
        S:=MultiplicatorRing(I);
        got_one:=false;
        for u in transversal_US_USplus(S) do
            x:=u*iso;
            if is_polarization(x,PHI) then
                got_one:=true;
                break;
            end if;
        end for;
        if got_one then
            Ipols:=[ x*t : t in transversal_USplus_USUSb(S) ];
        else
            Ipols:=[PowerStructure(AlgEtQElt)|]; //empty sseq
        end if;
    end if;
    return Ipols;
end intrinsic;

intrinsic pAdicPosCMType(A::AlgEtQ : precpAdic := 30, precCC := 30 ) -> AlgEtQCMType
{}
// Thanks John Voight!
// given an ordinary isogeny class AVh, it computes a AlgAssCMType of the 
// Algebra determined by the Frobenius of AVh such that the Frobenius has 
// positive p-adic valuation according to some embedding of \barQp in C.
    h:=ChangeRing(DefiningPolynomial(A),Integers());
    _,p:=IsPrimePower(ConstantCoefficient(h));
    require IsCoprime(Coefficients(h)[(Degree(h) div 2)+1],p) : "The isogeny class is not ordinary";
    rtspp,rtsCC:=pAdicToComplexRoots(PolynomialRing(Rationals())!h,p : precpAdic := precpAdic, precCC:=precCC ); 
        //from paddictocc.m. works only for ordinary
    homs:=HomsToC(A : Precision:=precCC );
    FA:=PrimitiveElement(A);
    homs_FA:=[Parent(rtsCC[1])!h(FA) : h in homs ];
    cmtype_homs:=[ ];
    for ir in [1..#homs_FA] do
        r:=homs_FA[ir];
        assert exists(ind){ irCC : irCC in [1..#rtsCC] | Abs(r-rtsCC[irCC]) lt 10^(-(precCC div 2)) };
        if Valuation(rtspp[ind]) gt 0 then
            Append(~cmtype_homs,homs[ir]);
        end if;
    end for;
    assert #cmtype_homs eq (Degree(h) div 2);
    PHI:=CMType(cmtype_homs);
    return PHI;
end intrinsic;

intrinsic PrincipalPolarizationsIsogenyClass(R::AlgEtQOrd)->SeqEnum
{ returns a sequence of tuples < I, [x1,...,xn] > where (I,x1),...,(I,xn) represent the isomorphism classes of PPAVs corresponding with underlying AV given by I. Ideally, R=Z[F,V]. Important: isomorphism classes without a principal polarization are not returned (seomtimes not even computed).}
    if not assigned R`PrincipalPolarizationsIsogenyClass then
        A:=Algebra(R);
        PHI:=pAdicPosCMType(A);
        oo:=OverOrders(R);
        output:=[];
        for iS in [1..#oo] do
            S:=oo[iS];
            test_S:=IsConjugateStable(S) and not exists{ P : P in NonGorensteinPrimes(S) | IsConjugateStable(P) and CohenMacaulayTypeAtPrime(S,P) eq 2 };
            // if test eq false then there is no PPAV with End = S.
            if test_S then
                // if S is Gorenstein the next part can be improved! See the notes TODO
                icmS:=ICM_bar(S);
                for I in icmS do
                    pp:=PrincipalPolarizations(I,PHI);
                    if #pp gt 0 then
                        Append(~output,< I , pp >);
                    end if;
                end for;
            end if;
        end for;
        R`PrincipalPolarizationsIsogenyClass:=output;
    end if;
    return R`PrincipalPolarizationsIsogenyClass;
end intrinsic;

RemoveBlanks:=function(str)
// given a string str removes the blank spaces
    return &cat(Split(str," "));
end function;

intrinsic PrintPrincipalPolarizationsIsogenyClass(R::AlgEtQOrd)->MonStgElt
{}
    A:=Algebra(R);
    nf:=Components(A);
    nf_poly:=[ Coefficients((DefiningPolynomial(K))) : K in nf ];

    str:="<\n";
    str cat:=RemoveBlanks(Sprint(nf_poly)) cat ",\n";
    _,zbR:=PrintSeqAlgEtQElt(ZBasis(R));
    str cat:=zbR cat ",\n";
    str cat:="<\n";
    ppav:=PrincipalPolarizationsIsogenyClass(R);
    for i->pair in ppav do
        I:=pair[1];
        ppols:=pair[2];
        _,strI:=PrintSeqAlgEtQElt(ZBasis(I));
        _,str_ppols:=PrintSeqAlgEtQElt(ppols);
        str cat:="<\n" cat strI cat "," cat str_ppols cat "\n>";
        if i ne #ppav then
            str cat:=",\n";
        else
            str cat:="\n";
        end if;
    end for;
    str cat:= ">\n>";
    return str;
end intrinsic;

intrinsic LoadPrincipalPolarizationsIsogenyClass(str::MonStgElt)->AlgEtQOrd
{}
    data:=eval(str);
    PP:=PolynomialRing(Rationals());
    ff:=[ PP!f : f in data[1]];
    A:=EtaleAlgebra([NumberField(f) : f in ff ]);
    zbR:=[A!s : s in data[2]];
    R:=Order(zbR);
    pairs:=data[3];
    ppav:=[];
    for pair in pairs do
        I:=Ideal(R,[A!s : s in pair[1]]);
        I_pols:=[A!s : s in pair[2]];
        Append(~ppav,<I,I_pols>);
    end for;
    R`PrincipalPolarizationsIsogenyClass:=ppav;
    return R;
end intrinsic;

intrinsic PeriodMatrix(I::AlgEtQIdl,x0::AlgEtQElt,phi::AlgEtQCMType) -> AlgMatElt,AlgMatElt
{ Given an abelian variety I over a finite field and a principal polarization x0 computed wrt the CM-type phi, it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
	A:=Algebra(I);
	cc:=ComplexConjugate;
	zb:=ZBasis(I);
	N:=#zb;
    phi:=Homs(phi);
	prec:=Precision(Codomain(phi[1]));
	//E := Matrix(Integers(),N,N,[Trace(x0*cc(a)*b) : b in zb, a in zb]); // added sign
	E := Matrix(Integers(),N,N,[-Trace(x0*cc(a)*b) : b in zb, a in zb]); // added sign
	D, C := FrobeniusFormAlternating(E);
	// newb := ElementToSequence(Matrix(A,C)*Matrix(A,N,1,zb));
    newb:= [ SumOfProducts(Eltseq(r),zb) : r in Rows(C) ];
	N:=N div 2;
	bigPM := Matrix(Codomain(phi[1]),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
	smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
	test_symm:=forall{<i,j> : i,j in [1..N] | Abs(smallPM[i,j]-smallPM[j,i]) lt 10^(-(prec div 2)) };
	im_smallPM:=Matrix([[Im(x) : x in Eltseq(r)] :r in Rows(smallPM)]);
	test_pos_def:=forall{e : e in Eigenvalues(im_smallPM) | e[1] gt 0 };
	require test_symm and test_pos_def : "Precision issue. Increase the precision of the given cm-type";
	return bigPM,smallPM;     
end intrinsic;

    /*
    fld:="~/266_wk_icm_rec/";
    fld_schema_wk:=fld cat "labelling/parallel/output/";
    AttachSpec(fld cat "AlgEt/spec");
    load "~/999_LMFDB_isogeny_label_functions.txt";
    P<x>:=PolynomialRing(Integers());
    Attach(fld cat "polarizations/padictocc.m");
    Attach(fld cat "labelling/parallel/labelling.m");
    Attach(fld cat "polarizations/polarizations.m");

    t0:=Cputime();
        file:=fld_schema_wk cat "2.128.a_bf_schema.txt";
        //file:=fld_schema_wk cat "3.9.d_j_o_schema.txt";
        time R:=LoadSchemaWKClasses(Read(file));
        time str:=PrintPrincipalPolarizationsIsogenyClass(R);
        time S:=LoadPrincipalPolarizationsIsogenyClass(str);
        time ppavs:=PrincipalPolarizations(S);
        "We have", &+[ #p[2] : p in ppavs ], "ppavs";
        PHI:=CMType(ppavs[1,2]);
        for p in ppavs do
            pp:=p[2];
            PeriodMatrix(p[1],pp,PHI);
        end for;
    t1:=Cputime(t0);
    "Tot time",t1;
    */
