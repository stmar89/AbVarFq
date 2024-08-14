/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Complex Multiplication for AlgAss
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
/////////////////////////////////////////////////////

declare verbose CMAlgAss, 1;

/////////////////////////////////////////////////////
// AllCMTypes 
/////////////////////////////////////////////////////

declare attributes IsogenyClassFq : AllCMTypes;

intrinsic AllCMTypes(AVh::IsogenyClassFq : precCC := 30 ) -> SeqEnum[AlgAssCMType]
{ returns all the AlgAssCMTypes of Q(Frob) }
    if not assigned AVh`AllCMTypes then
        A:=Algebra(ZFVOrder(AVh));
        cc:=CartesianProduct(Partition([ h: h in HomsToC(A : Precision:=precCC )],2));
        cc:=[ [ci : ci in c] : c in cc ]; //from tuple to seq
        AVh`AllCMTypes:=[ CreateCMType(c) : c in cc ];
    end if;
    return AVh`AllCMTypes;
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
        // if AllCMTypes has already been computed take PHI from there.
        if assigned AVh`AllCMTypes then
            PHI_old:=[ cm : cm in AllCMTypes(AVh) | PHI eq cm ]; 
            assert #PHI_old eq 1; //sanity check
            PHI:=PHI_old[1];
        end if;
        if not assigned PHI`pAdicData then
            PHI`pAdicData:=[< p, rtspp, rtsCC >];
        else
            assert not exists{ data : data in PHI`pAdicData | data[1] eq p }; //to avoid computing different p-adic data for the same p.
            Append(~PHI`pAdicData,< p, rtspp, rtsCC >);
        end if;
        AVh`pAdicPosCMType:=PHI;
    end if;
    return AVh`pAdicPosCMType;
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
        time all:=AllCMTypes(AVf);
        time _:=AllCMTypes(AVf); // should be instant.
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

    _<x>:=PolynomialRing(Integers());
    f:=x^4+x^2+529;
    AVf:=IsogenyClass(f);
    PHI:=pAdicPosCMType(AVf);
    PHI2:=ChangePrecision(PHI,100);
    ChangePrecision(~PHI,200);

    _<x>:=PolynomialRing(Integers());
    f:=x^4+x^2+529;
    AVf:=IsogenyClass(f);
    _:=AllCMTypes(AVf);
    PHI:=pAdicPosCMType(AVf);
    assert PHI in AllCMTypes(AVf);
    PHI2:=ChangePrecision(PHI,100);
    ChangePrecision(~PHI,200);

    //testing the removal of IdealsNF.m
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    P<x>:=PolynomialRing(Integers());
    polys:=[ eval(c) : c in Split(Read("~/219_CCO/input/prime_field_sqfree_low_pRank.txt")) ];
    for c in polys do
        f:=P!c;
        A:=AssociativeAlgebra(f);
        t0:=Cputime();
        _:=CMType(A : TestOrdinary:=false);
        t1:=Cputime(t0);
        if t1 gt 20 and t1 lt 60 then f; break; end if;
    end for;

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    P<x>:=PolynomialRing(Integers());
    f:=x^6 - 2*x^5 + 2*x^4 - 2*x^3 + 4*x^2 - 8*x + 8;
    A:=AssociativeAlgebra(f);
    time _:=CMType(A : TestOrdinary:=false);


*/
