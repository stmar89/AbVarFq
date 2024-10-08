/* vim: set syntax=magma :*/

    SetDebugOnError(true);

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    //////////////////////////////////
    // Isomorphism Classes (with Deligne Modules)
    //////////////////////////////////

    _<x>:=PolynomialRing(Integers());
    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    time IsogenyClass(f);
    time ZFVOrder(IsogenyClass(f));
    time pRank(IsogenyClass(f));
    time pRank(IsogenyClass(f : Check:=false ));
    IsOrdinary(f);
    
    AVf:=IsogenyClass(f);
    IsOrdinary(AVf);
    _:=IsomorphismClasses(AVf);
    time #IsomorphismClasses(AVf);
    for A,B in IsomorphismClasses(AVf) do t,s:=IsIsomorphic(A,B); end for;

    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    time AVf:=IsogenyClass(f^3 );
    time AVf:=IsogenyClass(f^3 : Check:=false );
    _:=FrobeniusEndomorphismOnDeligneAlgebra(AVf);
    iso:=IsomorphismClasses(AVf);
    time #IsomorphismClasses(AVf); //it should be 0
    for A in iso do
        _:=FrobeniusEndomorphism(A);
    end for;
    for A,B in iso do 
        t,s:=IsIsomorphic(A,B);
    end for;

    f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
    h:=x^2-x+2;
    AVf:=IsogenyClass(h*f^2);
    //iso:=IsomorphismClasses(AVf); //this is very slow
    ZFV:=ZFVOrder(AVf);

    //////////////////////////////////
    // CMTypes
    //////////////////////////////////

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

    //////////////////////////////////
    // Polarizations
    //////////////////////////////////

    //Example 7.2
    
    _<x>:=PolynomialRing(Integers());
    h:=x^4+2*x^3-7*x^2+22*x+121;
    AVh:=IsogenyClass(h);
    iso:=IsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for iA in [1..#iso] do
        A:=iso[iA];
        N:=0;
        repeat
            printf ".";
            N+:=1;
            test,pols_deg_N:=HasPolarizationsOfDegree(A,PHI,N);
        until test;
        for pol in pols_deg_N do
            aut:=#PolarizedAutomorphismGroup(pol);
        end for;
        iA,#pols_deg_N,N,aut;
    end for;

    //Example 7.3
    
    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    iso:=IsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        test,princ_pols:=IsPrincipallyPolarized(A,PHI);
        for pol in princ_pols do
            assert IsPolarization(pol,PHI);
            PolarizedAutomorphismGroup(pol);
        end for;
    end for;

    //////////////////////////////////
    // Period matrices
    //////////////////////////////////

    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    iso:=IsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        test,princ_pols:=IsPrincipallyPolarized(A,PHI);
        for pol in princ_pols do
            assert IsPolarization(pol,PHI);
            go:=false;
            repeat
                try 
                    PeriodMatrix(pol,PHI);
                    go:=true;
                catch e
                    prec0:=Precision(PHI);
                    ChangePrecision(~PHI,2*prec0);
                    go:=false;
                end try;
            until go;
        end for;
    end for;

    //////////////////////////////////
    // Rational Points
    //////////////////////////////////

    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    S1:=ZFVOrder(AVh);
    O:=MaximalOrder(Algebra(S1));
    iso:=IsomorphismClasses(AVh);
    over_orders:=FindOverOrders(S1);
    for S in over_orders do
        iso_S:=[ A : A in iso | EndomorphismRing(A) eq S];
        for r in [1..8] do
            r,{ ElementaryDivisors(RationalPoints(A,r)) : A in iso_S};
        end for;
    end for;

    _<x>:=PolynomialRing(Integers());
    h:=x^8-5*x^7+13*x^6-25*x^5+44*x^4-75*x^3+117*x^2-135*x+81;
    AVh:=IsogenyClass(h);
    S1:=ZFVOrder(AVh);
    O:=MaximalOrder(Algebra(S1));
    iso:=IsomorphismClasses(AVh);
    over_orders:=FindOverOrders(S1);
    for S in over_orders do if not IsGorenstein(S) then
        iso_S:=[ A : A in iso | EndomorphismRing(A) eq S];
        #iso_S;
        { ElementaryDivisors(RationalPoints(A)) : A in iso_S};
    end if; end for;
    
    //////////////////////////////////
    // Base Field Ext
    //////////////////////////////////
    
    SetDebugOnError(true);

    P<x>:=PolynomialRing(Integers());

    // Example 1
    h:=x^6 - x^3 + 8;
    AVh:=IsogenyClass(h);
    r:=6;
    I6,m6:=BaseFieldExtension(AVh,r);

    iso:=IsomorphismClasses(AVh);
    #iso;
    iso_6:=IsomorphismClasses(I6);
    #iso_6;


    for A in iso do 
        Ae:=BaseFieldExtension(A,I6,m6);
        R:=ZFVOrder(Ae);
        exists{ B : B in iso_6 | IsIsomorphic(Ae,B) }; 
    end for;

    for A in iso do
        for B in iso do
            IsTwistOfOrder(A,B,r);
        end for;
    end for;

    // Example 2
    h:=x^6 + 4*x^3 + 27;
    AVh:=IsogenyClass(h);
    r:=3;
    I3,m3:=BaseFieldExtension(AVh,r);

    iso:=IsomorphismClasses(AVh);
    #iso;
    for A in iso do 
        Ae:=BaseFieldExtension(A,I3,m3);
    end for;

    // Example 3
    _<x>:=PolynomialRing(Integers());
    h1:=x^4 - 205*x^2 + 10609;
    h2:=(x^2-x+103)*(x^2+x+103);
    g3:=(x^2-x+103); h3:=g3^2;
    g4:=(x^2+x+103); h4:=g4^2;
    Ah1:=IsogenyClass(h1);
    isoh1:=IsomorphismClasses(Ah1);
    Ah2:=IsogenyClass(h2);
    isoh2:=IsomorphismClasses(Ah2);
    Ah3:=IsogenyClass(h3);
    isoh3:=IsomorphismClasses(Ah3);
    Ah4:=IsogenyClass(h4);
    isoh4:=IsomorphismClasses(Ah4);

    "isom classes: ", #isoh1, #isoh2, #isoh3, #isoh4;

    assert 1 eq #{ WeilPolynomial(BaseFieldExtension(Ahi,4)) : Ahi in [Ah1,Ah2,Ah3,Ah4] };

    for I in [Ah1,Ah2,Ah3,Ah4] do
        WeilPolynomial(BaseFieldExtension(I,2));
    end for;
    // the last 3 isogeny classes extend to the same isogeny class over F_103^2

    Ah_2,_:=BaseFieldExtension(Ah2,2);
    seq_2:=BaseFieldExtension(isoh2 cat isoh3 cat isoh4 , Ah_2);
    Ah_4,_:=BaseFieldExtension(Ah2,4);
    seq_4:=BaseFieldExtension(isoh2 cat isoh3 cat isoh4 , Ah_4);
    seq_2_4:=BaseFieldExtension([s[1] : s in seq_2],Ah_4);
    assert #seq_4 eq #seq_2_4;
    assert forall{ i : i in [1..#seq_4] | seq_4[i,1] eq seq_2_4[i,1] };
    // we test that the base extension of the base extension is equal to a single base extension

    all_iso:=isoh1 cat isoh2 cat isoh4 cat isoh4 ;
    for A in all_iso do
        for B in all_iso do
            if IsTwistOfOrder(A,B,2) then
                printf "1 ";
            else
                printf "0 ";
            end if;
        end for;
        printf "\n";
    end for;

    all_ext:=BaseFieldExtension(all_iso,Ah_4);
    for A in all_ext do
        for B in all_ext do
            if IsIsomorphic(A[1],B[1]) then
                printf "1 ";
            else
                printf "0 ";
            end if;
        end for;
        printf "\n";
    end for;



    // Example 4 - continutation of the previous

    _<x>:=PolynomialRing(Integers());
    h1:=x^4 - 205*x^2 + 10609;
    h2:=(x^2-x+103)*(x^2+x+103);
    g3:=(x^2-x+103); h3:=g3^2;
    g4:=(x^2+x+103); h4:=g4^2;
    Ah1:=IsogenyClass(h1);
    isoh1:=IsomorphismClasses(Ah1);
    Ah2:=IsogenyClass(h2);
    isoh2:=IsomorphismClasses(Ah2);
    Ah3:=IsogenyClass(h3);
    isoh3:=IsomorphismClasses(Ah3);
    Ah4:=IsogenyClass(h4);
    isoh4:=IsomorphismClasses(Ah4);
    A:=isoh1[1];
    UA:=DeligneAlgebra(A);
    F:=MapOnDeligneAlgebras(FrobeniusEndomorphism(A));
    U,u:=UnitGroup(MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]));
    TAut:=[ hom<UA->UA|[u(t)*b:b in Basis(UA)]> : t in TorsionSubgroup(U) ];
    TF:=[ t*F : t in TAut ];
    assert forall{ t : t in TAut | F*t eq t*F };
    all_iso:=isoh1 cat isoh2 cat isoh4 cat isoh4 ;
    Ah_4,_:=BaseFieldExtension(Ah1,4);
    all_ext:=BaseFieldExtension(all_iso,Ah_4);
    Ae:=all_ext[1,1];
    mAe:=all_ext[1,2];
    TF_mAe:=[ tf*mAe : tf in TF];


    for B in all_ext do
        test,iso:=IsIsomorphic(Ae,B[1]);
        if test then
            iso:=MapOnDeligneAlgebras(iso);
            FB:=MapOnDeligneAlgebras(FrobeniusEndomorphism(B[1]));
            mB:=iso*FB*Inverse(iso);
            exists{ a : a in TF_mAe | a eq mB };
        end if;
    end for;



    // Example 4.2 - continutation of the previous. second version of the test

    P<x>:=PolynomialRing(Integers());
    h:=x^4 - 205*x^2 + 10609;
    Ah:=IsogenyClass(h);
    Ah_4,_:=BaseFieldExtension(Ah,4);
    h_4:=WeilPolynomial(Ah_4);
    hs:=[];
    rr:=Roots(h_4,ComplexField());
    ccsq:=[ Roots(x^4-r[1]) : i in [1..r[2]] ,  r in rr];
    ccsq:=CartesianProduct(ccsq);
    for c in ccsq do 
        coCC:=Coefficients(&*[ x-cc[1] : cc in c ]); 
        coZZ:=[ Round(Re(c)) : c in coCC ];
        if forall{ i : i in [1..#coCC] | Abs(coCC[i] - coZZ[i]) lt 10^(-15) } then
            ht:=P!coZZ;
            Append(~hs,ht);
        end if;
    end for;

    hs:=[h] cat Exclude(Setseq(Seqset(hs)),h); hs;
    assert hs[1] eq h;

    all_iso:=&cat[ IsomorphismClasses(IsogenyClass(ht)) : ht in hs ];
    all_ext:=BaseFieldExtension(all_iso,Ah_4);
    #all_iso,#all_ext;

    for i in [1..#IsomorphismClasses(Ah)] do
        A:=all_iso[i];
        UA:=DeligneAlgebra(A);
        RA,mRA:=ZFVOrder(A);
        FA_elt:=mRA(PrimitiveElement(Algebra(RA)));
        FA:=FrobeniusEndomorphism(A);
        U,u:=UnitGroup(MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]));
        Tors:=[ t : t in TorsionSubgroup(U)];
        TAut:=[ hom<UA->UA|[u(t)*b:b in Basis(UA)]> : t in Tors ];
        Ae:=all_ext[i,1];
        mAe:=all_ext[i,2];
        UAe:=DeligneAlgebra(Ae);
        TF_mAe:=[ Inverse(mAe)*t*FA*mAe : t in TAut ];
        TF_mAe_mats:=[Matrix([t(b) :b in Basis(UAe)]) : t in TF_mAe];
        for j in [1..#all_ext] do
            B:=all_iso[j];
            Be:=all_ext[j,1];
            mBe:=all_ext[j,2];
            test,iso:=IsIsomorphic(Ae,Be);
            if test then
                RB,mRB:=ZFVOrder(B);
                FB_elt:=mRB(PrimitiveElement(Algebra(RB)));
                FB:=FrobeniusEndomorphism(B);
                map:=iso*Inverse(mBe)*FB*mBe*Inverse(iso);
                map_mat:=Matrix([map(b) : b in Basis(UAe)]);
                if exists(a){ a : a in [1..#TF_mAe_mats] | TF_mAe_mats[a] eq map_mat } then 
                    aut:=u(Tors[a]);
                    phi:=HomsToC(Parent(aut))[1];
                    if aut eq 1 then printf "1 ";
                    elif aut eq -1 then printf "-1 ";
                    elif aut^2 eq -1 and Im(phi(aut)) gt 0 then printf "i ";
                    elif aut^2 eq -1 and Im(phi(aut)) lt 0 then printf "-i ";
                    end if;
                else printf "0 ";
                end if;
            else
                printf "_ ";
            end if;
        end for;
        printf "\n";
    end for;

    // new example

    P<x>:=PolynomialRing(Integers());
    h:=x^4 - 205*x^2 + 10609;
    Ah:=IsogenyClass(h);
    Ah_4,map:=BaseFieldExtension(Ah,4);
    h_4:=WeilPolynomial(Ah_4);
    ext_of:=[ I : I in IsBaseFieldExtensionOfPrimitive(Ah_4) | FiniteField(I) eq FiniteField(Ah)]; ext_of;
    iso_all:=&cat[ IsomorphismClasses(I) : I in ext_of ];
    [#IsomorphismClasses(I) : I in ext_of];
    ext_all:=BaseFieldExtension(iso_all,Ah_4);
    assigned ext_all[1,1]`DeligneModuleAsBassMod`StdDirectSumRep;
    for iM0 in [1..#ext_all] do
        M0:=ext_all[iM0];
        time twists:=[ M : M in ext_all | IsIsomorphic(M[1],M0[1]) ];
        iM0,#twists;
    end for;
