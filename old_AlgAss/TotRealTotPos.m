/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Totally Real and Totally Positive of orders in CM etale algebras over \Q
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
/////////////////////////////////////////////////////

    declare attributes AlgAss:TotallyRealSubAlgebra;
    declare attributes AlgAssVOrd:TotallyRealUnitGroup;
    declare attributes AlgAssVOrd:TotallyRealPositiveUnitGroup;

//////////////////////////
// IsTotallyReal, IsTotallyRealPositive
//////////////////////////

    intrinsic IsTotallyReal(a::AlgAssElt) -> BoolElt
    { returns whther a is totally real }
        return a eq ComplexConjugate(a); 
    end intrinsic;

    intrinsic IsTotallyRealPositive(a::AlgAssElt) -> BoolElt
    { returns whether a is totally positive, that is, totally real and with positive image in C }
        return IsTotallyReal(a) and forall{ h : h in HomsToC(Parent(a)) | Re(h(a)) gt 0 }; 
    end intrinsic;

//////////////////////////
// Totally Real SubAlgebra
//////////////////////////

    intrinsic TotallyRealSubAlgebra(K::AlgAss) -> AlgAss,Map
    { given a CM algbra K returns the unique totally real subalgebra, and an embedding }
        if not assigned K`TotallyRealSubAlgebra then
            require HasComplexConjugate(K) : "the algebra does not have CM ";
            a:=PrimitiveElement(K);
            b:=a+ComplexConjugate(a);
            
            F:=AssociativeAlgebra(ChangeRing(MinimalPolynomial(b),Integers()));
            bF:=PrimitiveElement(F);
            bF_pows:=[bF^i : i in [0..Degree(F)-1]];
            assert Degree(K)/Degree(F) eq 2;
            FtoK:=hom<F->K | [&+[b^i*(Coordinates([F.j],bF_pows)[1])[i+1] : i in [0..Degree(F)-1]] : j in [1..Degree(F)] ] >;
            assert FtoK(PrimitiveElement(F)) eq b; 
            K`TotallyRealSubAlgebra:=<F,FtoK>;
        end if;
        return K`TotallyRealSubAlgebra[1],K`TotallyRealSubAlgebra[2];
    end intrinsic;

//////////////////////////
// Totally Real Units
//////////////////////////

    intrinsic TotallyRealUnitGroup(S::AlgAssVOrd) -> Grp
    { Given an order S in a CM étale algebra A
      returns the groups of totally real units of S, as a subgroup of S^* }
        if not assigned S`TotallyRealUnitGroup then
            K:=Algebra(S);
            F,FtoK:=TotallyRealSubAlgebra(K);
            OF:=MaximalOrder(F); // computing OF is not optimal, and possibly avoidable
                                 // on the other hand, to compu te US, one needs OK
            UF,uF:=UnitGroup2(OF); // uF:UF->F
            UK,uK:=UnitGroup2(MaximalOrder(K));
            UFtoUK:=hom< UF->UK | [ (FtoK(uF(UF.i))@@uK) : i in [1..Ngens(UF)]]>;
            US,uS:=UnitGroup2(S);
            US_in_UK:=sub<UK| [(US.i)@uS@@uK : i in [1..Ngens(US)]]>;

            S_tot_real_in_UK:=Image(UFtoUK) meet US_in_UK;
            S_tot_real_in_US:=sub<US| [ (uK(S_tot_real_in_UK.i))@@uS : i in [1..Ngens(S_tot_real_in_UK)] ]>;
            S`TotallyRealUnitGroup:=S_tot_real_in_US;
        end if;
        return S`TotallyRealUnitGroup;
    end intrinsic;

//////////////////////////
// Totally Real Positive Units
//////////////////////////

    debug_test:=function(S,S_tot_pos_in_US) 
    // this test is quite costly!
    // it loops over the subgroups of S*/<v*bar(v) : v in S^*> meet S^* to find the totally positive units
        K:=Algebra(S);
        zbS:=ZBasis(S);
        T:=Order(zbS cat [ ComplexConjugate(z) : z in zbS ]); // T=S*bar(S)
        UT,uT:=UnitGroup2(T); //uT:UT->T
        US, uS := UnitGroup2(S); //uS:US->S
        gensUinS:=[ uS(US.i) : i in [1..Ngens(US)]];
        USUSb:=sub< UT | [ (g*ComplexConjugate(g))@@uT : g in gensUinS ]>; // <v*bar(v) : v in S^*> in UT
        USinUT:=sub<UT | [ g@@uT : g in gensUinS ]>;
        Q,q:=quo< USinUT | USinUT meet USUSb >; // q:=USinUT->Q
                                                // Q = S*/<v bar(v) : v in S*> meet S* in UT
        ker_q:=Kernel(q);
        subs:=Subgroups(Q);
        subs_tp:=[]; // subs of tot pos elements
        for H0 in subs do
            H:=H0`subgroup;
            gensH_inK:=[ uT((Q!H.i)@@q) : i in [1..Ngens(H)]];
            if forall{ g : g in gensH_inK | IsTotallyRealPositive(g)} then
                Append(~subs_tp,H);
            end if;
        end for;
        Htp:=&+subs_tp; // in Q 
        Htp:=Htp@@q; // in USinUT
        gens_Htp_inK:=[Htp.i@uT : i in [1..Ngens(Htp)]];
        assert forall{ g : g in gens_Htp_inK | IsTotallyRealPositive(g) };
        Htp:=sub<US| [g@@uS : g in gens_Htp_inK ]>;
        return Htp eq S_tot_pos_in_US;
    end function;

    intrinsic TotallyRealPositiveUnitGroup(S::AlgAssVOrd) -> Grp
    { Given an order S in a CM étale algebra A
      returns the groups of totally positive units of S, as a subgroup of S^* }
        if not assigned S`TotallyRealPositiveUnitGroup then
            K:=Algebra(S);
            F,FtoK:=TotallyRealSubAlgebra(K);
            OF:=MaximalOrder(F); // computing OF is not optimal, and possibly avoidable
                                 // on the other hand, to compute US, one needs OK
            UF,uF:=UnitGroup2(OF); // uF:UF->F
            UK,uK:=UnitGroup2(MaximalOrder(K));
            UFtoUK:=hom< UF->UK | [ (FtoK(uF(UF.i))@@uK) : i in [1..Ngens(UF)]]>;
            US,uS:=UnitGroup2(S);
            US_in_UK:=sub<UK| [(US.i)@uS@@uK : i in [1..Ngens(US)]]>;

            FF2:=FiniteField(2);
            signs:=Matrix([[ Re(h(uF(UF.i))) gt 0 select (FF2!0) else (FF2!1) : h in HomsToC(F) ] : i in [1..Ngens(UF)]]); 
            sol,ker:=Solution( signs , Vector([FF2!0 : i in [1..Degree(F)]]));
            UF_tot_pos_gens:=   [ 2*UF.i : i in [1..Ngens(UF)] ] cat
                                [ &+[ sol[i]+k[i] eq 1 select UF.i else 0*UF.i : i in [1..Ngens(UF)] ] : k in Basis(ker)] ;
            assert2 debug_test(OF,sub<UF|UF_tot_pos_gens>);
            S_tot_pos_in_UK:=sub<UK| [ g@uF@FtoK@@uK : g in UF_tot_pos_gens ]> meet US_in_UK;
            S_tot_pos_in_US:=sub<US| [ (uK(S_tot_pos_in_UK.i))@@uS : i in [1..Ngens(S_tot_pos_in_UK)] ]>;
            assert2 debug_test(S,S_tot_pos_in_US);
            S`TotallyRealPositiveUnitGroup:=S_tot_pos_in_US;
        end if;
        return S`TotallyRealPositiveUnitGroup;
    end intrinsic;

/* TESTs

    AttachSpec("packages_github/AbVarFq/packages.spec");
    PP<x>:=PolynomialRing(Integers());
    SetAssertions(2);

    f:=x^8+16;
    A:=AssociativeAlgebra(f);
    F:=PrimitiveElement(A);
    R:=Order([F,2/F]);
    oo:=FindOverOrders(R);
    for iS in [1..#oo] do
        S:=oo[iS];
        _:=TotallyRealUnitGroup(S);
        _:=TotallyRealPositiveUnitGroup(S);
    end for;
    SetAssertions(1);

*/
