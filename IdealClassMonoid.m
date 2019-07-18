freeze;

/////////////////////////////////////////////////////
// Ideal class monoid and weak equivalence classes for orders in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

declare attributes AlgEtOrd: WKICM_bar,WKICM,ICM_bar,ICM;

intrinsic WKICM_bar(S::AlgEtOrd) -> SeqEnum
{returns all the weak eq classes I, such that (I:I)=S}
//TODO : prime per prime;
    if not assigned S`WKICM_bar then
        if IsGorenstein(S) then
            S`WKICM_bar:=[OneIdeal(S)];
        else
            A:=Algebra(S);
            degA:=Degree(A);
            seqWk_bar:=[];
            St:=TraceDualIdeal(S);
            T:=&meet([ T : T in FindOverOrders(S) | IsInvertible(T !! St) ]);
            //this construction of T is conjectural, hence the next assert. If the assert fails, please report it.
            assert IsInvertible(T !! St);
            T_ZBasis:=ZBasis(T);
            ff:=ColonIdeal(S,Ideal(S,T_ZBasis));
            ff_ZBasis:=ZBasis(ff);
            seqWk_bar:=[];
            F:=FreeAbelianGroup(Degree(Algebra(S)));
            matT:=Matrix(T_ZBasis);
            matff:=Matrix(ff_ZBasis);
            rel:=[F ! Eltseq(x) : x in Rows(matff*matT^-1)];
            Q,q:=quo<F|rel>; //Q=T/(S:T)
            QP,f:=FPGroup(Q);
            subg:=LowIndexProcess(QP,<1,#QP>);
            while not IsEmpty(subg) do
                H := ExtractGroup(subg);
                NextSubgroup(~subg);
                geninF:=[(f(QP ! x))@@q : x in Generators(H)];
                coeff:=[Eltseq(x) : x in geninF];
                I:=Ideal(S,[&+[T_ZBasis[i]*x[i] : i in [1..degA]] : x in coeff] cat Generators(ff));
                if MultiplicatorRing(I) eq S and not exists{J : J in seqWk_bar | IsWeakEquivalent(I,J)} then 
                    Append(~seqWk_bar,I);
                end if;
            end while;
            S`WKICM_bar:=seqWk_bar;
        end if;
     end if;
     return S`WKICM_bar;
end intrinsic;

intrinsic WKICM(E::AlgEtOrd)->SeqEnum
{computes the Weak equivalence class monoid of E}
    if not assigned E`WKICM then
        A:=Algebra(E);
        seqOO:=FindOverOrders(E);
        E`WKICM:= &cat[[(E!!I) : I in WKICM_bar(S)] : S in seqOO ];
    end if;
    return E`WKICM;
end intrinsic;

intrinsic ICM_bar(S::AlgEtOrd : GRH:=false ) -> SeqEnum
{returns the ideal classes of the order S having S as MultiplicatorRing, that is the orbits of the action of PicardGroup(S) on WKICM_bar(S)}
    if not assigned S`ICM_bar then
        seqWKS_bar:=WKICM_bar(S);
        GS,gS:=PicardGroup(S : GRH:=GRH );
        repS:=[gS(x) : x in GS];
        ICM_barS := &cat[[(S!!I)*(S!!J) : I in seqWKS_bar] : J in repS];
        assert2 forall{J : J in ICM_barS | MultiplicatorRing(J) eq S};
        assert forall{J : J in ICM_barS | Order(J) eq S};
        S`ICM_bar:=ICM_barS;
    end if;
    return S`ICM_bar;
end intrinsic;

intrinsic ICM(S::AlgEtOrd : GRH:=false ) -> SeqEnum
{returns the ideal class monoid of the order, that is a set of representatives for the isomorphism classes of the fractiona ideals}
    if not assigned S`ICM then
        seqOO:=FindOverOrders(S);
        seqICM:=[];
        for T in seqOO do
            ICM_barT := [(S!!I) : I in ICM_bar(T: GRH:=GRH )];
            seqICM:=seqICM cat ICM_barT;
        end for;
        assert forall{I: I in seqICM | Order(I) eq S};
        S`ICM:= seqICM;
    end if;
    return S`ICM;
end intrinsic;
