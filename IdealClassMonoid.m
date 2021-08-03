/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Ideal class monoid and weak equivalence classes for orders in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////


/////////////////////////////////////////////////////
// functions for orders that locally have CM-type \leq 2
/////////////////////////////////////////////////////
// In a so-far-unpublished note I have proved that 
// if S^t/P*S^t has dimension 2 over S/P then
// locally at P the only fractional ideals with 
// multiplicator ring S are S and S^t.

wkicm_bar_CM_dim2:=function(S,St,pp)
// Input:
//  S is an order such that for all primes P we have d(P) le 2.
//  St is the trace dual of S
//  pp is the list of primes P at which d(P)=2.
// Output: a sequence of ideals of S containing all weak equivalence 
//  classes of fractional ideals with multiplicator ring S.
    if #pp eq 1 then
        return [OneIdeal(S),St];
    else
        I:=MakeIntegral(St);
        pows:=[];
        for P in pp do
            _,p,e:=IsPrimePower(Integers()!Index(S,P)); // e=Valuation(p,Index(S,P));
            m:=Valuation(Index(S,I),p) div e; // Here we are using Proposition 4.2 of Klueners and Pauli 
                                              // "Computing residue class rings ...".
                                              // With such an m we have:
                                              //   pp[i]^m \subseteq I_pp[i]
            Append(~pows,P^m);
        end for;
        pows_hat:=[ &*[ pp[j] : j in [1..#pp] | j ne i ] : i in [1..#pp] ];
        Is:=[ seq : seq in CartesianProduct([[OneIdeal(S),I] : i in [1..#pp]]) ];
        out:=[];
        for I in Is do
            L:=&+[ (I[i]+pows[i]) * pows_hat[i] : i in [1..#pows_hat]];
            Append(~out,L);
        end for;
        return out;
     end if;
end function;

is_CM_dim2:=function(S)
// Input: an order S.
// Output: t,St,pp
// where t is a Boolean, St is the trace dual of S, and pp is a list of primes of S at which S is not locally Gorenstein
// t is true if and only if S is not Gorenstein, but d(P) is le 2 for every P.
    St:=TraceDualIdeal(S);
    pp0:=PrimesAbove(Conductor(S));
    pp:=[];
    dPs:=[];
    for P in pp0 do
        k:=Integers() ! Index(S,P);
        v:=Integers() ! Index(St,P*St);
        dP:=Ilog(k,v);
        if dP gt 1 then // don't want P such that S_P is Gorenstein
            Append(~pp,P);
            Append(~dPs,dP);
        end if;
    end for;
    if #dPs ne 0 and forall{dP : dP in dPs | dP eq 2} then //i.e. S is not Gorenstein and CM-dim is at most 2
        t:=true;
    else
        t:=false;
    end if;
    return t,St,pp;
end function;

intrinsic WKICM_bar(S::AlgAssVOrd) -> SeqEnum
{returns all the weak eq classes I, such that (I:I)=S}
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    if IsGorenstein(S) then
        return [OneIdeal(S)];
    else
        test,St,pp:=is_CM_dim2(S);    
        if test then
            return wkicm_bar_CM_dim2(S,St,pp);
        else
            // general case
            //TODO : prime per prime;
            A:=Algebra(S);
            degA:=Degree(A);
            seqWk_bar:=[];
            St:=TraceDualIdeal(S);
            T:=&meet([ T : T in FindOverOrders(S) | IsInvertible(T ! St) ]);
            //this construction of T is conjectural, hence the next assert. If the assert fails, please report it.
            assert IsInvertible(T ! St);
            T_ZBasis:=ZBasis(T);
            ff:=ColonIdeal(S,ideal<S|T_ZBasis>);
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
                I:=ideal<S| [&+[T_ZBasis[i]*x[i] : i in [1..degA]] : x in coeff] cat ff_ZBasis>;
                if MultiplicatorRing(I) eq S and not exists{J : J in seqWk_bar | IsWeakEquivalent(I,J)} then 
                    Append(~seqWk_bar,I);
                end if;
            end while;
            return seqWk_bar;
        end if;
    end if;
end intrinsic;

intrinsic WKICM(E::AlgAssVOrd)->SeqEnum
{computes the Weak equivalence class monoid of E}
    A:=Algebra(E);
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    seqOO:=FindOverOrders(E);
    return &cat[[(E!I) : I in WKICM_bar(S)] : S in seqOO ];
end intrinsic;

intrinsic ICM_bar(S::AlgAssVOrd : GRH:=false ) -> SeqEnum
{returns the ideal classes of the order S having S as MultiplicatorRing, that is the orbits of the action of PicardGroup(S) on WKICM_bar(S)}
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    seqWKS_bar:=WKICM_bar(S);
    GS,gS:=PicardGroup(S : GRH:=GRH );
    repS:=[gS(x) : x in GS];
    ICM_barS := &cat[[(S!I)*(S!J) : I in seqWKS_bar] : J in repS];
    assert2 forall{J : J in ICM_barS | MultiplicatorRing(J) eq S};
    assert forall{J : J in ICM_barS | Order(J) eq S};
    return ICM_barS;
end intrinsic;

intrinsic ICM(S::AlgAssVOrd : GRH:=false ) -> SeqEnum
{returns the ideal class monoid of the order, that is a set of representatives for the isomorphism classes of the fractiona ideals}
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    seqOO:=FindOverOrders(S);
    seqICM:=[];
    for T in seqOO do
        ICM_barT := [(S!I) : I in ICM_bar(T: GRH:=GRH )];
        seqICM:=seqICM cat ICM_barT;
    end for;
    assert forall{I: I in seqICM | Order(I) eq S};
    return seqICM;
end intrinsic;
