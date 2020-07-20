/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
//// Group of rational points
//// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
//// http://www.staff.science.uu.nl/~marse004/
///////////////////////////////////////////////////////

intrinsic RationalPoints(A::AbelianVarietyFq,r::RngIntElt)-> GrpAb 
{ Given an abelian variety over Fq, it returns the group of rational points defined over Fq^r }
    F:=MapOnUniverseAlgebras(FrobeniusEndomorphism(A));
    zb:=DeligneModuleZBasis(A);
	Fr:=FreeAbelianGroup(#zb);
	rel:=[ Fr!Eltseq(c) : c in Coordinates( [g-((F^r)(g)) : g in zb],zb ) ];
	Q,_:=quo<Fr|rel>;
    if r eq 1 then // sanity check for points over field of definition
        assert #Q eq Evaluate(WeilPolynomial(A),1);
    end if;
	return Q;
end intrinsic;

intrinsic RationalPoints(A::AbelianVarietyFq)-> GrpAb 
{ Given an abelian variety over Fq, it returns the group of rational points defined over Fq }
	return RationalPoints(A,1);
end intrinsic;

// Old code kept for retrocompatibility

intrinsic RationalPoints(I::AlgAssVOrdIdl,r::RngIntElt)-> GrpAb , Map
{Computes the group FF_(q^r) rational points G of the abelian variety determined by I and returns G,g, where g is a surjective map I->G}
	A:=Algebra(Order(I));
	F:=PrimitiveElement(A);
	zb:=ZBasis(I);
	Fr:=FreeAbelianGroup(#zb);
	rel:=[ Fr!Eltseq(c) : c in Coordinates( [(1-F^r)*g : g in zb],zb ) ];
	Q,q:=quo<Fr|rel>;
	mIQ:=map< A->Q | x:->q(Fr ! Eltseq(Coordinates([x],zb)[1])),
			   y:->A ! ((&+[ zb[j]*Eltseq(y)[j] : j in [1..#zb]])@@q)>;
    if r eq 1 then // sanity check for points over field of definition
        assert #Q eq Evaluate(DefiningPolynomial(A),1);
    end if;
	return Q,mIQ;
end intrinsic;

/* TESTs
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");

    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    S1:=ZFVOrder(AVh);
    O:=MaximalOrder(Algebra(S1));
    over_orders:=FindOverOrders(S1);
    for S in over_orders do
        iso_S:=ComputeIsomorphismClassesWithEndomorphismRing(AVh,S);
        for r in [1..8] do
            r,{ ElementaryDivisors(RationalPoints(A,r)) : A in iso_S};
        end for;
    end for;

    _<x>:=PolynomialRing(Integers());
    h:=x^8-5*x^7+13*x^6-25*x^5+44*x^4-75*x^3+117*x^2-135*x+81;
    AVh:=IsogenyClass(h);
    S1:=ZFVOrder(AVh);
    O:=MaximalOrder(Algebra(S1));
    over_orders:=FindOverOrders(S1);
    for S in over_orders do if not IsGorenstein(S) then
        iso_S:=ComputeIsomorphismClassesWithEndomorphismRing(AVh,S);
        #iso_S;
        { ElementaryDivisors(RationalPoints(A)) : A in iso_S};
    end if; end for;

*/



