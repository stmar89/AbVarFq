/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Completion of AlgAss at Prime ideals
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

intrinsic Completion(P::AlgAssVOrdIdl : MinPrecision:=20) -> FldPad,Map
{ Given a prime ideal of the maximal order of an etale algebra L it returns the number field corresponding to the completion LP and a homormophism map:L->LP. The vararg MinPrecision is passed to Completion. map has preimage, even if not injective. }
    L:=Algebra(P);
    require IsMaximal(Order(P)) and IsPrime(P) : "the ideal must be a prime ideal of the maximal order";
    nfs:=L`NumberFields;
    test,PKs:=IsProductOfIdeals(P);
    assert test;
    ind:=[ i : i in [1..#PKs] | not (Order(PKs[i]) ! 1) in PKs[i] ];
    assert #ind eq 1;
    ind:=ind[1];
    K:=nfs[ind,1];
    mK:=nfs[ind,2]; // mK:=K->L
    PK:=PKs[ind];
    LP,mLP:=Completion(K,PK : Precision:=MinPrecision); // mLP:K->LP
    //map:=Inverse(mK)*mLP;
    map:=hom< L->LP | x:->mLP(Components(x)[ind]) ,
                      y:->mK(y@@mLP) >;
    return LP,map;
end intrinsic;

/*
//TESTS
    
    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    PP<x>:=PolynomialRing(Integers());

    polys:=[
        x^6+3*x^4-10*x^3+15*x^2+125,
        (x^2+5)*(x^4-4*x^3+5*x^2-20*x+25),
        (x^4-5*x^3+15*x^2-25*x+25)*(x^4+5*x^3+15*x^2+25*x+25)
        ];
    for h in polys do
        L:=AssociativeAlgebra(h);
        O:=MaximalOrder(L);
        p:=5;
        pp:=PrimesAbove(p*O);
        for P in pp do
            Completion(P);
        end for;
    end for;

*/
