/* vim: set syntax=magma :*/

// declare attributes AlgEtQOrd :

intrinsic DecompositionKernelOfIsogeny(I::AlgEtQIdl , J::AlgEtQIdl, x::AlgEtQElt)->SeqEnum
{Decomposition of J/x*L.}
    L:=x*I;
    require L subset J : "The elements is not an isogeny between the two ideals";
    R:=Order(I);
    require Order(J) eq R : "The ideals are not defined over the same order";
    A:=Algebra(R);
    g:=Dimension(A) div 2;
    F:=PrimitiveElement(A);
    q:=Truncate(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
    V:=q/F;

    // M = J/L
    pp:=PrimesAbove(ColonIdeal(L,J) meet OneIdeal(R)); // primes above the annihilator = Supp(M)
    rr:=[P : P in pp | not (F in P or V in P)]; // coprime to q, F and V inv
    rl:=[P : P in pp | (not F in P) and (V in P)]; // only F is inv
    lr:=[P : P in pp | (F in P) and (not V in P)]; // only V is inv
    ll:=[P : P in pp | (F in P) and (V in P)]; // both F and V are not inv, empty in the ordinary case

    exp:=function(P)
        _,p,e:=IsPrimePower(Integers()!Index(R,P));
        m:=Valuation(Index(J,L),p) div e;
        return m;
    end function;
   
    output:=[PowerStructure(Tup)|];
    for type in [rr,rl,lr,ll] do
        if #type eq 0 then
            M:=AbelianGroup([]);
            qM:=map< A->M | x:->Zero(M) , y:->Zero(A) >;
            Append(~output,<M,qM>);
        else
            M,qM:=Quotient(J,L+ J*&*[P^exp(P) : P in type]);
            Append(~output,<M,qM>);
        end if;
    end for;
    return output;
end intrinsic;


/*
    AttachSpec("~/packages_github/AlgEt/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/ker_isog.m");

    _<x>:=PolynomialRing(Integers());
    f:=x^8+16;
    A:=EtaleAlgebra(f);
    g:=Dimension(A) div 2;
    F:=PrimitiveElement(A);
    q:=Truncate(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
    V:=q/F;
    R:=Order([F,V]);

    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),F);
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),V);
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),3*One(A));
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),2*One(A));
    
    AttachSpec("~/packages_github/AlgEt/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/ker_isog.m");

    _<x>:=PolynomialRing(Integers());
    f:=x^2+x+2;
    A:=EtaleAlgebra(f);
    g:=Dimension(A) div 2;
    F:=PrimitiveElement(A);
    q:=Truncate(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
    V:=q/F;
    R:=Order([F,V]);

    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),F);
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),V);
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),3*One(A));
    DecompositionKernelOfIsogeny(OneIdeal(R),OneIdeal(R),2*One(A));



*/
