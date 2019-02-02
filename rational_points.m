/*

STEPHANOS CODE FOR TAKING THE QUOTIENT AS AN ABELIAN

TODO: needs to compute elementary divisors

*/



Fq_points:=function(I,r)
//Computes the group FF_{q^r} rational points of the variety
/*
P<x>:=PolynomialRing(Integers());
f:=x^6 - 4*x^5 + 16*x^4 - 53*x^3 + 128*x^2 - 256*x + 512;
A:=AssociativeAlgebra(f);
R:=Order([13*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+13*A.2+0*A.3+0*A.4+0*A.5+0*A.6,1*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+1*A.4+0*A.5+0*A.6,5*A.1+1*A.2+0*A.3+0*A.4+1*A.5+0*A.6,2*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]);
S:=Order([1*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+0*A.2+0*A.3+1*A.4+0*A.5+0*A.6,0*A.1+0*A.2+0*A.3+0*A.4+1*A.5+0*A.6,0*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]);
phi_pos_elt:=7*A.1+-14*A.2+-68*A.3+5/8*A.4+53/8*A.5+41/8*A.6;
I:=<ideal<R|[13*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+13*A.2+0*A.3+0*A.4+0*A.5+0*A.6,1*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+1*A.4+0*A.5+0*A.6,5*A.1+1*A.2+0*A.3+0*A.4+1*A.5+0*A.6,2*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]>,[1/403*A.1+-2/403*A.2+32009/35139*A.3+-106259/140556*A.4+2417/10812*A.5+-2999/140556*A.6],2>[1];
F:=PrimitiveElement(A);

AFq := Fq_points(I,1);
#AFq eq Evaluate(f,1);
/*
    FA:=PrimitiveElement(Algebra(I));
    zb:=ZBasis(I);
    Fr:=FreeAbelianGroup(#zb);
    rel:=[ Fr!Eltseq(c) : c in Coordinates( [(1-FA^r)*g : g in zb],zb ) ];
    return quo<Fr|rel>;
end function;


