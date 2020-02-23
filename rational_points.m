/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
//// Group of rational points
//// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
//// http://www.staff.science.uu.nl/~marse004/
///////////////////////////////////////////////////////

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
	assert #Q eq Evaluate(DefiningPolynomial(A),1);
	return Q,mIQ;
end intrinsic;


//function Kernel(I,J,alpha)
/*
Find the group scheme of the kernel of a particular isogeny
*/



