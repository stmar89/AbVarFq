/* vim: set syntax=magma :*/

freeze;

//////////////////////////////////////////////////////////////
// Representatives of Z-conjugacy classes of integral matrices
// with square-free characteristic polynomial
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
//////////////////////////////////////////////////////////////

intrinsic RepresentativesZConjugate( f::RngUPolElt ) -> Seq
{given a monic square-free polynomial f with integer coefficients it returns a set of representatives of the Z-conjugacy classes of integral matrices with characteristic (and hence also minimal) polynomial f }
	require BaseRing(f) eq Integers() : "the polynomial doesn't have integer coefficients";
	require IsSquarefree(f) : "the polynomial is not squarefree";
	require IsMonic(f) : "the polynomial is not monic";

	A:=AssociativeAlgebra(f);
	E:=EquationOrder(A);
	icm:=ICM(E);
	reps:=[ IdealToMatrix(I) : I in icm ];
	return reps;
end intrinsic;
