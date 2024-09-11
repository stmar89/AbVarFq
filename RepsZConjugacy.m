/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Stefano Marseglia, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// 
// Distributed under the terms of the GNU Lesser General Public License (L-GPL)
//      http://www.gnu.org/licenses/
// 
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation; either version 3.0 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA
// 
// Copyright 2024, S. Marseglia
/////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////
// Representatives of Z-conjugacy classes of integral matrices
// with square-free characteristic polynomial
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
