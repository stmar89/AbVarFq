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

///////////////////////////////////////////////////
// Group of rational points
/////////////////////////////////////////////////////

intrinsic RationalPoints(A::AbelianVarietyFq,r::RngIntElt)-> GrpAb 
{Given an abelian variety over Fq, it returns the group of rational points defined over Fq^r.}
    I:=IsogenyClass(A);
    if IsOrdinary(I) or IsCentelegheStix(I) then
        F:=MapOnDeligneAlgebras(FrobeniusEndomorphism(A));
        zb:=ZBasis(DeligneModule(A));
        Fr:=FreeAbelianGroup(#zb);
        rel:=[ Fr!Eltseq(c) : c in AbsoluteCoordinates( [g-((F^r)(g)) : g in zb],zb ) ];
        Q,_:=quo<Fr|rel>;
        if r eq 1 then // sanity check for points over field of definition
            assert #Q eq Evaluate(WeilPolynomial(A),1);
        end if;
        return Q;
    end if;
end intrinsic;

intrinsic RationalPoints(A::AbelianVarietyFq)-> GrpAb 
{Given an abelian variety over Fq, it returns the group of rational points defined over Fq.}
	return RationalPoints(A,1);
end intrinsic;

