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

/////////////////////////////////////////////////////
// Endomorphism rings
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

declare attributes AbelianVarietyFq : EndomorphismRing;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic EndomorphismRing(A::AbelianVarietyFq)-> AlgEtQOrd
{Returns Endomorphism ring of the abelian variety.}
    require IsSquarefree(IsogenyClass(A)):"at the moment it is implemented only for squarefree abelian varieties";
    I:=IsogenyClass(A);
    if not assigned A`EndomorphismRing then
        if IsOrdinary(I) or IsCentelegheStix(I) then
            A`EndomorphismRing:=compute_multiplicator_overorder(DeligneModule(A));
        elif IsSquarefree(I) then
            return A`EndomorphismRing;
        else
            error "not implemented yet";
        end if;
    end if;
    return A`EndomorphismRing;
end intrinsic;

