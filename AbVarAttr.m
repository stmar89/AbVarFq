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

declare verbose AbelianVarieties, 1;

/////////////////////////////////////////////////////
// New Type AbelianVarietyFq
/////////////////////////////////////////////////////

declare type AbelianVarietyFq;

declare attributes AbelianVarietyFq : IsogenyClass;

intrinsic Print(I::AbelianVarietyFq)
{ print the abelian variety }
    printf "Abelian variety over FF_%o",FiniteField(I);
end intrinsic;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( A::AbelianVarietyFq) -> IsogenyClassFq
{Returns the isogeny class of the given abelian variety.}
    return A`IsogenyClass;
end intrinsic;

intrinsic WeilPolynomial(A::AbelianVarietyFq )-> RngUpolElt
{Given an isogeny class AV(h) returns the Weil polynomial h defining it.}
    return WeilPolynomial(IsogenyClass(A));
end intrinsic;

intrinsic FiniteField( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the size of the finite field of definition.}
    return FiniteField(IsogenyClass(A));
end intrinsic;

intrinsic CharacteristicFiniteField( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the characteristic of the finite field of definition.}
    return CharacteristicFiniteField(IsogenyClass(A));
end intrinsic;

intrinsic Dimension( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the dimension.}
    return Dimension(IsogenyClass(A));
end intrinsic;

intrinsic ZFVOrder( A :: AbelianVarietyFq) -> AlgEtQOrd,Map
{Returns the ZFV of the isogeny class of A.}
    return ZFVOrder(IsogenyClass(A));
end intrinsic;

