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
// Dual Abelian varieties 
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

/////////////////////////////////////////////////////
// Dual Abelian Variety 
/////////////////////////////////////////////////////

intrinsic DualAbelianVariety(A::AbelianVarietyFq)->AbelianVarietyFq
{Given an abelian variety A returns the dual abelian variety. The isogeny class needs to be ordinary or Centelghe-Stix.}
    require IsOrdinary(A) or IsCentelegheStix(IsogenyClass(A)): "implemented only for ordinary/CentelgehsStix isogeny classes";
    B:=ZBasis(DeligneModule(A));
    n:=#B;
    Q:=Matrix([[Trace(B[i]*B[j]): i in [1..n] ] : j in [1..n]]);
    QQ:=Q^-1;
    BB:=[&+[ (QQ[i,j]*B[j]): j in [1..n]] : i in [1..n]] ;
    BBc:=[ ComplexConjugate(b) : b in BB ];
    Av:=AbelianVarietyFromDeligneModule(IsogenyClass(A),BBc); //the direct sum of ideal is not computed here
    return Av;
end intrinsic;
