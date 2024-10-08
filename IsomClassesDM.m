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
// Abelian varieties and Isogeny classes
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

intrinsic IsIsomorphic(A1::AbelianVarietyFq,A2::AbelianVarietyFq) -> BoolElt,HomAbelianVarietyFq
{Checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism.}
    vprintf AbelianVarieties,1 : " IsIsomorphic :";
    I:=IsogenyClass(A1);
    if I eq IsogenyClass(A2) then
        if IsOrdinary(I) or IsCentelegheStix(I) then
            test,map:=IsIsomorphic(DeligneModule(A1),DeligneModule(A2));
            if test then
                return true,Hom(A1,A2,map);
            else
                return false,_;
            end if;
        elif IsSquarefree(I) then
            error "not implemented"; // as of 20240912 we don't have this functionality implemented. probably it will come in the future.
        else
            error "not implemented"; 
        end if; 
    else
        vprintf AbelianVarieties : "IsIsomorphic : the abelian varities are not in the same isogeny class \n";
        return false,_;
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// Compute all isomorphism classes in a given Isogeny class
/////////////////////////////////////////////////////

intrinsic IsomorphismClasses(AVh::IsogenyClassFq)->SeqEnum[AbelianVarietyFq]
{Computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class.}
    if not assigned AVh`IsomorphismClasses then
        if IsOrdinary(AVh) or IsCentelegheStix(AVh) then
            _,map:=DeligneAlgebra(AVh);
            R:=ZFVOrder(AVh);
            isom_DMs:=IsomorphismClasses(R,map);
            AVh`IsomorphismClasses:=[AbelianVarietyFromDeligneModule(AVh,M):M in isom_DMs];
        elif IsSquarefree(AVh) then
            AVh`IsomorphismClasses:=IsomorphismClassesCommEndAlg(AVh); 
        else
            error "not implemented for such an isogeny class"; 
        end if;
    end if;
    return AVh`IsomorphismClasses;
end intrinsic;
