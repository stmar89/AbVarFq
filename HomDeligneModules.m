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
// Morphisms of Abelian varieties over Finite Fields
// using Deligne Modules
/////////////////////////////////////////////////////

declare verbose HomAbelianVarieties, 1;


//TODO Composition of morphisms, Automorphism/EndomorphismRing,PolarizedAutomorphismGroup should all return also a funciton to create an HomAbelianVarietyFq

/////////////////////////////////////////////////////
// NewType: HomAbelianVarietyFq
// a morphism of abelin varieties over Fq
/////////////////////////////////////////////////////

declare attributes AbelianVarietyFq : FrobeniusEndomorphism;

declare type HomAbelianVarietyFq;
declare attributes HomAbelianVarietyFq : Domain,
                                         Codomain,
                                         // Image, //does it makes sense?
                                         // Kernel, //what should this be? 
                                         MapOnDeligneAlgebras,
                                         IsIsogeny, // a pair true or false, Degree
                                         IsIsomorphism,
                                         IsEndomorphism;

/////////////////////////////////////////////////////
// Access, Print 
/////////////////////////////////////////////////////

intrinsic Print(m::HomAbelianVarietyFq)
{ print the morphism abelian variety }
    printf "Morphism from %o to %o",Domain(m),Codomain(m);
end intrinsic;

intrinsic Domain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the domain the morphism}
    return m`Domain;
end intrinsic;

intrinsic Codomain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the codomain the morphism}
    return m`Codomain;
end intrinsic;

intrinsic MapOnDeligneAlgebras(m::HomAbelianVarietyFq)->Map
{returns underlying homormorphism of Deligne Moduels as a Z[F,V]-linear hom on the DeligneAlgebras}
    return m`MapOnDeligneAlgebras;
end intrinsic;

intrinsic IsEndomorphism(m::HomAbelianVarietyFq)->BoolElt 
{returns whether the morphism is an endomorphism}
    if not assigned m`IsEndomorphism then
        m`IsEndomorphism:=Domain(m) eq Codomain(m);
    end if;
    return m`IsEndomorphism;
end intrinsic;

// TODO IsIsogeny, Degree, IsIsomorphsim 

/////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////

intrinsic Hom(A::AbelianVarietyFq,B::AbelianVarietyFq,map::Map : Check:=true)->HomAbelianVarietyFq
{Creates a morphisms of abelian varieties A->B determined by map, where map is a morphisms of the DeligneAlgebras of A and B. The vararg Check allows to skip the test of the compatibility with the Frobenius.}
    IA:=IsogenyClass(A);
    IB:=IsogenyClass(B);
    require (IsOrdinary(IA) and IsOrdinary(IB)) or (IsCentelegheStix(IA) and IsCentelegheStix(IB)) : "The isogeny classes should both be ordinary or both be CentelegheStix";
    if Check then
        FA:=MapOnDeligneAlgebras(FrobeniusEndomorphism(A));
        FB:=MapOnDeligneAlgebras(FrobeniusEndomorphism(B));
        UA:=DeligneAlgebra(A);
        require UA eq Domain(map) and DeligneAlgebra(B) eq Codomain(map) and 
                forall{z:z in AbsoluteBasis(UA)|map(FA(z)) eq FB(map(z)) } //the map must be Frobanius-linear
                          : "the map does not define a morphism of abelian varieties";
    end if;
    hom:=New(HomAbelianVarietyFq);
    hom`Domain:=A;
    hom`Codomain:=B;
    hom`MapOnDeligneAlgebras:=map;
    return hom;
end intrinsic;

/////////////////////////////////////////////////////
// Frobenius
/////////////////////////////////////////////////////

intrinsic FrobeniusEndomorphism(A::AbelianVarietyFq)-> HomAbelianVarietyFq
{Returns the Frobenius endomorphism (acting on the DeligneAlgebra).}
    if not assigned A`FrobeniusEndomorphism then
        FUA:=FrobeniusEndomorphismOnDeligneAlgebra(IsogenyClass(A));
        A`FrobeniusEndomorphism:=Hom(A,A,FUA : Check:=false ); //the Check:=false is necessary to prevent a loop
    end if;
    return A`FrobeniusEndomorphism;
end intrinsic;

