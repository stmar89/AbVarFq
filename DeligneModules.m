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
// Abelian varieties using Deligne Modules
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

declare attributes IsogenyClassFq : 
           DeligneAlgebra,  // An AlgEtQ constructed from the Weil polynomial. 
                            // eg. if h=g1^s1*g2^s2 then it equals (Q[x]/g1)^s1 x (Q[x]/g2)^s2 
                            // In the ordinary or Centeleghe-Stix case, it contains the Deligne modules.
           FrobeniusEndomorphismOnDeligneAlgebra;
                            // An endomorphism of the DeligneAlgebra representing the Frobenius.

declare attributes AbelianVarietyFq : DeligneModule; //of type AlgEtQMod

/////////////////////////////////////////////////////
// New Type AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic DeligneAlgebra(I::IsogenyClassFq)-> AlgEtQ,Map
{Given an isogeny class AV(h), defined by the Weil polynomial h with factorization over Q equal to h=g1^s1*...*gn^sn, it returns the algebra V=prod_i=1^n (Q[x]/gi)^si, where the DeligneModules live (if ordinary of CentelgeheStix), together with the componentwise diagonal action of ZFV.}
    if not assigned I`DeligneAlgebra then
        E:=Algebra(ZFVOrder(I));
        h:=WeilPolynomial(I);
        if IsSquarefree(h) then
            I`IsSquarefree:=true;
            Ah:=E;
        else
            nfs:=Components(E);
            fac:=Factorization(h);
            sq_fac:=[f[1] : f in fac];
            exps:=[f[2]:f in fac];
            nf_h:=[];
            for K in nfs do
                g:=DefiningPolynomial(K);
                nfK:=[ K : j in [1..exps[Index(sq_fac,g)]]]; 
                nf_h cat:=nfK;
            end for;
            Ah:=EtaleAlgebra(nf_h);
        end if;
        delta:=NaturalAction(E,Ah); // componentwise diagonal
        I`DeligneAlgebra:=<Ah,delta>;
    end if;
    return Explode(I`DeligneAlgebra);
end intrinsic;

intrinsic FrobeniusEndomorphismOnDeligneAlgebra(I::IsogenyClassFq)-> Map
{Given an isogeny class AV(h) returns the Frobenius endomorphism (acting on the DeligneAlgebra).}
    if not assigned I`FrobeniusEndomorphismOnDeligneAlgebra then
        UA,mR:=DeligneAlgebra(I);
        R:=ZFVOrder(I);
        FUA:=mR(PrimitiveElement(Algebra(R)));
        abs:=AbsoluteBasis(UA);
        F:=Hom(UA,UA,[FUA*abs[i] : i in [1..Dimension(UA)] ]);
        I`FrobeniusEndomorphismOnDeligneAlgebra:=F;
    end if;
    return I`FrobeniusEndomorphismOnDeligneAlgebra;
end intrinsic;

/////////////////////////////////////////////////////
// Creation functions of AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic AbelianVarietyFromDeligneModule(AVh::IsogenyClassFq,M::AlgEtQMod)->AbelianVarietyFq
{Returns the abelian variety defined by a Z[F,V]-module M. The isogeny class needs to be ordinary, almost ordinary or CentelegheStix.} 
    require IsOrdinary(AVh) or IsAlmostOrdinary(AVh) or IsCentelegheStix(AVh) : "The isogeny class is not ordinary, almost ordinary or CentelegheStix.";
    R:=ZFVOrder(AVh);
    require R eq Order(M):"The module is not defined over the order Z[F,V] of the given isogeny class.";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    AV`DeligneModule:=M;
    return AV;
end intrinsic;

intrinsic AbelianVarietyFromDeligneModule( AVh::IsogenyClassFq , I::AlgEtQIdl )->AbelianVarietyFq
{Returns the abelian variety defined by a fractional ideal I of the Z[F,V] order of the isogeny class AV(h), where h is the characteristic polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.} 
    require IsSquarefree(AVh) and (IsOrdinary(AVh) or IsAlmostOrdinary(AVh) or IsCentelegheStix(AVh)) : "The isogeny class is not squarefree and ordinary, almost ordinary or CentelegheStix.";
    _,map:=DeligneAlgebra(AVh);
    R:=ZFVOrder(AVh);
    require R eq Order(I):"The fractional ideal is not defined over the order Z[F,V] of the given isogeny class.";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    AV`DeligneModule:=ModuleFromDirectSum(R,map,[<I,map>]);
    return AV;
end intrinsic;

intrinsic AbelianVarietyFromDeligneModule( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQIdl] )-> AbelianVarietyFq
{Returns the abelian variety defined by a direct sum of s fractional ideals of the Z[F,V] order of the isogeny class AV(g^s), where g is the miniml polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.} 
    require IsSquarefree(AVh) and (IsOrdinary(AVh) or IsAlmostOrdinary(AVh) or IsCentelegheStix(AVh)) : "The isogeny class is not squarefree and ordinary, almost ordinary or CentelegheStix.";
    UA,delta:=DeligneAlgebra(AVh);
    R:=ZFVOrder(AVh);
    s:=#seq;
    require forall{ I : I in seq | R eq Order(I) } : "the sequence of fractional ideals does not define an abelin variety in the given isogeny class";
    E:=Algebra(R);
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    ort:=OrthogonalIdempotents(UA);
    DM:=[];
    require #ort eq s : "Not enough ideals to generate an abelian variety in this isogeny class.";
    for i in [1..s] do
        I:=seq[i];
        map:=Hom(E,UA,[delta(z)*ort[i]:z in AbsoluteBasis(E)]); // embedding of Ag->Ag^s into the ith component
        Append(~DM,<I,map>);
    end for;    
    AV`DeligneModule:=ModuleFromDirectSum(R,delta,DM);
    return AV;
end intrinsic;

intrinsic AbelianVarietyFromDeligneModule( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQElt] )-> AbelianVarietyFq
{Returns the abelian variety defined defined by the module generated by the elements in seq. The isogeny class needs to be ordinary or CentelegheStix.}
    require IsOrdinary(AVh) or IsAlmostOrdinary(AVh) or IsCentelegheStix(AVh) : "The isogeny class is not ordinary, almost ordinary or CentelegheStix.";
    UA,delta:=DeligneAlgebra(AVh);
    R:=ZFVOrder(AVh);
    require forall{ g : g in seq | Parent(g) eq UA } : " the elements are not in the DeligneAlgebra(A)";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    AV`DeligneModule:=Module(R,delta,seq);
    return AV;
end intrinsic;

intrinsic AbelianVarietyFromDeligneModule(AVh::IsogenyClassFq,seq::SeqEnum[Tup])->AbelianVarietyFq
{Given an isogeny class and sequence of pairs  <J_i,v_i> returns the abelin variety in the given isogeny class defined by the Deligne Module J_1v_1+...+J_sv_s. The isogeny class needs to be ordinary or CentelegheStix.}
    require IsPurePower(AVh) and (IsOrdinary(AVh) or IsAlmostOrdinary(AVh) or IsCentelegheStix(AVh)) : "The isogeny class is not pure power and ordinary, or almost ordinary or Centeleghe.";
    UA,delta:=DeligneAlgebra(AVh);
    R:=ZFVOrder(AVh);
    s:=#seq;
    require forall{ J : J in seq | R eq Order(J[1]) and Parent(J[2]) eq UA } : "the sequence of fractional ideals does not define an abelin variety in the given isogeny class";
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=AVh;
    AV`DeligneModule:=Module(R,delta,seq);
    return AV;
end intrinsic;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic DeligneModule(A :: AbelianVarietyFq)->AlgEtQMod
{Returns the DeligneModule defining the variety A.}
    return A`DeligneModule;
end intrinsic;

intrinsic DeligneAlgebra( A :: AbelianVarietyFq) -> AlgEqQ
{Returns the DeligneAlgebra where the DeligneModule lives in.}
    return DeligneAlgebra(IsogenyClass(A));
end intrinsic;

/////////////////////////////////////////////////////
// Equality testing for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic 'eq'( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt
{Checks if two abelin varieties are equal, using the appropriate categorical description.}
    I:=IsogenyClass(A1);
    if I eq IsogenyClass(A2) then
        if IsOrdinary(I) or IsCentelegheStix(I) then
            return DeligneModule(A1) eq DeligneModule(A2);
        elif IsSquarefree(I) then
            return IsomDataCommEndAlg(A1) eq IsomDataCommEndAlg(A2);
        else
            error "not implemented yet";
        end if;
    else
        vprintf AbelianVarieties : "eq : the abelian varities are not in the same isogeny class \n";
        return false;
    end if;
end intrinsic;

