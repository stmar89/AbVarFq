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
// Base Field Extension of IsogenyClassesFq and AbelianVarietiesFq
/////////////////////////////////////////////////////

declare verbose BaseFieldExtension, 1;

declare attributes IsogenyClassFq : IsBaseFieldExtensionOf, // the isogeny classes that extend the the given one
                                    IsBaseFieldExtensionOfPrimitive, // the primitive isogeny classes that extend the the given one
                                    IsPrimitive; // is the isogeny class primitive

// ------------------- //
// Instrinsic: Extend q-Weil Poly
// ------------------- //

intrinsic BaseFieldExtension( h::RngUPolElt, r::RngIntElt : prec:=3000) -> RngUPolElt
{Given a q-Weil polynomial, it returns the polynomial hr which is the char poly of Frobenius of A\otimes F_(q^r) for each A in AV(h). The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    require r gt 0 : "the integer must be positive";
    CC:=ComplexField(prec);
    PP:=Parent(h);
    PPCC:=PolynomialRing(CC);
    roots:=Roots(h,CC);
    roots_ext:=&cat([ [s[1]^r : i in [1..s[2]] ] : s in roots ]);
    hrCC:=&*[ PPCC.1-ro : ro in roots_ext ];
    //assert forall{ c : c in Coefficients(hrCC) | IsWeaklyZero(Im(c)) and IsWeaklyZero(Abs(Re(c)-Round(Re(c)))) };
    return PP![Round(Re(c)) : c in Coefficients(hrCC)]; 
end intrinsic;

// ------------------- //
// Extend IsogenyClassFq
// ------------------- //


is_pure_product:=function(V)
// given an etale algebra V returns whether V=K^s for some etale algebra K and some positive integer s;
// the = sign above means that we allow the Components of K to be shuffled, but not isomorphism.
// if so it returs also the s-embeddings K->V and the s-projections V->K
    nfsV,embsV,projsV:=Components(V); 
    polys_V:=[DefiningPolynomial(L):L in nfsV];
    polys_K:=Setseq(Seqset(polys_V));
    if (#polys_V mod #polys_K) ne 0 then
        return false,_,_;
    end if;
    s:=#polys_V div #polys_K;
    if exists{g:g in polys_K|#[f:f in polys_V|f eq g] ne s} then
        return false,_,_;
    end if;
    // Now we now it is a pure power
    assert forall{L:L in nfsV|#[LL:LL in nfsV|LL eq L] eq s}; // to double check that there are no 
                                                              // 'doubly defined' components of V
    K:=EtaleAlgebra(Setseq(Seqset(nfsV)));
    nfsK,embsK,projsK:=Components(K);
    // for each L in nfsK we record the indices of its occurrences in nfsV
    inds:=[[ i : i in [1..#nfsV] | nfsV[i] eq L] : L in nfsK ];
    assert forall{ind:ind in inds | #ind eq s};
    assert Seqset(&cat(inds)) eq {1..#nfsV};
    // we construct the embeddings
    embs:=[];
    for i in [1..s] do
        Append(~embs,Hom(K,V,[&+[embsV[inds[j,i]](projsK[j](z)):j in [1..#nfsK]]:z in AbsoluteBasis(K)]));
    end for;
    // we construct the projections
    projs:=[];
    for i in [1..s] do
        Append(~projs,Hom(V,K,[&+[embsK[j](projsV[inds[j,i]](z)) : j in [1..#nfsK]]:z in AbsoluteBasis(V)]));
    end for;
    assert forall{z:z in AbsoluteBasis(K)|&and[z eq projs[i](embs[i](z)):i in [1..s]]};
    assert forall{z:z in AbsoluteBasis(V)|&and[z eq &+[embs[i](projs[i](z)):i in [1..s]]]};
    return true,embs,projs;
end function;

intrinsic BaseFieldExtension(I::IsogenyClassFq, Ie::IsogenyClassFq : prec:=3000, CheckIsOrdinary:=true )->Map
{Given a squarefree ordinary isogeny class I over Fq and Ie which is the base field extension to F_q^r, the map from the DeligneAlgebra of I to the one of Ie. The Weil polynomials of I and of Ie need to be pure powers of squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    if CheckIsOrdinary then
        require IsOrdinary(I) : "The input isogeny class needs to be ordinary";
    end if;
    r:=Ilog(FiniteField(I),FiniteField(Ie));
    require WeilPolynomial(Ie) eq BaseFieldExtension(WeilPolynomial(I),r : prec:=prec ) : "Ie is not a base field extension of I";
    fac:=Factorization(WeilPolynomial(I));
    exps:={@ g[2] : g in fac @};
    require #exps eq 1 : "The Weil polynomial of I is not a pure power of an squarefree polynomial.";
    fac:=Factorization(WeilPolynomial(Ie));
    exps:={@ g[2] : g in fac @};
    require #exps eq 1 : "The Weil polynomial of Ie is not a pure power of an squarefree polynomial.";
    s:=exps[1];
    UA,m:=DeligneAlgebra(I);
    UAe,me:=DeligneAlgebra(Ie);
    test,embsUA,projsUA:=is_pure_product(UA);
    t:=#projsUA;
    assert test;
    Kh:=Codomain(projsUA[1]);
    Fh:=PrimitiveElement(Kh);
    test,embsUAe,projsUAe:=is_pure_product(UAe);
    st:=#projsUAe;
    assert (st mod t) eq 0;
    s:=st div t;
    assert test;
    Kg:=Codomain(projsUAe[1]);
    Fg:=PrimitiveElement(Kg);
    pow_bas_Kg:=[Fg^j:j in [0..AbsoluteDimension(Kg)-1]];

    // UA=Kh^t , UAe=Kg^st
    sigma:=func<x|&+[AbsoluteCoordinates([x],pow_bas_Kg)[1,j]*Fh^(r*(j-1)) : j in [1..AbsoluteDimension(Kg)]]>; 
    // - sigma: Kg=Q[Fg]->Kh replaces Fg with Fh^r
    // - define the map Kg^s->Kh sending (c1,...,cs):->\sum_i sigma(ci)*Fh^(i-1).
    // - let m be direct sum of t-copies of the map above, UAe=(Kg^s)^t->Kh^t=UA.
    // - finally, we return the inverse of m.
    m:=function(z)
        cc:=[projsUAe[i](z):i in [1..st]];
        cc:=Partition(cc,s);
        return &+[embsUA[j](&+[sigma(cc[j][i])*Fh^(i-1):i in [1..s]]) : j in [1..t]];
    end function;
    m:=Hom(UAe,UA,[m(z):z in AbsoluteBasis(UAe)]: ComputeInverse:=true); // this is the inverse of what we want
    return Inverse(m);
end intrinsic;

intrinsic BaseFieldExtension(AVh::IsogenyClassFq, r::RngIntElt : prec:=3000, CheckIsOrdinary:=true )->IsogenyClassFq,Map
{Given a squarefree ordinary isogeny class AV(h) and a positive integer r, it returns the isogeny class AV(hr) and maps mUA from the DeligneAlgebra of the AV(h) to the one of AV(hr). The Weil polynomials of AV(h) and of the extension AV(h^r) need to be pure powers of a squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    if CheckIsOrdinary then
        require IsOrdinary(AVh) : "The input isogeny class needs to be ordinary";
    end if;
    hr:=BaseFieldExtension(WeilPolynomial(AVh),r : prec:=prec);
    AVhr:=IsogenyClass(hr);
    return AVhr,BaseFieldExtension(AVh,AVhr : prec:=prec );
end intrinsic;
    
intrinsic IsBaseFieldExtensionOf(Ie::IsogenyClassFq : Precision:=300)->SeqEnum
{Given an isogeny class over F_(p^r) it returns the sequence of all isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision". }
    if not assigned Ie`IsBaseFieldExtensionOf then
        P:=PolynomialRing(Integers());
        PC<x>:=PolynomialRing(ComplexField(Precision));
        he:=WeilPolynomial(Ie);
        rr:=Roots(PC!he);
        _,p,r:=IsPrimePower(FiniteField(Ie));
        out:={@ @};
        for s in Divisors(r) do
            ccsq:=[ Roots(x^s-r[1]) : i in [1..r[2]] ,  r in rr];
            ccsq:=CartesianProduct(ccsq);
            for c in ccsq do 
                coCC:=Coefficients(&*[ x-cc[1] : cc in c ]); 
                coZZ:=[ Round(Re(c)) : c in coCC ];
                if forall{ i : i in [1..#coCC] | Abs(coCC[i] - coZZ[i]) lt 10^(-(Precision div 2)) } then
                    ht:=P!coZZ;
                    Include(~out,ht);
                end if;
            end for;
        end for;
        Ie`IsBaseFieldExtensionOf:=[IsogenyClass(ht) : ht in out];
    end if;
    return Ie`IsBaseFieldExtensionOf;
end intrinsic;

intrinsic IsPrimitive(I::IsogenyClassFq : Precision:=300)->SeqEnum
{Returns whether the given isogeny class is primitive, that is, if it is not the base extension of an isogeny class defined over a subfield. The computations is done by looking at the roots of the Weil polynomial of I. The precision of such computations can be set by using the vararg "Precision".}
    if not assigned I`IsPrimitive then
        I`IsPrimitive:=#IsBaseFieldExtensionOf(I : Precision:=Precision) eq 1;
    end if;
    return I`IsPrimitive;
end intrinsic;

intrinsic IsBaseFieldExtensionOfPrimitive(Ie::IsogenyClassFq : Precision:=300)->SeqEnum
{Given an isogeny class over F_(p^r) it returns the sequence of all primitive isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision".}
    if not assigned Ie`IsBaseFieldExtensionOfPrimitive then
        Ie`IsBaseFieldExtensionOfPrimitive:=[ I : I in IsBaseFieldExtensionOf(Ie : Precision:=Precision) | IsPrimitive(I) ];
    end if;
    return Ie`IsBaseFieldExtensionOfPrimitive;
end intrinsic;

// ------------------- //
// Extend AbelianVarietyFq
// ------------------- //

intrinsic BaseFieldExtension(A::AbelianVarietyFq, Ie::IsogenyClassFq, me::Map: CheckIsOrdinary:=true)->AbelianVarietyFq
{Given an ordinary abelian variety A in the isogeny class I, the base field extension Ie of I, together with the map me from the DeligneAlgebra(I) to the DeligneAlgebra(Ie), it returns the base field extension Ae of A in Ie. The Weil polynomial of I and of Ie need to be pure powers of squarefree polynomials.}
    if CheckIsOrdinary then
        require IsOrdinary(A) : "The abelian variety needs to be ordinary";
    end if;
    require WeilPolynomial(Ie) eq BaseFieldExtension(WeilPolynomial(A),Ilog(FiniteField(A),FiniteField(Ie))) : "the given abelin variety does not extend to Ie";
    require Domain(me) eq DeligneAlgebra(IsogenyClass(A)) and Codomain(me) eq DeligneAlgebra(Ie) : "the input does not correspond to a base field extension data"; 
        return AbelianVarietyFromDeligneModule(Ie,[me(g) : g in ZBasis(DeligneModule(A))]);
end intrinsic;

intrinsic BaseFieldExtension( seq::SeqEnum[AbelianVarietyFq], Ie::IsogenyClassFq )->SeqEnum[List]
{Given a sequence of squarefree ordinary abelian varieties A whose isogeny classes extend to Ie, it returns a sequence of pairs [*Ae,me*] consisting of the base field extension of the abelian varieties together with the maps on the DeligneAlgebras. The Weil polynomials of all inputs need to be pure powers of squarefree polynomials}
    isog:={@ IsogenyClass(A) : A in seq @};
    isog_maps:=[ BaseFieldExtension(I,Ie) : I in isog ];
    seq_e:=[ ];
    for A in seq do
        me:=isog_maps[Index(isog,IsogenyClass(A))];
        Append(~seq_e,[*BaseFieldExtension(A,Ie,me),me*]);
    end for;
    return seq_e;
end intrinsic;

// ------------------- //
// Instrinsic: IsTwistOfOrder
// ------------------- //

intrinsic IsTwistOfOrder(A1::AbelianVarietyFq, A2::AbelianVarietyFq, r::RngIntElt : CheckIsOrdinary:=true)-> BoolElt,HomAbelianVarietyFq
{Given two ordinary abelian varieties A1 and A2 (possibly non isogenous) over Fq checks itf they are twist of order r, that is, if they become isomorphic after a base field extension to F_q^r. The Weil polynomials of A1 and A2 and of their extensions need to be pure power of squarefree polynomials. This is the case, for example, if they are simple.}
    if CheckIsOrdinary then
        require IsOrdinary(A1) and IsOrdinary(A2) : "The abelian varieties need to be ordinary";
    end if;
    Ie,me:=BaseFieldExtension(IsogenyClass(A1),r);
    Ie2,_:=BaseFieldExtension(IsogenyClass(A2),r);
    if WeilPolynomial(Ie) eq WeilPolynomial(Ie2) then
        seq_e:=BaseFieldExtension([A1,A2],Ie);
        return IsIsomorphic(seq_e[1,1],seq_e[2,1]);
    else 
        return false,_;
    end if;
end intrinsic;

