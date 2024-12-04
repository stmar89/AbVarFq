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
// CM Types
/////////////////////////////////////////////////////

declare verbose CMAlgEt, 1;

/////////////////////////////////////////////////////
// AllCMTypes 
/////////////////////////////////////////////////////

declare attributes IsogenyClassFq : AllCMTypes;

intrinsic AllCMTypes(AVh::IsogenyClassFq : precCC := 30 ) -> SeqEnum[AlgEtQCMType]
{Returns all the AlgEtQCMType of Algebra(ZFVOrder(AVh)).}
    if not assigned AVh`AllCMTypes then
        A:=Algebra(ZFVOrder(AVh));
        cc:=CartesianProduct(Partition([ h: h in HomsToC(A : Precision:=precCC )],2));
        cc:=[ [ci : ci in c] : c in cc ]; //from tuple to seq
        AVh`AllCMTypes:=[ CreateCMType(c) : c in cc ];
    end if;
    return AVh`AllCMTypes;
end intrinsic;

/////////////////////////////////////////////////////
// pAdicPosCMType for ordinary IsogenyClassFq
/////////////////////////////////////////////////////

declare attributes IsogenyClassFq : pAdicPosCMType; //this will be of type 'AlgEtQCMType'
declare attributes AlgEtQCMType : pAdicData; // it stores a tuple < p,rrtspp,rtsCC > where p is a prime and rtspp and rtsCC are p-adic and complex roots of the defining polynomial sorted according to a Galois-equivariant bijection. This boils down to determine the restriction of an embedding \bar Qp into CC.

intrinsic pAdicPosCMType(AVh::IsogenyClassFq : precpAdic := 30, precCC := 30 ) -> AlgEtQCMType
{Given an ordinary isogeny class AVh, it computes a AlgEtQCMType of the Algebra determined by the Frobenius of AVh such that the Frobenius has positive p-adic valuation according to some embedding of \barQp in C. The varargs precpAdic and precCC specify (minimum) output padic and complex precision.}
    if not assigned AVh`pAdicPosCMType then
        require IsOrdinary(AVh) : "implemented only for ordinary isogeny classes";
        h:=WeilPolynomial(AVh);
        p:=CharacteristicFiniteField(AVh);
        rtspp,rtsCC:=pAdicToComplexRoots(PolynomialRing(Rationals())!h,p : precpAdic := precpAdic, precCC:=precCC ); //from paddictocc.m. works only for ordinary
        // rtspp and rtsCC are the padic and CC roots of h, sorted G-eqivariantly.
        A:=Algebra(ZFVOrder(AVh));
        homs:=HomsToC(A : Precision:=precCC );
        FA:=PrimitiveElement(A);
        homs_FA:=[Parent(rtsCC[1])!h(FA) : h in homs ];
        cmtype_homs:=[ ];
        for ir in [1..#homs_FA] do
            r:=homs_FA[ir];
            assert exists(ind){ irCC : irCC in [1..#rtsCC] | Abs(r-rtsCC[irCC]) lt 10^(2-precCC) };
            if Valuation(rtspp[ind]) gt 0 then
                Append(~cmtype_homs,homs[ir]);
            end if;
        end for;
        assert #cmtype_homs eq (Degree(h) div 2);
        // creation AlgEtQCMType 
        PHI:=CMType(cmtype_homs);
        // if AllCMTypes has already been computed take PHI from there.
        if assigned AVh`AllCMTypes then
            PHI_old:=[ cm : cm in AllCMTypes(AVh) | PHI eq cm ]; 
            assert #PHI_old eq 1; //sanity check
            PHI:=PHI_old[1];
        end if;
        if not assigned PHI`pAdicData then
            PHI`pAdicData:=[< p, rtspp, rtsCC >];
        else
            assert not exists{ data : data in PHI`pAdicData | data[1] eq p }; //to avoid computing different p-adic data for the same p.
            Append(~PHI`pAdicData,< p, rtspp, rtsCC >);
        end if;
        AVh`pAdicPosCMType:=PHI;
    end if;
    return AVh`pAdicPosCMType;
end intrinsic;
