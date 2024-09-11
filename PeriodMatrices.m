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
// Period matrices.
/////////////////////////////////////////////////////

/* REFERENCES:
Example CrvHyp_Find_CM_Curve (H131E48) on the Magma Handbook
*/

intrinsic PeriodMatrix(pol::HomAbelianVarietyFq , PHI::AlgEtQCMType : CheckOrdinary:=true ) -> AlgMatElt,AlgMatElt
{Given a polarizattion of and abelian variety over a finite field it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
    AV:=Domain(pol);
    require IsSquarefree(IsogenyClass(AV)) : "implemented only for ordinary squarefree isogeny classes";
    if CheckOrdinary then
        require IsOrdinary(AV) : "the input needs to be ordinary.";
    end if;
    require IsPolarization(pol,PHI) : "the input is not a polarization for the given cm-type";
    A:=Algebra(ZFVOrder(AV));
	cc:=ComplexConjugate;
    zb:=ZBasis(DeligneModule(AV));
	N:=#zb;
    phi:=Homs(PHI);
	prec:=Precision(Codomain(phi[1]));
    x0:=MapOnDeligneAlgebras(pol)(1);

	E := Matrix(Integers(),N,N,[Trace(x0*cc(a)*b) : b in zb, a in zb]); // added sign
	D, C := FrobeniusFormAlternating(E);
    C:=[A!x:x in Eltseq(C)];
	newb := Columns(Matrix(N,N,C)*Matrix(N,1,zb))[1];
	N:=N div 2;
	bigPM := Matrix(Codomain(phi[1]),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
	smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
	test_symm:=forall{<i,j> : i,j in [1..N] | Abs(smallPM[i,j]-smallPM[j,i]) lt 10^(-(prec div 2)) };
	im_smallPM:=Matrix([[Im(x) : x in Eltseq(r)] :r in Rows(smallPM)]);
	test_pos_def:=forall{e : e in Eigenvalues(im_smallPM) | e[1] gt 0 };
	require test_symm and test_pos_def : "Precision issue. Increase the precision of the given cm-type";
	return bigPM,smallPM;     
end intrinsic;

