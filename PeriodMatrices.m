/////////////////////////////////////////////////////
// Period matrices.
// Stefano Marseglia, Stockholm University, stefanom@math.su.se
// http://staff.math.su.se/stefanom/
/////////////////////////////////////////////////////

/* DESCRIPTION
some intrinsics tp compute period matrices of principally polarized abelian vareities

this is a preliminary version, which should be checked
*/

/* LIST of functions:
intrinsic 

*/ 

/* REFERENCES:
Example CrvHyp_Find_CM_Curve (H131E48) on the Magma Handbook
*/

/* TODO:

*/


intrinsic PeriodMatrix(I::AlgAssVOrdIdl,x0::AlgAssElt,phi::SeqEnum : prec:=10) -> AlgMatElt
{ given an abelian variety I over a finite field and a principal polarization x0 computed wrt the CM-type phi, it returns the corresponding big and small period matrices }
    A:=Algebra(I);
    cc:=ComplexConjugate;
    zb:=ZBasis(I);
    N:=#zb;
    E := Matrix(Integers(),N,N,[Trace(cc(x0*a)*b) : b in zb, a in zb]);
    D, C := FrobeniusFormAlternating(E);
    newb := ElementToSequence(Matrix(A,C)*Matrix(A,N,1,zb));
    N:=N div 2;
    bigPM := Matrix(ComplexField(prec),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
    smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
    return bigPM,smallPM;     
end intrinsic;
