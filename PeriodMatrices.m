/////////////////////////////////////////////////////
// Period matrices.
// // Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/

// http://staff.math.su.se/stefanom/
/////////////////////////////////////////////////////

/* LIST of functions:
intrinsic PeriodMatrix(I::AlgAssVOrdIdl,x0::AlgAssElt,phi::SeqEnum : prec:=10) -> AlgMatElt
*/ 

/* REFERENCES:
Example CrvHyp_Find_CM_Curve (H131E48) on the Magma Handbook
*/

intrinsic PeriodMatrix(I::AlgAssVOrdIdl,x0::AlgAssElt,phi::SeqEnum) -> AlgMatElt
{ Given an abelian variety I over a finite field and a principal polarization x0 computed wrt the CM-type phi, it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
    A:=Algebra(I);
    cc:=ComplexConjugate;
    zb:=ZBasis(I);
    N:=#zb;
    E := Matrix(Integers(),N,N,[Trace(cc(x0*a)*b) : b in zb, a in zb]);
    D, C := FrobeniusFormAlternating(E);
    newb := ElementToSequence(Matrix(A,C)*Matrix(A,N,1,zb));
    N:=N div 2;
    bigPM := Matrix(Codomain(phi[1]),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
    smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
    return bigPM,smallPM;     
end intrinsic;
