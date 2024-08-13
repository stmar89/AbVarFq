/* vim: set syntax=magma :*/

freeze;


/////////////////////////////////////////////////////
// Period matrices.
// // Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
/////////////////////////////////////////////////////

/* REFERENCES:
Example CrvHyp_Find_CM_Curve (H131E48) on the Magma Handbook
*/

intrinsic PeriodMatrix(pol::HomAbelianVarietyFq , PHI::AlgAssCMType ) -> AlgMatElt,AlgMatElt
{ Given a polarizattion of and abelian variety over a finite field it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
    AV:=Domain(pol);
    require IsPolarization(pol,PHI) : "the input is not a polarization for the given cm-type";
    A:=UniverseAlgebra(AV);
	cc:=ComplexConjugate;
    zb:=DeligneModuleZBasis(AV);
	N:=#zb;
    phi:=Homs(PHI);
	prec:=Precision(Codomain(phi[1]));
    x0:=MapOnUniverseAlgebras(pol)(1);
	E := Matrix(Integers(),N,N,[Trace(x0*cc(a)*b) : b in zb, a in zb]); // added sign
	D, C := FrobeniusFormAlternating(E);
	newb := ElementToSequence(Matrix(A,C)*Matrix(A,N,1,zb));
	N:=N div 2;
	bigPM := Matrix(Codomain(phi[1]),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
	smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
	test_symm:=forall{<i,j> : i,j in [1..N] | Abs(smallPM[i,j]-smallPM[j,i]) lt 10^(-(prec div 2)) };
	im_smallPM:=Matrix([[Im(x) : x in Eltseq(r)] :r in Rows(smallPM)]);
	test_pos_def:=forall{e : e in Eigenvalues(im_smallPM) | e[1] gt 0 };
	require test_symm and test_pos_def : "Precision issue. Increase the precision of the given cm-type";
	return bigPM,smallPM;     
end intrinsic;

/////////////////////////////////////////////////////
// OLD functions. Kept for retro-compatibility
/////////////////////////////////////////////////////

intrinsic PeriodMatrix(I::AlgAssVOrdIdl,x0::AlgAssElt,phi::SeqEnum) -> AlgMatElt,AlgMatElt
{ Given an abelian variety I over a finite field and a principal polarization x0 computed wrt the CM-type phi, it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
	A:=Algebra(I);
	cc:=ComplexConjugate;
	zb:=ZBasis(I);
	N:=#zb;
	prec:=Precision(Codomain(phi[1]));
	E := Matrix(Integers(),N,N,[Trace(x0*cc(a)*b) : b in zb, a in zb]); // added sign
	D, C := FrobeniusFormAlternating(E);
	newb := ElementToSequence(Matrix(A,C)*Matrix(A,N,1,zb));
	N:=N div 2;
	bigPM := Matrix(Codomain(phi[1]),N,2*N,&cat[[F(b) : b in newb] : F in phi]);
	smallPM := Submatrix(bigPM,1,N+1,N,N)^-1*Submatrix(bigPM,1,1,N,N);
	test_symm:=forall{<i,j> : i,j in [1..N] | Abs(smallPM[i,j]-smallPM[j,i]) lt 10^(-(prec div 2)) };
	im_smallPM:=Matrix([[Im(x) : x in Eltseq(r)] :r in Rows(smallPM)]);
	test_pos_def:=forall{e : e in Eigenvalues(im_smallPM) | e[1] gt 0 };
	require test_symm and test_pos_def : "Precision issue. Increase the precision of the given cm-type";
	return bigPM,smallPM;     
end intrinsic;


/*
// TEST

    AttachSpec("~/packages_github/AbVarFq/packages.spec");
    _<x>:=PolynomialRing(Integers());
    h:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    AVh:=IsogenyClass(h);
    iso:=ComputeIsomorphismClasses(AVh);
    PHI:=pAdicPosCMType(AVh);
    for A in iso do
        A;
        test,princ_pols:=IsPrincipallyPolarized(A,PHI);
        for pol in princ_pols do
            assert IsPolarization(pol,PHI);
            go:=false;
            repeat
                try 
                    PeriodMatrix(pol,PHI);
                    go:=true;
                catch e
                    prec0:=Precision(PHI);
                    ChangePrecision(~PHI,2*prec0);
                    go:=false;
                end try;
            until go;
        end for;
    end for;


*/
