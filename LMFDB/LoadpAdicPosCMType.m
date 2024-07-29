/* vim: set syntax=magma :*/

intrinsic LoadpAdicPosCMType(basis::SeqEnum[AlgEtQElt], str::MonStgElt)->AlgEtQCMType
{Given a basis of commutative endomorphism algebra of and ordinary abelian variety and a string of the form \{x1,...,xn\} where xi are the integr coefficients of a totally imaginary element b with respect to the given basiis, it populates the attribute A`pAdicPosCMType with the correspoding CMType, and returns the CMType.}
    require str[1] eq "{" and str[#str] eq "}" : "the string is not of the right format";
    str:=str[2..#str-1];
    str:=[ StringToInteger(s) : s in Split(str,",") ];
    A:=Algebra(basis[1]);
    b:=SumOfProducts(str,basis);
    assert b eq -ComplexConjugate(b);
    PHI:=CMType(b);
    A`pAdicPosCMType:=PHI;
    return pAdicPosCMType(A);
end intrinsic;


/*
    // to be run on lovelace
    AttachSpec("~/packages_github/AlgEt/spec");
    AttachSpec("~/packages_github/AbVarFq/LMFDB/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/LoadpAdicPosCMType.m");
    load "~/999_LMFDB_isogeny_label_functions.txt";
    
    fld_output:="/scratch/abvar/pAdicPos/output_parallel1/";
    files:=Split(Pipe("ls " cat fld_output,""));

    _<x>:=PolynomialRing(Integers());
   
    for file in files do
        str:=Read(fld_output cat file);
        label,str:=Explode(Split(str,":"));
        g,q,f:=LabelToPoly(label);
        A:=EtaleAlgebra(f);
        basis:=ZFVBasis(A);
        PHI:=LoadpAdicPosCMType(basis,str);
        printf ".";
    end for;


*/
