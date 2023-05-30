/* vim: set syntax=magma :*/

intrinsic MonogenicGeneratorsOverOrder(S::AlgEtQOrd,R::AlgEtQOrd : limit:=100)->SeqEnum[AlgEtQElt]
{Given order R subset S, returns a sequence of elements x such that S=R[x]. This sequence is produced with a randomized search over 100 candidates. In particular, it is not necessarily complete. If none is found then the empty list is returned. The limit 100 can be modified by setting the vararg "limit".}
    require R subset S : "The orders are not one inside the other.";
    if R eq S then
        return [Zero(Algebra(R))];
    end if;
    Q,q:=Quotient(R!!OneIdeal(S),OneIdeal(R));
    cand:=[];
    limit:=Min(limit,#Q-1);
    while #cand lt limit do
        x:=Random(Q);
        if x ne Zero(Q) then
            Append(~cand,x@@q);
        end if;
    end while;
    zbR:=ZBasis(R);
    cand:=Seqset(cand);
    cand:=[ x : x in cand | Order(zbR cat [x]) eq S ];
    return cand; 
end intrinsic;

intrinsic SmallestMonogenicGeneratorOverZFV(S::AlgEtQOrd,ZFV::AlgEtQOrd: limit:=100)->SeqEnum[AlgEtQElt],SeqEnum[MonStgElt]
{Returns a sequence of minimal monogenic generators of S over ZFV, if any is found, where minimal is with respect to the lenght of the string of printing with respect to the basis V^(g-1),...,V,1,F,...,F^g.}
    A:=Algebra(S);
    F:=PrimitiveElement(A);
    g:=Dimension(A) div 2;
    q:=Truncate(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
    V:=q/F;
    basis:=ZFVBasis(A);
    seq:=MonogenicGeneratorsOverOrder(S,ZFV : limit:=limit);
    if #seq eq 0 then
        return [PowerStructure(AlgEtQElt)|],[PowerStructure(RngIntElt)|],[PowerStructure(SeqEnum)|];
    end if;

    all_str:=[];
    all_len:=[];
    all_coeff:=[ AbsoluteCoordinates([x],basis)[1] : x in seq ];
    ZFV<V,F>:=PolynomialRing(Rationals(),2);
    for ix->x in seq do
        coeff:=all_coeff[ix];
        poly:=coeff[g];
        poly_V:=g gt 1 select &+([ Reverse(coeff[1..g-1])[i]*V^i : i in [1..g-1] ]) else 0;
        poly_F:=&+([coeff[g+1..2*g][i]*F^i : i in [1..g]]);
        poly:=poly + poly_V + poly_F;
        str_x:=Sprintf("%o",poly);
        Append(~all_str,str_x);
        Append(~all_len,#str_x);
    end for;
    min:=Min(all_len);
    elts:=[ seq[i] : i in [1..#seq] | all_len[i] eq min];
    coeffs:=[ all_coeff[i] : i in [1..#seq] | all_len[i] eq min ];
    dens:=[ LCM([ Denominator(c) : c in coeffs[i]]) : i in [1..#elts] ];
    nums:=[ [ dens[i]*c : c in coeffs[i] ] : i in [1..#elts]];
    return elts,dens,nums;
end intrinsic;

/*
    // on diopahntus
    SetDebugOnError(true);
    AttachSpec("~/packages_github/AlgEt/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/MonGenOrd.m");
    _<x>:=PolynomialRing(Integers());
    f:=(x^2-2)*(x^2-3)*(x^2-5);
    A:=EtaleAlgebra(f);
    E:=EquationOrder(A);
    oo:=FindOverOrders(E);
    for S in oo do
        #MonogenicGeneratorsOverOrder(S,E);
    end for;

    // extensive test
    fld := "~/266_wk_icm_rec/labelling/parallel/";
    fld_wk := fld cat "wk_classes/";
    fld_out := fld cat "output/";
    issue_file:=fld cat "issue_wkicm.txt";
    "Loading schemas";
    files:=Reverse(Split(Pipe("ls " cat fld_out,"")));
    "..Done";
  
    SetDebugOnError(true);
    AttachSpec("~/packages_github/AlgEt/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/MonGenOrd.m");
    Attach("~/packages_github/AbVarFq/LMFDB/labelling_wk_classes.m");

    for ifile->file in files do
        schema:=Read(fld_out cat file);
        ZFV:=LoadSchemaWKClasses(schema);
        f:=DefiningPolynomial(Algebra(ZFV));
        if not IsIrreducible(f) and #OverOrders(ZFV) eq 1 then
            assert IsMaximal(ZFV);
            printf "!";
        end if;
        //if IsIrreducible(f) then
        //    printf ".";
        //    oo:=OverOrders(ZFV);
        //    if #oo gt 1 then
        //        for S in oo do
        //            #MonogenicGeneratorsOverOrder(S,ZFV);
        //            SmallestMonogenicGeneratorOverZFV(S,ZFV);
        //        end for;
        //    else
        //        printf "!";
        //    end if;
        //end if;
    end for;

*/
