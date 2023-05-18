/* vim: set syntax=magma :*/

//declare attributes AlgEtQOrd : ; // should I cache it?

intrinsic IsProduct(S::AlgEtQOrd)->BoolElt,SeqEnum[AlgEtQElt]
{Returns whether S is a product of orders S1 x .. x Sn for orders Si in some factor algebra of Algebra(S), together with the idempotents ei of Algebra of S such that Si=ei*S, and the product_partition as a list of lists of integers, giving which components of the etale algebra are clustered together. If no splitting will be [[1,2,...,m]], while if completely split will be [[1],[2],...,[m]]. Here m is the number of components of the etale algebra, and the components are ordered by sorting their defining polynomials.}
    A:=Algebra(S);
    idem:=[ i : i in Idempotents(A) | i in S]; // idempotents in S
    output:=[PowerStructure(AlgEtQElt)|];
    if Seqset(idem) eq { One(A), Zero(A) } then
        return false,output,[[i : i in [1..#Components(A)]]];
    end if;

    test,D:=IsPowerOf(#idem,2);
    assert test;
    F2:=GF(2);
    V:=VectorSpace(F2,#Components(A));
    idem_inV:=[ V![ c eq 1 select F2!1 else F2!0 : c in Components(i) ] : i in idem ];
    sub:=sub<V| idem_inV >;
    arr:=AssociativeArray();
    for j in [1..#idem] do
        i:=idem[j];
        v:=idem_inV[j];
        n:=#[ x : x in Eltseq(v) | x eq 1 ];
        if not IsDefined(arr,n) then
            arr[n]:=[];
        end if;
        Append(~arr[n],j);
    end for;
    max:=Max(Keys(arr));
    W:=sub<V|>;
    n:=1;
    while Dimension(W) lt D and n lt max do
        if IsDefined(arr,n) then
            for j in arr[n] do
                v:=idem_inV[j];
                if not v in W then 
                    Append(~output,idem[j]);
                    W:=sub<V| W,v>;
                    if Dimension(W) eq D then
                        break;
                    end if;
                end if;
            end for;
            printf ".";
        end if;
        n+:=1;
    end while;
    assert #output gt 1;
    assert OneIdeal(S) eq Ideal(S , [ z*g : z in ZBasis(S) , g in output ]);

    // LMFDB
    // we now compute the product partition
    prod_part:=[];
    nfs:=[ Coefficients(DefiningPolynomial(K)) : K in Components(A) ];
    require #nfs eq #Seqset(nfs) : "We need the number fields forming the etale algebra to be different";
    ind:=[1..#nfs];
    ParallelSort(~nfs,~ind);
    for id in output do
        comp:=Components(id);
        comp:=[ comp[ind[i]] eq 1 select 1 else 0 : i in [1..#ind] ]; //sorted
        Append(~prod_part,[ i : i in [1..#ind] | comp[i] eq 1 ]); 
    end for;
    return true, output, prod_part; 
end intrinsic;

/*
    SetDebugOnError(true);
    AttachSpec("~/packages_github/AlgEt/spec");
    Attach("~/packages_github/AbVarFq/LMFDB/IsProduct.m");
    _<x>:=PolynomialRing(Integers());
    f:=(x^2-2)*(x^2-3)*(x^2-5);
    A:=EtaleAlgebra(f);
    E:=EquationOrder(A);
    assert not IsProduct(E);
    O:=MaximalOrder(A);
    assert IsProduct(O);
    oo:=FindOverOrders(E);
    for S in oo do
        IsProduct(S);
    end for;

    // extensive test
    fld := "~/266_wk_icm_rec/labelling/parallel/";
    fld_wk := fld cat "wk_classes/";
    fld_out := fld cat "output/";
    issue_file:=fld cat "issue_wkicm.txt";
    "Loading schemas";
    files:=Split(Pipe("ls " cat fld_out,""));
    "..Done";
  
    Attach("~/packages_github/AbVarFq/LMFDB/labelling_wk_classes.m");

    for ifile->file in files do
        schema:=Read(fld_out cat file);
        R:=LoadSchemaWKClasses(schema);
        assert #WKICM(R) eq #Split(schema);
        oo:=OverOrders(R);
        for S in oo do
            _:=IsProduct(S);
        end for;
        printf ".";
    end for;

*/
