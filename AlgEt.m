freeze;

/////////////////////////////////////////////////////
// Functions for ideals and order in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose AlgEt, 1;

/*TODO:
-IsFiniteEtale is wrong!!! it does not recognize the base ring, on the other hand, when I define an AssociativeAlgebra, I set the test to be true, so it is sort of harmless.
*/


declare type AlgEt[AlgEtElt]: AlgAss;

//TODO

declare attributes AlgAss : NumberFields;
declare attributes AlgAss : isFiniteEtale;
declare attributes AlgAss : DefiningPolynomial;


intrinsic HomsToC(A::AlgAss : Precision:=30)->SeqEnum[Map]
{returns Hom(A,\C) as a sequence of maps. The precision of \C is given by the optional parameter "Precision". Default value is 30}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    assert IsSquarefree(DefiningPolynomial(A));
    CC:=ComplexField(Precision);
    images:=function(x)
        return &cat[[CC ! z : z in Conjugates(y : Precision:=Precision)] :y in Components(x)];
    end function;
    maps:=< map< A -> CC | x:-> images(x)[k] > : k in [1..Degree(A)] >;
    f:=&*[DefiningPolynomial(L[1]) : L in A`NumberFields];
    assert &and [ Abs(Evaluate(f,g(PrimitiveElement(A)))) lt 10^-10 : g in maps]; //the precision here is quite arbitrary...
    return maps;
end intrinsic;

intrinsic OrthogonalIdempotents(A::AlgAss)->SeqEnum
{returns a sequence containing the orthogonal ideampotents of the algebra, that is the image of the units of the number fields the algebra is product of}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    return [L[2](One(L[1])) : L in A`NumberFields ];
end intrinsic;

intrinsic AssociativeAlgebra(f::RngUPolElt) -> AlgAss
{given a integer polynomial f generates the Associative algebra over Q given by the factors of f with multiplicity}
  f_fac:=Factorization(f);
  num_fields:=[NumberField(g[1] : DoLinearExtension := true) : j in [1..g[2]] , g in f_fac];
  A:=AssociativeAlgebra(num_fields);
  A`DefiningPolynomial:=f;
  return A;
end intrinsic;

intrinsic AssociativeAlgebra(S::SeqEnum[FldNum]) -> AlgAss
{given given a sequence of number fields, it returns the associative algebra given by the product of the number field}
    QQ:=RANF_protected;
    num_fields:=S;
    deg:=&+[Degree(Ai): Ai in S];

    // let's build A = \prod A_i
    A_matrix:=ZeroMatrix(QQ,deg,deg^2);
    for i in [1..#num_fields] do
        deg_fi:=Degree(num_fields[i]);
        if i eq 1 then
            deg_prev:=0;
        else
            deg_prev:=&+[Degree(num_fields[j]) : j in [1..(i-1)]];
        end if;
        if i eq #num_fields then
            deg_next:=0;
        else
            deg_next:=&+[Degree(num_fields[j]) : j in [(i+1)..(#num_fields)]];
        end if;
        Ai:=num_fields[i];
        mult_table:=MultiplicationTable(EquationOrder(DefiningPolynomial(Ai))); // the table has to be defined via DefiningPolynomial to avoid an issue with SplittingAlgebra(AssociativeAlgebra(x^4+4*x^3+6*x^2+44*x+121));
        for k in [1..#mult_table] do
            InsertBlock(~A_matrix, ChangeRing(mult_table[k],QQ) , deg_prev+1, deg_prev*deg+deg*(k-1)+deg_prev+1);
        end for;
    end for;
    A:=AssociativeAlgebra<QQ,deg | &cat(RowSequence(A_matrix))>;
    A`NumberFields:=[**];
    //let's build the maps from the number fields to K
    deg_prev:=0;
    for L in num_fields do
        Lass,LToLass:=Algebra(L,QQ);
        LassToA:=hom<Lass -> A | [A.j : j in [deg_prev+1..deg_prev+Degree(L)]]>;
        deg_prev:=deg_prev+Degree(L);
        Append(~A`NumberFields, <L,LToLass * LassToA>);
    end for;
    A`isFiniteEtale:=true;
    return A;
end intrinsic;

intrinsic PrimitiveElement(A::AlgAss) -> AlgAssElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    assert IsSquarefree(DefiningPolynomial(A));
    return &+[L[2](PrimitiveElement(L[1])) : L in A`NumberFields];
end intrinsic;

intrinsic DefiningPolynomial(A::AlgAss) -> RngUPolElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    if not assigned A`DefiningPolynomial then
        A`DefiningPolynomial:=&*[DefiningPolynomial(L[1]) : L in A`NumberFields];
    end if;
    return A`DefiningPolynomial;
end intrinsic;

intrinsic Components(x::AlgAssElt) -> SeqEnum
{returns the components of the element as in the product of number fields}
    A:=Parent(x);
    require IsFiniteEtale(Parent(x)): "the algebra of definition must be finite and etale over Q";
    idem:=OrthogonalIdempotents(A);
    x_asProd:=[**];
    for i in [1..#A`NumberFields] do
        L:=A`NumberFields[i];
        x_L:=(x*idem[i])@@L[2];
        Append(~x_asProd,x_L);
    end for;
    return x_asProd;
end intrinsic;

intrinsic Idempotents(A::AlgAss)->SeqEnum
{returns a sequence containing the ideampotents of the algebra, zero included}
    ort_idem:=OrthogonalIdempotents(A);
    cc:=CartesianProduct([[A!0,oi] : oi in ort_idem]);
    idem:=[&+([cj : cj in c]) : c in cc];
    return idem;
end intrinsic;
