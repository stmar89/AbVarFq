freeze;

/////////////////////////////////////////////////////
// Functions for ideals and order in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose et_algebras, 1;

/*TODO:

*/

declare type AlgEt[AlgEtElt];

declare attributes AlgEt : DefiningPolynomial, 
                           ass_algebra, 
                           NumberFields;
declare attributes AlgEtElt: Algebra,
                             AlgAssElt;

//------------
//
// Basics
//
//------------

intrinsic Print(A::AlgEt)
{returns the underlying algebra of A}
  printf"Etale Algebra given by %o", AssAlgebra(A);
end intrinsic;

intrinsic Print(x::AlgEtElt)
{returns the underlying algebra of A}
  printf"%o", x`AlgAssElt;
end intrinsic;

intrinsic IsCoercible(A::AlgEt, x::.) -> BoolElt, .
{Return whether x is coercible into A and the result if so}
    if Parent(x) cmpeq A then
        return true,x;
    elif Parent(x) cmpeq AssAlgebra(A) then
        x1:=New(AlgEtElt);
        x1`Algebra:=A;
        x1`AlgAssElt:=x;
        return true,x1;
    elif Type(x) eq FldNumElt or Type(x) eq RngIntElt or Type(x) eq FldRatElt then
        x1:=New(AlgEtElt);
        x1`Algebra:=A;
        x1`AlgAssElt:=AssAlgebra(A) ! x;
        return true, x1;
    else 
      return false,_;
    end if;
end intrinsic;

//------------
//
// Coercion
//
//------------

intrinsic '!'(A::AlgEt,x::AlgAssElt) -> AlgEtElt
{ given an etale algebra A and an element x of the underlying Associtive Algebra coerces x in A}
    bool,x:=IsCoercible(A,x);
    error if not bool, "the element cannot be coerced in the algebra";
    return x;
end intrinsic;

intrinsic '!'(A::AlgAss,x::AlgEtElt) -> AlgAssElt
{ given an associative algebra A and an element x of an etale algebra built on A, coerces the element in A }
    if AssociativeAlgebra(Parent(x)) cmpeq A then
        return x`AlgAssElt;
    else
        error "the element cannot be coerced";
    end if;
end intrinsic;

//------------
//
// Access attributes
//
//------------

intrinsic AssociativeAlgebra(A::AlgEt) -> AlgAss
{returns the underlying associative algebra of A}
  return A`ass_algebra;
end intrinsic;

intrinsic AssAlgebra(A::AlgEt) -> AlgAss
{returns the underlying associative algebra of A}
  return AssociativeAlgebra(A);
end intrinsic;

intrinsic AssElt(x::AlgEtElt) -> AlgAssElt
{returns the underlying element of the associative algebra}
  return x`AlgAssElt;
end intrinsic;

intrinsic Parent(x::AlgEtElt) -> AlgEt
{returns the underlying etale algebra of A}
  return x`Algebra;
end intrinsic;

intrinsic Algebra(x::AlgEtElt) -> AlgEt
{returns the underlying etale algebra of A}
  return x`Algebra;
end intrinsic;

intrinsic '.'(A::AlgEt,i::RngIntElt) -> AlgEtElt
{A.i returns the ith generator of the Algebra A}
   alg:=AssociativeAlgebra(A);
   y:=New(AlgEtElt);
   y`AlgAssElt:=alg.i;
   y`Algebra:=A;
   return y;
end intrinsic;

//------------
//
// Operations
//
//------------

intrinsic '+'(x1::AlgEtElt,x2::AlgEtElt) -> AlgEtElt
{x1+x2}
   require Parent(x1) cmpeq Parent(x2): "the elements must be defined over the same algebra";
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=(x1`AlgAssElt)+(x2`AlgAssElt);
   x3`Algebra:=Parent(x1);
   return x3;
end intrinsic;

intrinsic '+'(x1::.,x2::AlgEtElt) -> AlgEtElt
{x1+x2}
   bool,x1:=IsCoercible(Algebra(x2),x1);
   if bool then
        return x1 + x2;
   else
        error "x1 not coercible";
   end if;
end intrinsic;

intrinsic '+'(x1::AlgEtElt,x2::.) -> AlgEtElt
{x1+x2}
   bool,x2:=IsCoercible(Algebra(x1),x2);
   if bool then
        return x1 + x2;
   else
        error "x2 not coercible";
   end if;
end intrinsic;

intrinsic '-'(x::AlgEtElt) -> AlgEtElt
{-x}
   y:=New(AlgEtElt);
   y`AlgAssElt:=-(x`AlgAssElt);
   y`Algebra:=Parent(x);
   return y;
end intrinsic;

intrinsic '-'(x1::AlgEtElt,x2::AlgEtElt) -> AlgEtElt
{x1-x2}
   require Parent(x1) cmpeq Parent(x2): "the elements must be defined over the same algebra";
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=(x1`AlgAssElt)-(x2`AlgAssElt);
   x3`Algebra:=Parent(x1);
   return x3;
end intrinsic;

intrinsic '-'(x1::.,x2::AlgEtElt) -> AlgEtElt
{x1-x2}
   bool,x1:=IsCoercible(Algebra(x2),x1);
   if bool then
        return x1 - x2;
   else
        error "x1 not coercible";
   end if;
end intrinsic;

intrinsic '-'(x1::AlgEtElt,x2::.) -> AlgEtElt
{x1-x2}
   bool,x2:=IsCoercible(Algebra(x1),x2);
   if bool then
        return x1 - x2;
   else
        error "x2 not coercible";
   end if;
end intrinsic;

intrinsic '*'(x1::AlgEtElt,x2::AlgEtElt) -> AlgEtElt
{x1*x2}
   require Parent(x1) cmpeq Parent(x2): "the elements must be defined over the same algebra";
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=(x1`AlgAssElt)*(x2`AlgAssElt);
   x3`Algebra:=Parent(x1);
   return x3;
end intrinsic;

intrinsic '*'(x1::.,x2::AlgEtElt) -> AlgEtElt
{x1*x2}
   bool,x1:=IsCoercible(Algebra(x2),x1);
   if bool then
        return x1 * x2;
   else
        error "x1 not coercible";
   end if;
end intrinsic;

intrinsic '*'(x1::AlgEtElt,x2::.) -> AlgEtElt
{x1*x2}
   bool,x2:=IsCoercible(Algebra(x1),x2);
   if bool then
        return x1 * x2;
   else
        error "x2 not coercible";
   end if;
end intrinsic;

intrinsic '/'(x1::AlgEtElt,x2::AlgEtElt) -> AlgEtElt
{x1/x2}
   require Parent(x1) cmpeq Parent(x2): "the elements must be defined over the same algebra";
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=(x1`AlgAssElt)*(x2`AlgAssElt)^-1;
   x3`Algebra:=Parent(x1);
   return x3;
end intrinsic;

intrinsic '/'(x1::.,x2::AlgEtElt) -> AlgEtElt
{x1/x2}
   bool,x1:=IsCoercible(Algebra(x2),x1);
   if bool then
        return x1 / x2;
   else
        error "x1 not coercible";
   end if;
end intrinsic;

intrinsic '/'(x1::AlgEtElt,x2::.) -> AlgEtElt
{x1/x2}
   bool,x2:=IsCoercible(Algebra(x1),x2);
   if bool then
        return x1 / x2;
   else
        error "x2 not coercible";
   end if;
end intrinsic;

intrinsic '^'(x1::AlgEtElt,n::RngIntElt) -> AlgEtElt
{x1^n}   
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=(x1`AlgAssElt)^n;
   x3`Algebra:=Parent(x1);
   return x3;
end intrinsic;

intrinsic One(A::AlgEt) -> AlgEtElt
{the unit of A}   
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=One(AssociativeAlgebra(A));
   x3`Algebra:=A;
   return x3;
end intrinsic;

intrinsic Zero(A::AlgEt) -> AlgEtElt
{the unit of A}   
   x3:=New(AlgEtElt);
   x3`AlgAssElt:=0*A.1;
   x3`Algebra:=A;
   return x3;
end intrinsic;

intrinsic 'eq'(x1::AlgEtElt,x2::AlgEtElt) -> BoolElt
{x1 eq x2}
   require Parent(x1) cmpeq Parent(x2): "the elements must be defined over the same algebra";
   return (x1`AlgAssElt) eq (x2`AlgAssElt);
end intrinsic;

intrinsic 'eq'(x1::.,x2::AlgEtElt) -> BoolElt
{x1 eq x2}
   bool,x1:=IsCoercible(Algebra(x2),x1);
   if bool then
        return x1 eq x2;
   else
        error "x1 not coercible";
   end if;
end intrinsic;

intrinsic 'eq'(x1::AlgEtElt,x2::.) -> BoolElt
{x1 eq x2}
   bool,x2:=IsCoercible(Algebra(x1),x2);
   if bool then
        return x1 eq x2;
   else
        error "x2 not coercible";
   end if;
end intrinsic;

intrinsic 'eq'(A1::AlgEt,A2::AlgEt) -> BoolElt
{A1 eq A2}
   return A1 cmpeq A2;
end intrinsic;

intrinsic Eltseq(x1::AlgEtElt) -> SeqEnum
{rational coordinates of x1}    
   return Eltseq(x1`AlgAssElt);
end intrinsic;

intrinsic HomsToC(A::AlgEt : Precision:=30)->SeqEnum[Map]
{returns Hom(A,\C) as a sequence of maps. The precision of \C is given by the optional parameter "Precision". Default value is 30}
    CC:=ComplexField(Precision);
    images:=function(x)
        return &cat[[CC ! z : z in Conjugates(y : Precision:=Precision)] :y in Components(x)];
    end function;
    maps:=< map< A -> CC | x:-> images(x)[k] > : k in [1..Degree(A)] >;
    f:=&*[DefiningPolynomial(L[1]) : L in A`NumberFields];
    assert &and [ Abs(Evaluate(f,g(PrimitiveElement(A)))) lt 10^-10 : g in maps]; //the precision here is quite arbitrary...
    return maps;
end intrinsic;

intrinsic OrthogonalIdempotents(A::AlgEt)->SeqEnum
{returns a sequence containing the orthogonal ideampotents of the algebra, that is the image of the units of the number fields the algebra is product of}
    return [L[2](One(L[1])) : L in A`NumberFields ];
end intrinsic;

intrinsic Dimension(A::AlgEt)->RngInt
{Dimenison of A}    
    return Dimension(AssociativeAlgebra(A));
end intrinsic;

intrinsic Degree(A::AlgEt)->RngInt
{Dimenison of A}    
    return Degree(AssociativeAlgebra(A));
end intrinsic;

intrinsic EtaleAlgebra(f::RngUPolElt) -> AlgEt
{given a integer polynomial f generates the Associative algebra over Q given by the factors of f with multiplicity}
  require IsSquarefree(f) : "the polynomial must be squaree";
  f_fac:=Factorization(f);
  num_fields:=[NumberField(g[1] : DoLinearExtension := true) : j in [1..g[2]] , g in f_fac];
  A:=EtaleAlgebra(num_fields);
  A`DefiningPolynomial:=f;
  return A;
end intrinsic;

intrinsic EtaleAlgebra(S::SeqEnum[FldNum]) -> AlgEt
{given given a sequence of number fields, it returns the associative algebra given by the product of the number field}
    QQ:=RationalsAsNumberField();
    num_fields:=S;
    deg:=&+[Degree(Ai): Ai in S];
    A:=New(AlgEt);
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
    A`ass_algebra:=AssociativeAlgebra<QQ,deg | &cat(RowSequence(A_matrix))>;
    A`NumberFields:=[**];
    //let's build the maps from the number fields to A
    deg_prev:=0;
    for L in num_fields do
        Lass,LToLass:=Algebra(L,QQ);
        //LassToA:=hom<Lass -> A | [(A.j) : j in [deg_prev+1..deg_prev+Degree(L)]]>;
        LassToAss:=hom<Lass -> AssociativeAlgebra(A) | [(A.j)`AlgAssElt : j in [deg_prev+1..deg_prev+Degree(L)]]>;
        AsstoA:=map<AssociativeAlgebra(A) -> A | x:->&+[Eltseq(x)[j]*(A.j) : j in [1..Dimension(A)]],
                                     y:->y`AlgAssElt
                          >;
        deg_prev:=deg_prev+Degree(L);
        Append(~A`NumberFields, <L,LToLass * LassToAss * AsstoA>);
    end for;
    return A;
end intrinsic;

intrinsic PrimitiveElement(A::AlgEt) -> AlgEtElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    assert IsSquarefree(DefiningPolynomial(A));
    return &+[L[2](PrimitiveElement(L[1])) : L in A`NumberFields];
end intrinsic;

intrinsic DefiningPolynomial(A::AlgEt) -> RngUPolElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    if not assigned A`DefiningPolynomial then
        A`DefiningPolynomial:=&*[DefiningPolynomial(L[1]) : L in A`NumberFields];
    end if;
    return A`DefiningPolynomial;
end intrinsic;

intrinsic Components(x::AlgEtElt) -> SeqEnum
{returns the components of the element as in the product of number fields}
    A:=Parent(x);
    idem:=OrthogonalIdempotents(A);
    x_asProd:=[**];
    for i in [1..#A`NumberFields] do
        L:=A`NumberFields[i];
        x_L:=(x*idem[i])@@L[2];
        Append(~x_asProd,x_L);
    end for;
    return x_asProd;
end intrinsic;

intrinsic Idempotents(A::AlgEt)->SeqEnum
{returns a sequence containing the ideampotents of the algebra, zero included}
    ort_idem:=OrthogonalIdempotents(A);
    cc:=CartesianProduct([[A!0,oi] : oi in ort_idem]);
    idem:=[&+([cj : cj in c]) : c in cc];
    return idem;
end intrinsic;

intrinsic Coordinates(seq::SeqEnum[AlgEtElt],basis::SeqEnum[AlgEtElt]) -> SeqEnum
{ the coordinates of the sequence S of elements in an etale algebra A, relative to the given basis of A over the rationals. }
    vprintf et_algebras: "Coordinates";
    require Universe(seq) eq Universe(basis) : "the sequences must be defined over the same algebra";
    A:=AssAlgebra(Universe(seq));
    seq:=[A ! x : x in seq ];
    basis:=[A ! x : x in basis ];
    coord:=Coordinates(seq,basis);
    return coord;
end intrinsic;

intrinsic IsZeroDivisor(x::AlgEtElt) -> BoolElt
{returns if the element x is a zero divisor}
    return exists{c : c in Components(x)|c eq Zero(Parent(c))};
end intrinsic;

intrinsic IsZeroDivisor2(x::AlgEtElt) -> BoolElt
{returns if the element x is a zero divisor}
    return IsZeroDivisor(x);
end intrinsic;

intrinsic Evaluate(p::RngUPolElt, y::AlgEtElt) -> AlgEtElt
{evaluates a polynomial at y}
    evl:=Evaluate(p,AssElt(y));
    return Algebra(y)!evl;
end intrinsic;

/* TEST
Attach("~/packages_github/AbVarFq/AlgEt.m");
_<x>:=PolynomialRing(Integers());
f:=(x^8+16)*(x^8+81);
A:=EtaleAlgebra(f);
[A.1,A.2];
Components(A.1);
Components(A!1);
IsZeroDivisor(A.1);
IsZeroDivisor(A!1);


*/
