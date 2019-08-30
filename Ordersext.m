freeze;

/////////////////////////////////////////////////////
// Functions for ideals and order in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

import "usefulfunctions.m": AllPossibilities;
declare verbose Ordersext, 1;

/*TODO:
-compare my IsZeroDivisor2 with the already built-in IsUnit
-IsFiniteEtale is wrong!!! it does not recognize the base ring, on the other hand, when I define an AssociativeAlgebra, I set the test to be true, so it is sort of harmless.
-Put all the "if assigned ??" in dedicated functions
*/

RANF_protected:=RationalsAsNumberField();

declare attributes AlgAss : NumberFields;
declare attributes AlgAss : isFiniteEtale;
declare attributes AlgAss : CMType;
declare attributes AlgAssVOrd : OneIdeal;
declare attributes AlgAssVOrd : Index;
declare attributes AlgAssVOrd : IsProductOfOrders;
//alternative to declare attributes AlgAssVOrdIdl:Index;
AlgAssVOrdIdlData2 := recformat<
  // magma internal, see orders-jv.m
  Jprimes:List, // list of tuples <JJ,b,n> containing output of Jprime
  Index:FldRatElt // to store the index
  >;

intrinsic OneIdeal(S::AlgAssVOrd) -> AlgAssVOrdIdl
{given an S returns ideal<S|One(S)> which will be cached}
  if not assigned S`OneIdeal then
    S`OneIdeal := ideal<S | One(S)>;
  end if;
  return S`OneIdeal;
end intrinsic;

intrinsic PrimesAbove(I::AlgAssVOrdIdl) -> SeqEnum[AlgAssVOrdIdl]
{given an integral S-ideal, returns the sequence of maximal ideals P of S above I}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require IsIntegral(I): "the ideal must be integral";
    S:=Order(I);
    if One(S) in I then
        return [];
    else
        if IsMaximal(S) then
            O:=S;
            IO:=I;
        else
            O:=MaximalOrder(Algebra(I));
            IO:=O!I;
        end if;
        fac:=Factorization(IO);
        primes:= Setseq({ S meet (S!PO[1]) : PO in fac });
        assert2 forall{P : P in primes | I subset P};
        return primes;
    end if;
end intrinsic;

intrinsic IsPrime(I::AlgAssVOrdIdl) -> BoolElt
{given an integral S-ideal, returns if the ideal is a prime fractional ideal of S, that is a maximal S ideal}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require IsIntegral(I): "the ideal must be integral";
    prim:=PrimesAbove(I);
    if #prim eq 1 and I eq prim[1] then
        return true;
    else
        return false;
    end if;
end intrinsic;

intrinsic '!'(T::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{given an S-ideal I and an order T, returns the extension IT as a T-ideal. Note that if T is in S, then IT=I}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    if Order(I) eq T then
        return I;
    else
        return ideal<T|ZBasis(I)>;
    end if;
end intrinsic;

intrinsic MultiplicatorRing(R::AlgAssVOrd) -> AlgAssVOrd
{returns the MultiplicatorRing of an order R, that is R itself}
    return R;
end intrinsic;

intrinsic '/'(a::AlgAssElt,b::AlgAssElt)->AlgAssElt
{ given a and b, a non-zero divisor, it returs a/b}
    require IsFiniteEtale(Parent(a)): "the algebra of definition must be finite and etale over Q";
    require Parent(a) eq Parent(b): "the elements must belong to the same algebra";
    require not IsZeroDivisor2(b): "the denominator must be an invertible element";
    return a*b^-1;
end intrinsic;

intrinsic IsFiniteEtale(A::AlgAss) -> BoolElt
{returns if A is a finite etale algebra over Q, that is a finite product of number fields}
    if not assigned A`isFiniteEtale then
    //it does not recognize the BaseRing!!! the next part is useless
    //t:=BaseRing(A) eq RANF_protected and IsCommutative(A) and IsFinite(Degree(A)) and assigned A`NumberFields;
        A`isFiniteEtale:=assigned A`NumberFields;
    end if;
    return A`isFiniteEtale;
end intrinsic;

intrinsic MinimalInteger(I::AlgAssVOrdIdl) -> RngIntElt
{returns the smallest integer contained in the ideal I}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require IsIntegral(I): "the ideal must be integral";
    coord:=Coordinates([One(Algebra(I))],ZBasis(I))[1];
    min:=LCM([ Denominator(c) : c in Eltseq(coord)]);
    return min;
end intrinsic;

intrinsic ListToSequence(L::List)->SeqEnum
{given a list of elements returns the same sequence}
    return [s : s in L];
end intrinsic;

intrinsic IsZeroDivisor2(x::AlgAssElt) -> BoolElt
{returns if the element x is a zero divisor}
    require IsFiniteEtale(Parent(x)): "the algebra of definition must be finite and etale over Q";
    return exists{c : c in Components(x)|c eq Zero(Parent(c))};
end intrinsic;

intrinsic Random(I::AlgAssVOrdIdl : bound:=3) -> AlgAssElt
{Returns a random (small coefficient) element of I}
    A := Algebra(Order(I));
    B := ZBasis(I);
    return A ! &+[ Random([-bound..bound])*b : b in B];
end intrinsic;

intrinsic CoprimeRepresentative(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> AlgAssElt
{return an element x such that x*I is an integral ideal coprime with J. The first ideal must be invertible and the second should be integral}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require IsIntegral(J) : "the second ideal must be integral";
    S:=Order(I);
    require S eq Order(J): "the ideals must be defined over the same order";
    require IsInvertible(I): "The first ideal must be invertible";
    invI:=ColonIdeal(S,I);
    repeat
        x:=Random(invI);
    until (not IsZeroDivisor2(x) and IsCoprime(x*I,J)); //integrality of x*I is checked in IsCoprime
    return x;
end intrinsic;

intrinsic ChineseRemainderTheorem(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl,a::AlgAssElt,b::AlgAssElt)-> AlgAssElt
{given two coprime ideals I and J of S, two elements a,b in S, finds e such that (e-a) in I and (e-b) in J}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require IsCoprime(I,J) : "the ideals must be coprime";
    S:=Order(I);
    require a in S and b in S:"the elements must lie in order of definition of the ideals";
    require S eq Order(J): "the ideals must be of the same order";
    K:=Algebra(S);
    n:=Degree(K);
    //I need to modify the ZBasis(S) in a way that One(K) is the first element of Zbasis_S
    Zbasis_S:=ZBasis(S);
    pos:=Position(Eltseq(S ! One(K)),1); //Eltseq(S ! One(K)) does not distinguish 1 from -1.....
    temp:=Zbasis_S[1];
    Zbasis_S[1]:=One(K);
    if pos ne 1 then
        Zbasis_S[pos]:=temp;
    end if;
    //assert Order(Zbasis_S) eq S;
    M:=Matrix(Zbasis_S);
    Minv:=M^-1;
    A:=ChangeRing(Matrix(ZBasis(I))*Minv,Integers());
    B:=ChangeRing(Matrix(ZBasis(J))*Minv,Integers());
    I_min:=MinimalInteger(I);
    J_min:=MinimalInteger(J);
    g,c1,d1:=XGCD(I_min,J_min);
    //assert I_min*One(K) in I and J_min*One(K) in J;
    if g ne 1 then
        C:=VerticalJoin(A,B);
        H,U:=HermiteForm(C); //U*C = H;
        z:=ZeroMatrix(Integers(),n,n);
        s:=ScalarMatrix(n,1);
        assert H eq VerticalJoin(s,z);
        P:=VerticalJoin(HorizontalJoin(z,s),HorizontalJoin(s,z));
        U1:=Transpose(U)*P; //I need the (n+1)st column of U1
        Z:=Transpose(U1)[n+1];
        X:=Matrix(Integers(),1,n,[Z[i] : i in [1..n]]);
        Y:=X*A;
        c:=&+[Y[1,i]*Zbasis_S[i] : i in [1..n]];
        assert c in I;
        d:=One(K)-c;
        assert d in J;
    else
        //g:=c1*I_min+d1*J_min
        c:=c1*I_min;
        d:=d1*J_min;
    end if;
    e:=a*d+b*c;
    assert e-a in I; assert e-b in J;
    return e;
end intrinsic;

intrinsic ResidueRing(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> GrpAb , Map
{given an integral ideal I of S, returns the abelian group S/I and the epimorphism pi:S -> S/I (with inverse map). Important: the domain of pi is the Algebra of S, since the elements of S are usually expressed al elements of A. For eg Parent(Random(S)) = Algebra(S)}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    require Order(I) eq S and IsIntegral(I): "I must be an integral ideal os S";
    A:=Algebra(S);
    N:=Degree(A);
    F:=FreeAbelianGroup(N);
    matS:=Transpose(Matrix(ZBasis(S)));
    matP:=Transpose(Matrix(ZBasis(I)));
    S_to_F:=function(x)
        assert Parent(x) eq A;
        assert x in S;
        clmn_vec_x:=Transpose(Matrix(x));
        x_inS:=matS^-1*clmn_vec_x; //column vector of wrt the ZBasis(S)
        assert N eq #Eltseq(x_inS);
        return (F ! Eltseq(x_inS)) ;
    end function;
    F_to_S:=function(y)
        clmn_vec_y:=Transpose(Matrix(Vector(Eltseq(y))));
        y_inA:=&+[ZBasis(S)[i]*Eltseq(clmn_vec_y)[i] : i in [1..N]];
    return y_inA;
    end function;
    StoF:=map< A -> F | x :-> S_to_F(x), y :-> F_to_S(y)>;
    rel:=[F ! Eltseq(x) : x in Rows(Transpose(matS^-1 * matP))];
    Q,q:=quo<F|rel>; //Q=S/I
    m:=StoF*q; //m is a map from S to Q
    assert #Q eq Index(S,I);
    assert forall{x : x in ZBasis(I) | m(x) eq Zero(Q)};
    assert forall{x : x in ZBasis(S) | ((m(x))@@m - x) in I};
    return Q,m;
end intrinsic;

intrinsic 'meet'(I::AlgAssVOrdIdl, S::AlgAssVOrd) -> AlgAssVOrdIdl
{given an ideal I of S, return S cap I}
    assert Algebra(I) eq Algebra(S);
    require Order(I) eq S: "the second argument must be an ideal of the first argument";
    return S meet I;
end intrinsic;

intrinsic 'meet'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{given an ideal I of S, return S cap I}
    assert Algebra(I) eq Algebra(S);
    require Order(I) eq S: "the second argument must be an ideal of the first argument";
    output := OneIdeal(S) meet I;
    return output;
end intrinsic;

intrinsic IsCoprime(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> BoolElt
{given two integral ideals I and J of an order S, returns whether I+J=R}
    assert Algebra(I) eq Algebra(J);
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    S:=Order(J);
    require Order(I) eq S: "the ideals must be over the same order";
    require IsIntegral(I) and IsIntegral(J): "the ideals must be integral";
    return (One(S) in I+J);
end intrinsic;

intrinsic IsIntegral(I::AlgAssVOrdIdl) -> BoolElt
{returns wheter the ideal I of S is integral, that is I \subseteq S}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    S:=Order(I);
    return I subset S;
end intrinsic;

intrinsic MakeIntegral(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{ginven a fractional S ideal I, returns the ideal d*I when d is the smallest integer such that d*I is integral in S}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    if IsIntegral(I) then return I; end if;
    S:=Order(I);
    d:=Denominator(ChangeRing(Matrix(Coordinates(ZBasis(I),ZBasis(S))),Rationals()));
    return d*I;
end intrinsic;

intrinsic 'eq'(I::AlgAssVOrdIdl, S::AlgAssVOrd) -> BoolElt
{return if I eq S. I needs to be an ideal of S}
  assert Algebra(I) eq Algebra(S);
  if Index(S, I) eq 1 then
      return I eq OneIdeal(S);
  else
      return false;
  end if;
end intrinsic;

intrinsic 'eq'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> BoolElt
{return if I eq S. I needs to be an indeal of S}
    return I eq S;
end intrinsic;

intrinsic 'subset'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> BoolElt
{given an ideal I of S, return if S subseteq I}
    assert Algebra(I) eq Algebra(S);
    require Order(I) eq S: "the second argument must be an ideal of the first argument";
    return OneIdeal(S) subset I;
end intrinsic;

intrinsic 'subset'(I::AlgAssVOrdIdl,S::AlgAssVOrd) -> BoolElt
{given an ideal I of S, return if I subseteq S}
    assert Algebra(I) eq Algebra(S);
    require Order(I) eq S: "the first argument must be an ideal of the second argument";
    return I subset OneIdeal(S);
end intrinsic;

intrinsic ProdEqOrders(A::AlgAss)->AlgAssVOrd
{given a product of number fields A, returns the order consisting of the product of the equation orders of the number fields}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    gen_inA:=[];
    for L in A`NumberFields do
        EL:=EquationOrder(L[1]);
        gen_inA:=gen_inA cat [L[2](y) : y in Basis(EL,L[1])];
    end for;
    return Order(gen_inA);
end intrinsic;

intrinsic Index(T::AlgAssVOrd) -> FldRatElt
{given an order T computes its index with respect to the basis of the algebra of T as a free Z-module}
  if not assigned T`Index then
    matT:=Matrix(ZBasis(T));
    T`Index := Abs(Rationals() ! Determinant(matT));
  end if;
  return T`Index;
end intrinsic;

intrinsic Index(S::AlgAssVOrd, T::AlgAssVOrd) -> Any
{given two orders T \subset S, returns [S:T] = #S/T }
  assert Algebra(T) eq Algebra(S);
  elt := Index(T)/Index(S);
  if IsCoercible(Integers(), elt) then
    elt := Integers() ! elt;
  end if;
  return elt;
end intrinsic;


intrinsic Index(T::AlgAssVOrdIdl) -> FldRatElt
{given an ideal T computes its index with respect to the basis of the algebra of T as a free Z-module}
  if not assigned T`PackageAttributes then
    T`PackageAttributes := rec< AlgAssVOrdIdlData2 | >;
  elif (not "Index" in Names(T`PackageAttributes)) and assigned T`PackageAttributes`Jprimes then
    Jprimes := T`PackageAttributes`Jprimes;
    T`PackageAttributes := rec< AlgAssVOrdIdlData2 | >;
    T`PackageAttributes`Jprimes := Jprimes;
  end if;
  if not assigned T`PackageAttributes`Index then
    matT := Matrix(ZBasis(T));
    T`PackageAttributes`Index := Abs(Rationals() ! Determinant(matT));
  end if;
  return T`PackageAttributes`Index;
end intrinsic;

intrinsic Index(J::AlgAssVOrdIdl, I::AlgAssVOrdIdl) -> FldRatElt
{given fractional ideals J and I defined over the same order returns [J:I] = [J:J cap I]/[I : J cap I]}
    require Order(I) eq Order(J): "the ideals must be of the same order";
  return Index(I)/Index(J);
end intrinsic;

intrinsic Index(S::AlgAssVOrd, I::AlgAssVOrdIdl) -> FldRatElt
{given and ideal I of an order S returns [S:I] = [S:S cap I]/[I : S cap I] }
    require Order(I) eq S: "the ideal must be of the appropriate order";
    return Index(OneIdeal(S), I);
end intrinsic;

/*
intrinsic Automorphisms(A::AlgAss) -> SeqEnum[Maps]
{returns the automorphisms of A as a sequence of maps. A must be a product of number fields and the maps are componentwise automorphisms}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    S:=[ Automorphisms(L[1]) : L in A`NumberFields ];
    output:=[];
    for s in AllPossibilities(S) do
        r:=#A`NumberFields;
        assert #s eq r;
        map_s:=map< A->A | x:-> &+[A`NumberFields[i,2](s[i](Components(x)[i])) : i in [1..r]] >;
        Append(~output, map_s);
    end for;
    return output;
end intrinsic;
*/

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


function factorizationMaximalOrder(I)
//given an ideal of the maximal order of an algebra, returns the factorization into a product of prime ideals
    O:=Order(I);
    assert IsMaximal(O);
    A:=Algebra(O);
    _,IasProd:=IsProductOfIdeals(I);
    fac:=[]; //this will be the factorization of I
    for i in [1..#A`NumberFields] do
        L:=A`NumberFields[i,1];
        mL:=A`NumberFields[i,2];
        IL:=IasProd[i];
        assert IsMaximal(Order(IL));
        facL:=Factorization(IL);
        for p in facL do
            genPinA:=[mL(x) : x in Basis(p[1],L)] cat [F[2](One(F[1])) : F in A`NumberFields | F[1] ne L];
            P:=ideal<O | genPinA>;
            Append(~fac,<P,p[2]>);
        end for;
    end for;
    assert I eq &*[p[1]^p[2] : p in fac];
    return fac;
end function;

intrinsic Factorization(I::AlgAssVOrdIdl) -> Tup
{given a proper integral S-ideal I coprime with the conductor of S (hence invertible in S), returns its factorization into a product of primes of S}
    S:=Order(I);
    require IsIntegral(I) and I ne OneIdeal(S): "the argument must be a proper integral ideal";
    if IsMaximal(S) then
        return factorizationMaximalOrder(I);
    else
        fS:=Conductor(S);
        require IsCoprime(fS,I): "the ideal must be coprime with the conductor of the order of definition";
        require assigned Algebra(I)`NumberFields :"it must be a product of number fields";
        O:=MaximalOrder(Algebra(I));
        IO:=O ! I;
        facO:=factorizationMaximalOrder(IO);
        primesO:=[ p[1] : p in facO ];
        primesS:=Setseq({ S meet (S!PO) : PO in primesO }); //this should cancel the doubles
        facS:=<>;
        for P in primesS do
            expP:=&+([ pO[2] : pO in facO | (S meet (S!pO[1])) eq P ]);
            Append(~facS, <P,expP>);
        end for;
        assert I eq &*([ p[1]^p[2] : p in facS ]);
        return facS;
    end if;
end intrinsic;

intrinsic IsBass(S::AlgAssVOrd) -> BoolElt
{check if the order is Bass}
// we compute the maximal order O and check if O/PO is at most 2-dimensional over S/P for every singular prime P
// This coincides with the usual definition since O has the maximal number of generators as a fractional S ideal and S is Bass iff every ideal can be generated by at most 2-elements.
// see Hofman,Sircana, On the computations of over-orders, Definition 5.23
    if IsMaximal(S) then 
        return true;
    else
        O:=MaximalOrder(Algebra(S));
        ff:=Conductor(S);
        sing:=PrimesAbove(ff);
        for P in sing do
            k:=Integers() ! Index(S,P);
            OS:=ideal<S|ZBasis(O)>;
            N:=Integers() ! Index(OS,P*OS);
            //N = k^(dim_P)
            assert N mod k eq 0;
            dim_P:=Ilog(k,N);
            if dim_P gt 2 then
                return false; //S is not Bass at P
            end if;
        end for;
        return true;
    end if;
end intrinsic;

intrinsic IsClifford(S::AlgAssVOrd) -> BoolElt
{checks if all the over orders of S are Gorenstein}
    return IsBass(S);
end intrinsic;

intrinsic EquationOrder(A::AlgAss) -> AlgAssVOrd
{given an associative algebra defined by a polynomial, returns the monogenic order defined by the same polynomial}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    F:=PrimitiveElement(A);
    E:=Order([F^i : i in [0..Degree(A)-1]]);
    return E;
end intrinsic;

intrinsic ColonIdeal(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
{computes the colon ideal (I:J) (as an O-ideal) of two O-ideals}
// require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    O := Order(I);
    require Order(J) eq O : "the ideals must be of the same order";
    C := Colon(I,J);
    C := PseudoMatrix(CoefficientIdeals(C), Matrix(C) * Matrix(PseudoMatrix(O))^-1 );
    IJ := ideal<O|C>;
    return IJ;
end intrinsic;

intrinsic ColonIdeal(O::AlgAssVOrd,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
{computes the colon ideal (1*O:J) (as an O-ideal)}
    require Order(J) eq O : "the ideals must be of the same order";
    return ColonIdeal(OneIdeal(O), J);
end intrinsic;

intrinsic ColonIdeal(I::AlgAssVOrdIdl,O::AlgAssVOrd)->AlgAssVOrdIdl
{computes the colon ideal (I:1*O) (as an O-ideal)}
    require Order(I) eq O : "the ideals must be of the same order";
    //return ColonIdeal(I, OneIdeal(O));
    return I; //since we require O=Order(I)
end intrinsic;

intrinsic Inverse(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
{computes the inverse of an ideal of a maximal order}
    O:=Order(I);
    require IsMaximal(O): "only for ideals in maximal orders. use ColonIdeal otherwise";
    return ColonIdeal(O,I);
end intrinsic;

intrinsic Conductor(O::AlgAssVOrd) ->AlgAssVOrdIdl
{computes the conductor of an order}
    A:=Algebra(O);
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    OA:=MaximalOrder(A);
    return ColonIdeal(O,ideal<O|ZBasis(OA)>);
end intrinsic;

intrinsic IsWeakEquivalent(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->BoolElt
{ checks if 1 \in (I:J)*(J:I). This function does not require that the ideals are defined over the same order. }
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    S := MultiplicatorRing(I);
    if MultiplicatorRing(J) ne S then
        return false;
    else
        IS:=S!I;
        JS:=S!J;
        CIJ:=ColonIdeal(IS,JS);
        CJI:=ColonIdeal(JS,IS);
        //test := OneIdeal(S) eq (CIJ*CJI); //note that this test does not depend on the order of definition of the ideals.
        test:=One(Algebra(I)) in (CIJ*CJI); //faster!
        return test;
        end if;
end intrinsic;

intrinsic IsWeakEquivalent(O1::AlgAssVOrd,O2::AlgAssVOrd)->BoolElt
{ check if the two orders are weakly equivalent, that is equal }
    require IsFiniteEtale(Algebra(O1)): "the algebra of definition must be finite and etale over Q";
    return O1 eq O2;
end intrinsic;

intrinsic IsWeakEquivalent(O::AlgAssVOrd,J::AlgAssVOrdIdl)->BoolElt
{ checks if the second argument is weakly equivalent to the first argument }
    require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
    return IsWeakEquivalent(OneIdeal(O), J);
end intrinsic;

intrinsic IsWeakEquivalent(J::AlgAssVOrdIdl,O::AlgAssVOrd)->BoolElt
{ checks if the second argument is weakly equivalent to the first argument }
    require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
    return IsWeakEquivalent(OneIdeal(O), J);
end intrinsic;

intrinsic IsInvertible(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
{ checks if the ideal is invertible in its order of definition }
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    O:=Order(I);
    return IsWeakEquivalent(I,O);
end intrinsic;

intrinsic IsGorenstein(O::AlgAssVOrd)->BoolElt
{ checks if the order O is Gorenstein }
    require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
    T:=TraceDualIdeal(O);
    return IsInvertible(T);
end intrinsic

intrinsic OrthogonalIdempotents(A::AlgAss)->SeqEnum
{returns a sequence containing the orthogonal ideampotents of the algebra, that is the image of the units of the number fields the algebra is product of}
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    return [L[2](One(L[1])) : L in A`NumberFields ];
end intrinsic;

intrinsic AssociativeAlgebra(f::RngUPolElt) -> AlgAss
{given a integer polynomial f generates the Associative algebra over Q given by the factors of f with multiplicity}
  f_fac:=Factorization(f);
  num_fields:=[NumberField(g[1] : DoLinearExtension := true) : j in [1..g[2]] , g in f_fac];
  return AssociativeAlgebra(num_fields);
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

/*
splittingfield_internal:=function(K)
//given a number field K returns a pair L,l where L is the SplittingField of K and l is an embedding K in L
//it is much faster then the in-built function SplittingField(K)
    f:=DefiningPolynomial(K);
    F:=PrimitiveElement(K);
    L:=SplittingField(f);
    pL:=PolynomialRing(L);
    fact:=Factorization(pL!f);
    l:=hom<K->L | F:->Coefficients(fact[1,1])[1]>;
    return L,l;
end function;

intrinsic SplittingAlgebra(A::AlgAss) -> AlgAss, Map
{ given a product of number fields A, returns the product of the splitting fields and a map from A }
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    split_fields:=[];
    split_fields_embeddings:=[];
    for K in A`NumberFields do
        L,l:=splittingfield_internal(K[1]);
        Append(~split_fields,L);
        Append(~split_fields_embeddings,l);
    end for;
    AA:=AssociativeAlgebra(split_fields);
    assert #A`NumberFields eq #AA`NumberFields;
    map_AtoAA:=map< A -> AA | x :-> &+[AA`NumberFields[i][2](split_fields_embeddings[i](Components(x)[i])) : i in [1..#AA`NumberFields]]>;
    return AA, map_AtoAA;
end intrinsic;
*/


intrinsic PrimitiveElement(A::AlgAss) -> AlgAssElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    assert IsSquarefree(DefiningPolynomial(A));
    return &+[L[2](PrimitiveElement(L[1])) : L in A`NumberFields];
end intrinsic;

intrinsic DefiningPolynomial(A::AlgAss) -> RngUPolElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    return &*[DefiningPolynomial(L[1]) : L in A`NumberFields];
end intrinsic;

intrinsic '^'(I::AlgAssVOrdIdl, n::RngIntElt) -> AlgAssVOrdIdl
{ compute the nth power of an ideal }
    S:=Order(I);
    power_positive:=function(I, n)
        id := I;
        output := OneIdeal(S);
        bin_exp:=IntegerToSequence(n,2);
        for i in [1..#bin_exp] do
            if bin_exp[i] eq 1 then
                output *:= id;
            end if;
            if i lt #bin_exp then
                id := id*id;
            end if;
        end for;
        return output;
    end function;
    if n eq 0 then
        return OneIdeal(S);
    elif n eq 1 then
        return I;
    elif n eq 2 then
        return I * I;
    else
        if n gt 0 then
            return power_positive(I,n);
        end if;
        if n lt 0 then
            require IsInvertible(I) :"the ideal must be invertible";
            invI:=ColonIdeal(S,I);
            return power_positive(invI,-n);
        end if;
    end if;
end intrinsic;

intrinsic IsProductOfOrders(O::AlgAssVOrd)->BoolElt, Tup
{return if the argument is a product of orders in number fields, and if so return also the sequence of these orders}
        if not assigned O`IsProductOfOrders then
            A:=Algebra(O);
	    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	    idem:=OrthogonalIdempotents(A);
	    test:=forall{x : x in idem | x in O};
	    O_asProd:=<>;
	    if test then
		for i in [1..#A`NumberFields] do
			L:=A`NumberFields[i];
			gen_L:=[(x*idem[i])@@L[2]: x in ZBasis(O)];
			O_L:=Order(gen_L);
			Append(~O_asProd,O_L);
		end for;
                O`IsProductOfOrders := <true, O_asProd>;
	    else
		O`IsProductOfOrders := <false,<>>;
	    end if;
        end if;
        return O`IsProductOfOrders[1], O`IsProductOfOrders[2];
end intrinsic;

/* I don't like the name
intrinsic IsDecomposable(O::AlgAssVOrd)->BoolElt, Tup
{return if the argument is a product of orders in sub-algebras, and if that's the case returns the minimal idempotents in O}
    A:=Algebra(O);
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    non_trivial_idem:=Exclude(Exclude(Idempotents(A),A!0),A!1);
    nt_idem_in_O:=[x : x in non_trivial_idem | x in O];
    if #nt_idem_in_O eq 0 then
        return false,_;
    end if;
    //one nt_idem_in_O is in O i.e. O splits.
    //now we want to find the minimal ideampotents in O
    idems:={};
    cc:=CartesianProduct(nt_idem_in_O,nt_idem_in_O);
    for id in nt_idem_in_O do
        if not exists{c : c in cc | id eq c[1]+c[2]} then
            idems:=idems join {id};
        end if;
    end for;
    return true,Setseq(idems);
end intrinsic;
*/

/*
//TO FINISH! second output missing!
intrinsic IsDecomposable(I::AlgAssVOrdIdl)->BoolElt, Tup
{return if the argument is a product of orders in sub-algebras, and if that's the case returns the minimal idempotents in O}
    S:=MultiplicatorRing(I);
    return IsDecomposable(S);
end intrinsic;
*/

intrinsic IsProductOfIdeals(I::AlgAssVOrdIdl) -> BoolElt, Tup
{return if the argument is a product of ideals in number fields, and if so return also the sequence of these ideals (in the appropriate orders)}
    O:=MultiplicatorRing(I);
    A:=Algebra(O);
    require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
    test,O_asProd:=IsProductOfOrders(O);
    I_asProd:=<>;
    if test then
        idem:=OrthogonalIdempotents(A);
        for i in [1..#A`NumberFields] do
            L:=A`NumberFields[i];
            gen_L:=[(x*idem[i])@@L[2]: x in ZBasis(I)];
            I_L:=ideal<O_asProd[i]|gen_L>;
            Append(~I_asProd,I_L);
        end for;
        return true, I_asProd;
    else
        return false,<>;
    end if;
end intrinsic;

intrinsic IsIsomorphic2(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> BoolElt, AlgAssElt
{checks if I=x*J, for some x. If so, also x is returned}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    test:=IsWeakEquivalent(I,J); //if so I=(I:J)*J and (I:J) is invertible in its MultiplicatorRing
    if test then
        S:=MultiplicatorRing(I);
        IS:=S!I;
        JS:=S!J;
        CIJ:=ColonIdeal(IS,JS);
        test2,x:= IsPrincipal(CIJ);
        if test2 then
            return test2,x;
        assert2 I eq x*J;
        else
            return false, _ ;
        end if;
    else
        return false , _ ;
    end if;
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

intrinsic TraceDualIdeal(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{ returns the trace dual ideal of an ideal in an order in an associative algebra }
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    S:=Order(I);
    B:=ZBasis(I);
    n:=#B;
    Q:=MatrixRing(RationalField(), n)![Trace(B[i]*B[j]): i, j in [1..n] ];
    QQ:=Q^-1;
    BB:=[&+[ (QQ[i,j]*B[j]): j in [1..n]] : i in [1..n]] ;
    return ideal<S|BB>;
end intrinsic;

intrinsic TraceDualIdeal(O::AlgAssVOrd) -> AlgAssVOrdIdl
{ returns the trace dual ideal of an order in an associative algebra }
    require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
    return TraceDualIdeal(OneIdeal(O));
end intrinsic;

/*
intrinsic IsFractionalIdl(I::AlgAssVOrdIdl) -> BoolElt
{ checks if the ideal is fractional, that is if contains a non-zero-divisor }
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    num_gens:=#Generators(I); //note that the number of generators depends on the rank as an abelian group
    return num_gens eq Dimension(Algebra(I));
end intrinsic;
*/

intrinsic IsMaximal(O::AlgAssVOrd) -> BoolElt
{ checks if the order is the maximal order of its associative algebra}
    require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
    if not assigned O`IsMaximal then
        OK:=MaximalOrder(Algebra(O));
        O`IsMaximal:=OK eq O;
    end if;
    return O`IsMaximal;
end intrinsic;

intrinsic 'subset'(O1 :: AlgAssVOrd, O2 :: AlgAssVOrd) -> BoolElt
{Checks if the first argument is inside the second.}
  require Algebra(O1) cmpeq Algebra(O2) : "The orders must be in the same algebra.";
  if not Index(O2, O1) in Integers() then
    return false;
  end if;
  mat := Matrix(Coordinates(ZBasis(O1), ZBasis(O2)));
  return &and[IsCoercible(Integers(), elt) : elt in Eltseq(mat)];
end intrinsic;

intrinsic 'subset'(I1 :: AlgAssVOrdIdl, I2 :: AlgAssVOrdIdl) -> BoolElt
{Checks if the first argument is inside the second. The ideals need to be fractional}
  require Order(I1) eq Order(I2) : "The ideals must be in the same order.";
  if not Index(I2, I1) in Integers() then
    return false;
  end if;
  mat := Matrix(Coordinates(ZBasis(I1), ZBasis(I2)));
  return &and[IsCoercible(Integers(), elt) : elt in Eltseq(mat)];
end intrinsic;

intrinsic Idempotents(A::AlgAss)->SeqEnum
{returns a sequence containing the ideampotents of the algebra, zero included}
    ort_idem:=OrthogonalIdempotents(A);
    cc:=CartesianProduct([[A!0,oi] : oi in ort_idem]);
    idem:=[&+([cj : cj in c]) : c in cc];
    return idem;
end intrinsic;
