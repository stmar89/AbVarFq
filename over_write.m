freeze;

/////////////////////////////////////////////////////
// Functions over-written for Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////


/*what follows overwrites "bugged" functions*/


intrinsic 'in'(a::RngElt, I::AlgAssVOrdIdl) -> BoolElt
{Return true iff a is in I. Here I must be an ideal (or fractional ideal) of an order
in an associative algebra.}
//overwrites the same fuction in ../package/Algebra/AlgAss/ideals-jv.m
    A:= Algebra(I);
    bool, a := IsCoercible(A, a);
    require bool : "The given element must be coercible to the algebra of the ideal";
    matrix:= Matrix(Basis(I, A));
    ans, coords := IsConsistent(matrix, Vector(a));
    assert ans;
    if Type(I) eq AlgQuatOrdIdl then
        ans:= forall{ i: i in [1..4] | IsIntegral(coords[i]) };
    else
        ideals:= CoefficientIdeals( PseudoMatrix(I) );
        //next line was fixed by Stefano
        //WRONG    ans:= forall{ i: i in [1..4] | coords[i] in ideals[i] };
        ans:= forall{ i: i in [1..#ideals] | coords[i] in ideals[i] };
    end if;
    return ans;
end intrinsic;

function order_over(Z_F, S, I : Check := true)
//modified from order-jv.m
  A := Universe(S);
  F := BaseRing(A);
  n := Dimension(A);
  if (A!1 notin S) then
    Append(~S, 1);
    Append(~I, 1*Z_F);
  end if;
  // Find an initial pseudobasis
  M := Matrix(F,#S,n, &cat[Eltseq(s) : s in S]);
  P := PseudoMatrix(I,M);
  P := HermiteForm(P);
  I := CoefficientIdeals(P);
  M := ChangeRing(Matrix(P),F);
  S := [A ! Eltseq(M[i]) : i in [1..Nrows(M)]];

  P_old:=P;
  repeat
      P_old:=P;
      M:=ChangeRing(Matrix(P_old),F);
      S := [A ! Eltseq(M[i]) : i in [1..Nrows(M)]];
      I:=CoefficientIdeals(P_old);
      for i,j in [1..#S] do
          s:=S[i]; id_i:=I[i];
          t:=S[j]; id_j:=I[j];
          M:=VerticalJoin(M,Matrix(F,1,n,Eltseq(s*t)));
          Append(~I,id_i*id_j);
          M:=VerticalJoin(M,Matrix(F,1,n,Eltseq(t*s)));
          Append(~I,id_j*id_i);
      end for;
      P:=PseudoMatrix(I,M);
      P:=HermiteForm(P);
      M_new:=ChangeRing(Matrix(P),F);
      rk:=Rank(M_new);
      M_new:=Matrix( Rows(M_new)[1..rk] );
      I_new:=CoefficientIdeals(P)[1..rk];
      P:=PseudoMatrix(I_new,M_new);
  until P eq P_old;

  error if Rank(M_new) ne n,
         "The given elements don't generate a lattice of full rank";
  M := MatrixRing(F,n) ! M_new;
  I:=I_new;
  O := Order(A, M, I);

  assert2 IsOrder(O);
  return O;
end function;

/*
intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : Check := true) -> AlgAssVOrd
  {Returns the order which has pseudobasis given by the basis elements S
   and the coefficient ideals I}
//over-writes order-jv.m
//it seems to be exactly the same!
  A := Universe(S);
  F := BaseRing(A);
  Z_F := MaximalOrder(F);
  n := Dimension(A);
  if I eq [] then
    I := [ideal<Z_F | 1> : i in [1..#S]];
  end if;
  require R cmpeq Z_F or R cmpeq FieldOfFractions(Z_F) where R is Ring(Universe(I)) :
        "Ideals in argument 2 must be of the ring of integers of the base ring of argument 1";
  require not ISA(Type(A), AlgMatV) : "Argument 1 must not contain elements of a matrix algebra";
  return order_over(Z_F, S, I : Check := Check);
end intrinsic;
*/

intrinsic '+'(O1::AlgAssVOrd[RngOrd], O2::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
  {Computes the sum O1+O2, the smallest order containing both O1 and O2.}
//over-writes order-jv.m
  require Algebra(O1) cmpeq Algebra(O2) :
    "Orders must be contained in the same algebra";
//what follows is the WRONG original code: it's the sum of O1 and O2 as modules, not the smallest order containing O1 and O2!!!!!!!
//   P := VerticalJoin(PseudoMatrix(O1), PseudoMatrix(O2));
//   P := HermiteForm(P);
//   O := Order(Algebra(O1), P);
  b1:=ZBasis(O1);
  b2:=ZBasis(O2);
  n:=#b1;
  assert #b2 eq n;
  O:=Order(&cat[[b1[i]*b2[j] , b2[j]*b1[i]] : i,j in [1..n]]);
  if assigned O1`ChangeRingMap then
    O`ChangeRingMap := O1`ChangeRingMap;
  end if;
  isRing := IsOrder(O);
  if not isRing then
    error "The sum does not generate a ring";
  else
    return O;
  end if;
end intrinsic;

intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
{Product of ideals I and J.}
//over-writes ..../ideals.m
//over-writes ..../ideals-jv.m
  A:=Algebra(I);
  require IsFiniteEtale(A): "Arguments must be ideals of orders in an Finite Etale Algebra over Q";
  O:=Order(I);
  require A cmpeq Algebra(Order(J)) : "Arguments must be ideals of orders in the same algebra";
  require O cmpeq Order(J) : "Arguments must be ideals of orders in the same algebra";
//   require IsTwoSidedIdeal(I) and IsTwoSidedIdeal(J): "the ideals must be two-sided";
  if I eq OneIdeal(Order(I)) then
    return J;
  elif J eq OneIdeal(Order(J)) then
    return I;
  end if;
  // Compute P = pmatrix of I*J, expressed relative to the basis of A
  S := [x*y : x in Basis(I, A), y in Basis(J, A)];
  CI := CoefficientIdeals(PseudoMatrix(I));
  CJ := CoefficientIdeals(PseudoMatrix(J));
  C := [ci*cj : ci in CI, cj in CJ];
  P := PseudoMatrix(C, Matrix(S));
  P := HermiteForm(P);
  // Get P relative to the basis of O, since the ideal constructor expects this
  P := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(O))^-1 );
  IJ := ideal<O | P>;
  return IJ;
end intrinsic;

