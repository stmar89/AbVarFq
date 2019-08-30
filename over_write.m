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
//quite different from the original 

  A := Universe(S);
  F := BaseRing(A);
  n := Dimension(A);

  if (A!1 notin S) then
    Append(~S, 1);
    Append(~I, 1*Z_F);
  end if;

/* //removed.
    if Check and (A!1 notin S) then
        // Always add 1 to the order
        Append(~S, 1);
        Append(~I, 1*Z_F);
    end if;
    if not Check then
        error if #S ne n, "Argument 1 must have length ", n, " to be a basis";
        M := MatrixRing(F,n) ! &cat[Eltseq(s) : s in S];
        return Order(A, M, I);
    end if;
*/          
  // Find an initial pseudobasis. not changed
  M := Matrix(F,#S,n, &cat[Eltseq(s) : s in S]);
  P := PseudoMatrix(I,M);
  P := HermiteForm(P);
  I := CoefficientIdeals(P);
  M := ChangeRing(Matrix(P),F);
  S := [A ! Eltseq(M[i]) : i in [1..Nrows(M)]];

/*  
  // Check that the module S tensor with the rationals is
  // multiplicatively closed
  if #S lt n then
    for i := 1 to #S do
      s := S[i];
      j := 1;
      while j le #S do
        t := S[j];
        Mst := VerticalJoin(M, Vector(s*t));
        if Rank(Mst) gt NumberOfRows(M) then
          Append(~S, s*t);
          Append(~I, I[i]*I[j]);
          M := Mst;
          if #S eq n then
            // We already have a full lattice
            break i;
          end if;
        end if;

        Mts := VerticalJoin(M, Vector(t*s));
        if Rank(Mts) gt NumberOfRows(M) then
          Append(~S, t*s);
          Append(~I, I[j]*I[i]);
          M := Mts;
          if #S eq n then
            // We already have a full lattice
            break i;
          end if;
        end if;

        j +:= 1;
      end while;  
    end for;
  end if;
*/
//replaced by ....
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
  M:=M_new;

  error if Rank(M) ne n,
         "The given elements don't generate a lattice of full rank";
  M := MatrixRing(F,n) ! M_new;
  I:=I_new;
  O := Order(A, M, I);
//end replacement

/*
  // Check that (S,I) generates a ring
  if not IsOrder(O) then
    error "These generators do not generate a ring";
  end if;
*/
//replaced by...
  assert2 IsOrder(O);

  return O;
end function;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : Check := true) -> AlgAssVOrd
  {Returns the order which has pseudobasis given by the basis elements S
   and the coefficient ideals I}
//nothing is changed. I need it in order to trigger the (heavily) over-written order_over(...), see above.

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

intrinsic '+'(O1::AlgAssVOrd[RngOrd], O2::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
  {Computes the sum O1+O2, the smallest order containing both O1 and O2.}
//over-writes order-jv.m
//see below for the changes
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
//end of changes

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
//over-writes ..../ideals.m very different
//over-writes ..../ideals-jv.m this over-writes the above. my code is very similar to the jv version, but I skip the last part which seems to refer to the non-commutative part. Nevertheless it seems to ompletely break my code....
  O:=Order(I);
  A:=Algebra(O);
  require IsFiniteEtale(A): "Arguments must be ideals of orders in an Finite Etale Algebra over Q";
  require A cmpeq Algebra(Order(J)) : "Arguments must be ideals of orders in the same algebra";
  require O cmpeq Order(J) : "Arguments must be ideals of orders in the same algebra";
//new  
  if I eq OneIdeal(Order(I)) then
    return J;
  elif J eq OneIdeal(Order(J)) then
    return I;
  end if;

/*
  // If I and J are both officially 2-sided ideals of O, return the same object for left and right
  if Sides ne "Right" and IsTwoSidedIdeal(I) and IsTwoSidedIdeal(J) and O eq Order(J) then
    // Get P relative to the basis of O, since the ideal constructor expects this
    P := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(O))^-1 );
    IJ := ideal<O | P : Check:=debug>;
    if assigned I`LeftOrder then IJ`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJ`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJ`Norm := I`Norm*J`Norm; end if;
    return IJ, IJ;
  end if;

  // Set up left ideal I*J
  if Sides ne "Right" then
    OL := IsLeftIdeal(I) select Order(I) 
                          else  LeftOrder(I);
    PL := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(OL))^-1 );
    IJleft := lideal< OL | PL : Check:=debug >;
    if assigned I`LeftOrder then IJleft`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJleft`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJleft`Norm := I`Norm*J`Norm; end if;
  end if;

  // Set up right ideal I*J
  // TO DO: we could take PR:=PL when IsIdentical(OL,OR), or when they have the same basis
  if Sides ne "Left" then
    OR := IsRightIdeal(J) select Order(J) 
                           else  RightOrder(J);
    PR := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(OR))^-1 );
    IJright := rideal< OR | PR : Check:=debug >;
    if assigned I`LeftOrder then IJright`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJright`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJright`Norm := I`Norm*J`Norm; end if;
  end if;

  if Sides eq "Left" then 
    return IJleft;
  elif Sides eq "Right" then 
    return IJright;
  elif Sides eq "Both" then 
    return IJleft, IJright;
  end if;
*/
//replaced by...
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




