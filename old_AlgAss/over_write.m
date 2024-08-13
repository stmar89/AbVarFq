/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Functions over-written for Etale Q algebras
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
/////////////////////////////////////////////////////


/*what follows overwrites "bugged" functions*/

/* I don't think this is used....
 
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
*/


intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
{Product of ideals I and J.}
//over-writes ..../ideals.m very different
//over-writes ..../ideals-jv.m this over-writes the above. my code is very similar to the jv version, but I skip the last part which seems to refer to the non-commutative part. Nevertheless it seems to ompletely break my code....
  O:=Order(I);
  A:=Algebra(O);
  require IsFiniteEtale(A): "Arguments must be ideals of orders in an Finite Etale Algebra over Q";
  require A cmpeq Algebra(Order(J)) : "Arguments must be ideals of orders in the same algebra";
  require O cmpeq Order(J) : "Arguments must be ideals of orders in the same algebra";
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

/*
//the difference with my code, apart from a lot of removing 'not used' things is that I do not want to check that RightOrder(I) cmepq LeftOrder(J) because I want to allow multiplication of ideals with different multiplicator rings.
// but note that (IJ:IJ) might be strictly bigger than (I:I)+(J:J). Hence the multiplicatorring of the product should always be recomputed!!!

debug:=false;
intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd] : Check:=true, Sides:="Both") -> 
     AlgAssVOrdIdl, AlgAssVOrdIdl
  {Product of ideals I and J. Returns two objects by default: firstly I*J as a left ideal,
   and secondly I*J as a right ideal.  When "Sides" is set to "Left" or "Right", only one 
   of these is returned}

  // When I is officially a left ideal (of Order(I)), the left ideal I*J is created 
  // as a lideal of Order(I), and otherwise as a lideal of LeftOrder(I).  
  // Likewise for the right I*J.

  if Check then
    require RightOrder(I) cmpeq LeftOrder(J) : 
      "Right order of the first argument must be equal to the left order of the second";
  end if;
  require Algebra(Order(I)) cmpeq Algebra(Order(J)) : 
    "Arguments must be ideals of orders in the same algebra";
  require Sides in {"Left", "Right", "Both"} : 
    "The optional argument \"Sides\" should be \"Left\", \"Right\" or \"Both\"";

  // Compute P = pmatrix of I*J, expressed relative to the basis of A
  O := Order(I);
  A := Algebra(O);
  S := [x*y : x in Basis(I, A), y in Basis(J, A)];
  CI := CoefficientIdeals(PseudoMatrix(I));
  CJ := CoefficientIdeals(PseudoMatrix(J));
  C := [ci*cj : ci in CI, cj in CJ];
  P := PseudoMatrix(C, Matrix(S));
  P := HermiteForm(P);

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
end intrinsic;
*/

// stuff to be included after breaking update 2.25-6
forward order_over;

function IsOrder(O);
  S := Basis(O);
  I := CoefficientIdeals(PseudoMatrix(O));

  // Check that (S,I) generates a ring
  isRing := true;
  for i,j in [1..Degree(O)] do
    for gi in Generators(I[i]) do
      for gj in Generators(I[j]) do
        s := gi*S[i];
        t := gj*S[j];
        if not IsCoercible(O, s*t) then
          printf "i = %o\nj = %o\ngi = %o\ngj = %o\nS[i] = %o\nS[j] = %o\nst = %o\n", 
                 i, j, gi, gj, S[i], S[j], s*t;
          isRing := false;
          break i;
        end if;
      end for;
    end for;
  end for;

  return isRing;
end function;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]] : Check := true) -> AlgAssVOrd
  {Given a sequence S of elements of A, returns the order generated by S
   as a module (over the maximal order of the underlying number field)}

  return Order(S, [] : Check := Check);
end intrinsic;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : 
                Check := true) -> AlgAssVOrd
  {Returns the order which has pseudobasis given by the basis elements S 
   and the coefficient ideals I}  

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

function order_over(Z_F, S, I : Check := true)
/*
    New version from S. Marseglia, Oct 2019.
    Now a loop keeps adding the products of the generators and reduces to
    HNF until it stabilizes (i.e., we get a multiplicatively closed set,
    that is, a ring).
*/

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
