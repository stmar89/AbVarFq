freeze;

/////////////////////////////////////////////////////
// Functions over-written for Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
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

