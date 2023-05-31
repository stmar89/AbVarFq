
// Depends on CHIMP for:
// WPSNormalizeCC

intrinsic IgusaInvariantsG2(tau::ModMatFldElt) -> SeqEnum
    tau := ReduceSmallPeriodMatrix(tau);
    CC := BaseRing(tau);
    R<x> := PolynomialRing(CC);
    fCC := x * (x - 1) * &*[x - r: r in RosenhainInvariants(tau)];
    JCC := IgusaInvariants(fCC);
    return WPSNormalizeCC([2,4,6,8,10], JCC);
end function;

intrinsic IgusaToAffineInvariants(Jlist::SeqEnum) -> SeqEnum
{ Convert Igusa invariants to Affine invariants away from J10 = 0 }
  J10 := Jlist[5];
  R := Parent(J10);
  require #Jlist eq 5: "We expected a list of 5 invariants";
  if Type(R) in [FldCom, FldRe] then
    require Abs(J10) gt R`epscomp: "It seems that J10 is zero";
  end if;
    monomials := [
        [5, 0, 0, 0, -1], // g1
        [3, 1, 0, 0, -1], // g2
        [2, 0, 1, 0, -1], // g3
        [0, 5, 0, 0, -2], // g2'
        [0, 1, 1, 0, -1], // g3'
        [0, 0, 5, 0, -3] // g3''
        ];
    return [&*[Jlist[i]^w : i->w in m] : m in monomials];
end intrinsic;


intrinsic AffineInvariantsToG2(A::SeqEnum) -> SeqEnum
{given a Affine invariants converst them to G2 invariants}
    if A[1] ne 0 then
        return A[1..3];
    end if;
    if A[4] ne 0 then
        assert A[2] eq 0 and A[3] eq 0;
        return A[3..5];
    end if;
    assert A[5] eq 0;
    assert A[6] ne 0;
    return A[4..6];
end intrinsic;
