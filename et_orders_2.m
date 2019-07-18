freeze;


//---------------------
//
// WORK IN PROGRESS to be tested and finish move to AlgEt
//
//--------------------

/////////////////////////////////////////////////////
// Extra Functions for order in Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

declare verbose AlgEtOrd, 1;


/* I don't like the name
intrinsic IsDecomposable(O::AlgEtOrd)->BoolElt, Tup
{return if the argument is a product of orders in sub-algebras, and if that's the case returns the minimal idempotents in O}
    A:=Algebra(O);
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
intrinsic IsDecomposable(I::AlgEtOrdIdl)->BoolElt, Tup
{return if the argument is a product of orders in sub-algebras, and if that's the case returns the minimal idempotents in O}
    S:=MultiplicatorRing(I);
    return IsDecomposable(S);
end intrinsic;
*/

intrinsic pMaximalOrder(O::AlgEtOrd, p::RngIntElt) -> AlgEtOrdIdl
{returns the artihmetic radical of O at p}
    OO:=AssOrder(O);
    I := ArithmeticRadical(OO, BaseRing(OO)*p);
    return O !! I;
end intrinsic;

intrinsic pMaximalOrder(O::AlgEtOrd, p::RngIntElt) -> AlgEtOrd
{given O, retuns the maximal p over order}
  if (Abs(Integers() ! Discriminant(O)) mod p^2) ne 0 then
    return O;
  end if;

  OO := O;
  // Theorem 6.1.3 Cohen
  while true do
    I := ArithmeticRadical(OO, BaseRing(OO)*p);
    OO := MultiplicatorRing(I);
    if OO eq Order(I) then
      return OO;
    end if;
  end while;
end intrinsic;


