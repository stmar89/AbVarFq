freeze;

/////////////////////////////////////////////////////
// Ideals of given index for Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl, http://www.staff.science.uu.nl/~marse004/
// Edgar Costa, MIT
/////////////////////////////////////////////////////

intrinsic IdealsOfIndex(O::RngOrd, N::RngIntElt) -> SeqEnum[RngOrdIdl]
{Given an Order, retuns all the ideals of index N in that order}
  vprintf Ordersext : "IdealsOfIndex RngOrd Int\n";
  if N eq 1 then
        return [O];
    end if;
  Js := IdealsUpTo(N, O);
    result := [];
    // Js are ordered by norm, and we only care about the ones with Norm = N * norm_I
  for J in Reverse(Js) do
    if Norm(J) eq N then
        Append(~result, J);
        else
              break;  //the other ideals in Js will have norm < N.
        end if;
  end for;
  return result;
end intrinsic;

intrinsic IdealsOfIndex(I::RngOrdIdl, N::RngIntElt) -> SeqEnum[RngOrdIdl]
{Given an ideal I in an order O in a number field and a positive integer N, with N coprime with the conductor, returns all the ideals J contained in I with index [I:J]=N.}
//by Edgar Costa
vprintf Ordersext : "IdealsOfIndex RngOrdIdl\n";
    if N eq 1 then
        return [I];
    end if;
    O := Order(I);
    OK := MaximalOrder(NumberField(O));
    index_OK_O := Index(OK, O);
    assert N gt 0 and GCD(index_OK_O, N) eq 1;
    Js := IdealsOfIndex(OK, N);
    ff:=OK !! Conductor(O);
    assert forall{J : J in Js | J+ff eq 1*OK};
      result := [];
    for J in Js do
            K := (O meet J) * I; // OK/J=O/(J meet O)=I/K, where the second isomorphism holds because (J meet O) is invertible in O, since it is coprime with ff.
            Append(~result, K);
    end for;
    return result;
end intrinsic;

intrinsic IdealsOfIndex(I::RngOrdFracIdl, N::RngIntElt) -> SeqEnum[RngOrdFracIdl]
{Given an ideal I in an order O in a number field and a positive integer N, with N coprime with the conductor, returns all the ideals J contained in I with index [I:J]=N.}
//by Edgar Costa
    vprintf Ordersext : "IdealsOfIndex Frac\n";
    if N eq 1 then
        return [I];
    end if;
    d := Denominator(I);
    dI := Order(I)!!(d*I);
    Js := IdealsOfIndex(dI, N);
    return [J/d : J in Js];
end intrinsic;

intrinsic IdealsOfIndexProduct(Is::Tup, N::RngIntElt) -> SeqEnum[Tup]
{Given a list Is of ideals representing the ideal I as a product and positive integer N, returns all the ideals of index N. N has to be coprime with the conductor.}
//by Edgar Costa
    vprintf Ordersext : "IdealsOfIndexProduct\n";
    if #Is eq 1 then
        return [<elt> : elt in IdealsOfIndex(Is[1], N)];
    end if;
    result := [];
    for d in Divisors(N) do
        J1 := IdealsOfIndex(Is[1], Integers()!(N/d));
        Jk := $$(<Is[i] : i in [2..#Is]>, d);
        if #J1 ge 0 and #Jk ge 0 then
            for c in CartesianProduct(J1, Jk) do
                assert #c[2] eq #Jk;
                Append(~result, <c[1]> cat c[2]);
            end for;
        end if;
    end for;
    return result;
end intrinsic;

intrinsic IdealsOfIndex(I::AlgAssVOrdIdl[RngOrd], N::RngIntElt : Al := "Default") -> SeqEnum[AlgAssVOrdIdl]
{Given an O-ideal I in O and integer N returns all the subideals J of I with index [I:J]=N.
 The function is very fast if N is coprime to the conductor of O. If this conditions are not satisfied a slow algorithm is used which doesn't require additional hypothesis.
 One can force the slow-naive by setting the vararg Al:="Naive".}
//by Edgar Costa
    if N eq 1 then
        return [I];
    end if;
    if Al eq "Naive" then
        test := false;
    else
        test, dec := IsProductOfIdeals(I);
        for J in dec do
            O := Order(J);
            OK := MaximalOrder(NumberField(O));
            index_OK_O := Index(OK, O);
            if GCD(index_OK_O, N) ne 1 then
                test :=false;
                break;
            end if;
        end for;
    end if;
    if test then
        Js := IdealsOfIndexProduct(dec, N);
        O := Order(I);
        A := Algebra(O);
        result := [];
        for J in Js do
            assert #J eq #dec;
            assert #J eq #A`NumberFields;
            gen_inA := [];
            for i := 1 to #J do
                L := A`NumberFields[i];
                gen_inA := gen_inA cat [L[2](y) : y in Basis(J[i], L[1])];
            end for;
            JA:= ideal<Order(I) | gen_inA>;
            assert Index(I,JA) eq N;
            Append(~result,JA);
        end for;
        return result;
    else
        result := [];
        vprintf Ordersext : "Naive version!!\n";
        // this is extremely NAIVE!!!
        S := MultiplicatorRing(I);
        zbasis := ZBasis(I);
        r := #zbasis;
        F := FreeAbelianGroup(r);
        // converte it to a Finite presented group
        FP, f := FPGroup(F); //f:FP->F

        // all subrgroups of index N of ZZ^r
        subg := LowIndexProcess(FP, <N, N>); // k in [N, N]
        while not IsEmpty(subg) do
            // pulling back the abstract subgroup of index N to J
            H := ExtractGroup(subg);
            NextSubgroup(~subg);
            geninF := [f(FP ! x) : x in Generators(H)];
            coeff := [Eltseq(x) : x in geninF];
            // H is a subgroup of J of index N, but as fractional ideal the index might not be N
            J := ideal<S| [&+[zbasis[i]*x[i] : i in [1..r]] : x in coeff]>;
            if Index(I, J) eq N then
              assert J subset I;
              Append(~result, J);
            end if;
        end while;
        return result;
    end if;
end intrinsic;
