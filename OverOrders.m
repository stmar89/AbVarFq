
intrinsic pMaximalOrder(O::AlgAssVOrd, p::RngIntElt) -> AlgAssVOrd
{given O, retuns the maximal p over order}
  if (Norm(Discriminant(O)) mod p^2) ne 0 then
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

intrinsic ResidueField(P::AlgAssVOrdIdl) -> FldFin, Map
{ given P a prime of S, returns a finite field F isomorphic to S/P and a surjection (with inverse) S->F.}
	//assert IsPrime(P);
	S := Order(P);
	Q,q := ResidueRing(S,P); //q:S->S/P
	size := #Q;
	F := FiniteField(size);
	min_poly := PolynomialRing(Integers())!DefiningPolynomial(F);
	//the following loop is naive
	for y in Q do
		if q(Evaluate(min_poly,y@@q)) eq Zero(Q) then
			prim_elt_inQ := y;
			prim_elt_inA := y@@q;
			break y;
		end if;
	end for;
	//now I need to build  the map
	G,gGF := AdditiveGroup(F); //g:G->F
	hGQ := iso<G->Q | [q(prim_elt_inA^i) : i in [0..Degree(min_poly)-1]]>;
	hQG := Inverse(hGQ);
	map := q*hQG*gGF;
	return F, map;
end intrinsic;

intrinsic QuotientVS(I::AlgAssVOrd, J::AlgAssVOrd, P::AlgAssVOrdIdl, K::FldFin, k::Map) -> ModFld, Map
{
 let I, J, P be fractional R-ideals such that:
 - P is prime with residue field K;
 - k the map
 - J in I and I/J is a vector space over R/P, say of dimension d;
 the function returns the KModule K^d and a lift map F^d->I
}
	S := Order(P);
	A := Algebra(S);
	//assert Order(I) eq S and Order(J) eq S;
	//assert IsPrime(P);
	//assert (P*I) subset J;
	//K,k := residue_field(P);
	d := Ilog(#K,Integers() ! Index(I,J));
	V := KModule(K,d);
	//need to find a basis of I/J over R/P.
	zbI := ZBasis(I);
	N := #zbI;
	F := FreeAbelianGroup(N);
	rel := [F ! cc : cc in Coordinates(ZBasis(J),zbI)];
	mFI := map<F->A| x:->&+[Eltseq(x)[i]*zbI[i] : i in [1..N]]>;
	mIF := map<A->F| x:-> F ! Eltseq(Coordinates([x],zbI)[1])>;
	Q0,q0 := quo<F|rel>; //q0:F->Q
	bas := [];
	Q := Q0;
	q := q0;
	for i in [1..d] do
		elt_F := (Q.1@@q);
		elt_I := mFI(elt_F);
		Append(~bas,elt_I);
		rel := rel cat [mIF(bb) : bb in ZBasis(ideal<S|elt_I>)];
		Q, q := quo<F|rel>; //q:F->Q
	end for;
	assert IsTrivial(Q);
	//assert ideal<S| bas cat ZBasis(J)> eq I;
	//now we build the map
	/*mIV := function(x)
	     end function;*/
	mVI := function(y)
		return &+[ bas[j]*(Eltseq(y)[j]@@k) : j in [1..d] ];
  end function;
	return V, map<V->A | x:->mVI(x)>;
end intrinsic;


intrinsic MinimalOverOrders(R::AlgAssVOrd : singular_primes := [], orders := {@ @}) -> SetIndx[AlgAssVOrd]
{ returns the minimal over orders of R given the singular primes of R }
  if not assigned R`MinimalOverOrders then
    min_oo := { };
    if not IsMaximal(R) then
      zbR := ZBasis(R);
      if singular_primes ne [] then
        pp := [(R!P) meet (ideal<R|1>) : P in singular_primes];
        pp := [P : P in pp | Index(P, P*P) ne Index(R,P)]; //only the sing ones
        pp := Setseq(Seqset(pp)); //remove duplicates
        //assert SequenceToSet(pp) eq SequenceToSet(PrimesAbove(Conductor(R)));
      else
        pp := PrimesAbove(Conductor(R));
      end if;
      for P in pp do
        pot_min_oo := {@ @};
        F, f := ResidueField(P);
        T := MultiplicatorRing(P);
        //idT := ideal<R|ZBasis(T)>;
        //V,mVT := quotient_as_vector_space(idT,ideal<R|1>,P,F,f); //trying to speed up
        V,mVT := QuotientVS(T, R, P, F, f);
        d := Dimension(V);
        //see Proposition 5.3 of Tommy's paper
        if d eq 1 then
          Include(~min_oo, T);
        else
          dims := PrimesUpTo(d);
          subs := Submodules(V : CodimensionLimit := d-1); //only subs of dim a prime number
          subs := [W : W in subs | Dimension(W)+1 in dims];
          //the +1 comes from using (P:P)/R instead of (P:P)/P, see Remark 5.4
        //TODO: add special test for W of dim 1, which needs a map idT->V, not implemented yet
          for W in subs do
            S := Order([mVT(w) : w in Basis(W)] cat zbR);
            Include(~pot_min_oo,S);
          end for;
          //we remove non-minimals
          for S in pot_min_oo do
            if not exists {T : T in pot_min_oo | S ne T and T subset S} then
              Include(~min_oo, S);
            end if;
          end for;
        end if;
      end for;
    end if;
    R`MinimalOverOrders := {@ @};
    for S in min_oo do
      i := Index(orders, S);
      if i eq 0 then
        Include(~R`MinimalOverOrders, S);
      else
        Include(~R`MinimalOverOrders, orders[i]);
      end if;
    end for;
  end if;
  return R`MinimalOverOrders;
end intrinsic;



intrinsic FindOverOrders_Minimal(R::AlgAssVOrd) -> SetIndx[AlgAssVOrd]
{ given an order R returns all the over orders }
  A := Algebra(R);
  require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
  //it faster to recompute them
  // O := MaximalOrder(A);
  // singular_primes := PrimesAbove(O!Conductor(R));
  singular_primes := [];
  queue := {@ R @};
  done := {@  @};
  output := {@ @};
  while #queue gt 0 do
    output join:=  queue;
    done join:= queue;
    for elt in queue do
      output join:= MinimalOverOrders(elt : singular_primes := singular_primes, orders := output);
    end for;
    queue := output diff done;
  end while;
  return output;
end intrinsic;


intrinsic FindOverOrders(E::AlgAssVOrd: alg := "minimal", populateoo_in_oo := false) -> SetIndx[AlgAssVOrd]
{returns all the overorders of E, and populates }
  require alg in ["minimal", "naive"]: "only naive and minimal options are supported";
  if not assigned E`OverOrders then
    if alg eq "minimal" then
      E`OverOrders := FindOverOrders_Minimal(E);
      //for S in E`MinimalOverOrders do
      //  _ := FindOverOrders(S: alg := "minimal");
      //end for;
    elif alg eq "naive" then
      E`OverOrders := FindOverOrders_Naive(E);
    end if;
  end if;

  // there might be a better way to do this
  // like looping over MaximalUnderOrders
  if populateoo_in_oo then
    for i in [1..#E`OverOrders] do
      S := E`OverOrders[i];
      if not assigned S`OverOrders then
        S`OverOrders := {@ T : T in E`OverOrders | S subset T @};
      end if;
    end for;
  end if;
  return E`OverOrders;
end intrinsic;



intrinsic FindOverOrders(E::AlgAssVOrd, O::AlgAssVOrd) -> SetIndx[AlgAssVOrd]
{given E subset O, returns the sequence of orders between E and O}
//15/02/2018 we add the LowIndexProcess
	require IsFiniteEtale(Algebra(E)): "the algebra of definition must be finite and etale over Q";
	require E subset O : "the first argument must be a subset of the second";
  return {@ S: S in FindOverOrders(E) | S subset O @};
end intrinsic;




intrinsic FindOverOrders_Naive(E::AlgAssVOrd) -> SetIndx[AlgAssVOrd]
{returns all the overorders of E}
  A := Algebra(E);
  require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
  if assigned A`MaximalOrder then
    O := A`MaximalOrder;
  else
    O := MaximalOrder(A);
    A`MaximalOrder := O;
  end if;
  if O eq E then
    return [E];
  end if;
  return FindOverOrders_Naive(E,O);
end intrinsic;

intrinsic FindOverOrders_Naive(E::AlgAssVOrd, O::AlgAssVOrd) -> SetIndx[AlgAssVOrd]
{given E subset O, returns the sequence of orders between E and O}
//15/02/2018 we add the LowIndexProcess
	require IsFiniteEtale(Algebra(E)): "the algebra of definition must be finite and etale over Q";
	require E subset O : "the first argument must be a subset of the second";
  F := FreeAbelianGroup(Degree(O));
  E_ZBasis := ZBasis(E);
  O_ZBasis := ZBasis(O);
  rel := [F ! Eltseq(x) : x in Coordinates(E_ZBasis, ZBasis(O))];
  Q,q := quo<F|rel>; //q:F->Q quotient map
  FP,f := FPGroup(Q); //f:FP->Q isomorphism
  N := #FP;
  subg := LowIndexProcess(FP,<1,N>);
  seqOO := {@ @};
  while not IsEmpty(subg) do
    H := ExtractGroup(subg);
    NextSubgroup(~subg);
    geninF := [(f(FP ! x))@@q : x in Generators(H)];
    coeff := [Eltseq(x) : x in geninF];
    S := Order([&+[O_ZBasis[i]*x[i] : i in [1..Degree(Algebra(O))]] : x in coeff] cat E_ZBasis);
    if S ne O then
      Include(~seqOO, S);
    end if;
  end while;
  Include(~seqOO,O); //in this way O is the last of the list
  assert E in seqOO and O in seqOO;
  return seqOO;
end intrinsic;
