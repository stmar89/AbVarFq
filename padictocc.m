// Must change lines 2010, 2132, and 2247 of 
//     package/Ring/GaloisGroup/Galois.m
// to read "prec := 20" (instead of 'prec := 1').
// The assumption made is that the prime chosen for the p-adic computation
// is unramified, so every root is a unit root.  :(

intrinsic pAdicToComplexRootsGMod(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -> 
    SeqEnum[RngPadElt], SeqEnum[FldComElt], GrpPerm
  {Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection is G-equivariant, and the Galois group G.  
   The varargs precpAdic and precCC specify output 
   padic and complex precision.}

  n := Degree(f);
  if precpAdic ne 0 then
    // refine padic roots
    // rtsp := [GaloisRoot(f,i,datp : Prec := precpAdic) : i in [1..n]];
    Gp, rtsp, datp := GaloisGroup(f : Prime := p, Prec := precpAdic);
  else
    Gp, rtsp, datp := GaloisGroup(f : Prime := p);
  end if;
  GCC, rtsCC, datCC := GaloisGroup(f : Type := "Complex", Prec := precCC);
  
  Sn := Sym(n);
  _, tau := IsConjugate(Sn,Gp,GCC);
  //rtsptau := [rtsp[i^(tau)] : i in [1..n]];
  rtsptau := [rtsp[i^(tau^-1)] : i in [1..n]];
      // it's either this or rtsCCtau!  :)
      // I thought it should be i^tau, 
      // because the tau above gives Gp^tau = tau^-1*Gp*tau = GCC, so
      // for the action we want (i^tau)^(tau^-1*sigma*tau) = (i^sigma)^tau. 
      // But we need to take tau^-1 to get integral relative invariants below,
      // so I must be misunderstanding something.

  G := GCC;
  NG := Normalizer(Sn,G);
  NGmodG, mN := quo<Normalizer(Sn,G) | G>;
  rhos := [c@@mN : c in NGmodG];
  
  if #rhos eq 1 then 
    return rtsptau, rtsCC, G;
  end if;

  Finv := RelativeInvariant(NG,G);
  pvals := [Evaluate(Finv,[rtsptau[i^rho] : i in [1..n]]) : rho in rhos];
  assert #SequenceToSet(pvals) eq #rhos;   // possible precision issue
    // if not, need to increase p-adic precision or 
    // possibly make a change of variables in f to land in a nonempty Zariski open subset
  d := Degree(Universe(pvals));
  pval := Roots(PowerRelation(Trace(pvals[1])/d,1),Integers())[1][1];  
    // assumes invariant is integral
  
  CCvals := [Abs(Evaluate(Finv,[rtsCC[i^rho] : i in [1..n]])-pval) : rho in rhos];
  minval, minind := Min(CCvals);
  assert minval lt 10^(-Precision(Universe(rtsCC))/2);     // possible precision issue
  assert #[c : c in CCvals | c le minval] eq 1;    // possible precision issue
    // if one of these fails, need to increase complex precision
  rho := rhos[minind];
  rtsCCrho := [rtsCC[i^rho] : i in [1..n]];
  return rtsptau, rtsCCrho, GCC;
end intrinsic;

intrinsic pAdicToComplexRoots(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -> 
    SeqEnum[RngPadElt], SeqEnum[FldComElt], GrpPerm
  {Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection arises from roots in a splitting field over 
   the rationals.  The varargs precpAdic and precCC specify (minimum) output 
   padic and complex precision.}

  n := Integers()!(Degree(f)/2);
  R<x> := PolynomialRing(Rationals());
  _, q := IsPower(Coefficient(f,0),n);
  assert q eq p^(Valuation(q,p));
  Rf := quo<R | f>;
  fred := Sqrt(CharacteristicPolynomial(Rf.1 + q/Rf.1));
  F := SplittingField(fred);
  if Degree(F) eq 1 then
    F := RationalsAsNumberField();
  end if;
  rtsF := Roots(fred,F);
  assert {r[2] : r in rtsF} eq {1}; // squarefree condition
  rtsF := [r[1] : r in rtsF];

  if precpAdic eq 0 then
    ZZp := pAdicRing(p);
  else
    ZZp := pAdicRing(p,precpAdic);
  end if;
  try
    Kp := FieldOfFractions(SplittingField(f,ZZp));  // returns a ring, go figure!
  catch e
    // insufficient padic precision
    prec := Max(precpAdic,20);
    success := false;
    repeat
      prec +:= 20;
      ZZp := pAdicRing(p,prec);
      try
        Kp := FieldOfFractions(SplittingField(f,ZZp));  // returns a ring, go figure!
        success := true;
      catch e;
      end try;
    until success;
  end try;    
  
  // for each root alpha of fred, we have two roots beta of f satisfying
  // beta^2 - alpha*beta + q = 0  [since beta + q/beta = alpha]
  // let d = disc = alpha^2-4*q; 
  // we need to keep track of the square classes of the discriminants,
  // when we see a new one we choose an embedding, when we have an old
  // one we use previous embedddings
  rtsCC := [];
  rtsp := [];
  alpha1 := rtsF[1];
  K1 := ext<F | Polynomial([q,-alpha1,1])>;
  Ks := [K1];
  v1 := InfinitePlaces(K1)[1];
  vs := [* v1 *];
  mu1p := [r[1] : r in Roots(MinimalPolynomial(F.1),Kp)][1];  // take first one, it's a choice
  mF1p := map<F -> Kp | u :-> &+[(F!u)[i+1]*mu1p^i : i in [0..Degree(F)-1]]>;
  assert IsWeaklyZero(Evaluate(MinimalPolynomial(F.1),mF1p(F.1))); // sanity check
  beta1p := [r[1] : r in Roots(Polynomial([q,-mF1p(alpha1),1])) | Valuation(r[1]) eq 0][1];
  mK1qq := map<K1 -> Kp | u :-> mF1p((K1!u)[1]) + mF1p((K1!u)[2])*beta1p>;
  qqs := [* mK1qq *];
  Append(~rtsp, beta1p);
  if precCC eq 0 then
    beta1CC := Evaluate(K1.1, v1); // use default
  else
    beta1CC := Evaluate(K1.1, v1 : Precision := precCC);
  end if;
  Append(~rtsCC, beta1CC);
  embedded_discs := [<alpha1^2-4*q, beta1CC-q/beta1CC, beta1p-q/beta1p>];
    // first one is arbitrary, guaranteed to be irreducible because has complex place
  
  for j := 2 to n do
    alphaj := rtsF[j];
    dj := alphaj^2-4*q;
    embfound := false;
    for dexps in CartesianPower([0,1],#embedded_discs) do
      ed := &*[embedded_discs[i][1]^dexps[i] : i in [1..#dexps]];
      bl, csq := IsSquare(dj/ed);
      if bl then
        // can use existing embedding: betaj = (alphaj + sqrt(d_j))/2
        // so sqrt(d_j) = csq*sqrt(ed), so to speak
        dv := &*[embedded_discs[i][2]^dexps[i] : i in [1..#dexps]];
        dqq := &*[embedded_discs[i][3]^dexps[i] : i in [1..#dexps]];
        betajp := (mF1p(alphaj)+mF1p(csq)*dqq)/2;
        betajCC := (Evaluate(alphaj,v1) + Evaluate(csq,v1)*dv)/2;
        if Valuation(betajp) gt 0 then
          betajp := q/betajp;
          betajCC := q/betajCC;
        end if;
        assert Valuation(betajp) eq 0;
        Append(~rtsp, betajp);
        Append(~rtsCC, betajCC);
        embfound := true;
        break;
      end if;
    end for;
    if not embfound then
      Kj := ext<F | Polynomial([q,-alphaj,1])>;
      Append(~Ks, Kj);
      vj := InfinitePlaces(Kj)[1];
      Append(~vs, vj);
      betajp := [r[1] : r in Roots(Polynomial([q,-mF1p(alphaj),1])) | Valuation(r[1]) eq 0][1];
      mKjqq := map<Kj -> Kp | u :-> mF1p((Kj!u)[1]) + mF1p((Kj!u)[2])*betajp>;
      Append(~qqs, mKjqq);
      Append(~rtsp, betajp);
      if precCC eq 0 then
        betajCC := Evaluate(Kj.1, vj); // use default
      else
        betajCC := Evaluate(Kj.1, vj : Precision := precCC);
      end if;
      Append(~rtsCC, betajCC);
      Append(~embedded_discs, <alphaj^2-4*q, betajCC-q/betajCC, betajp-q/betajp>);
    end if;
  end for;  
  
  return rtsp cat [q/r : r in rtsp], rtsCC cat [q/r : r in rtsCC];
end intrinsic;

/*
// IGNORE ME: tried something that is too elaborate
intrinsic ComplexRootsWithPositiveValuation(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -> 
    RngUPolElt, SeqEnum[FldComElt]
  {Given an ordinary p-Weil polynomial (half unit roots, half positive valuation)
   return a polynomial over a complex quadratic field whose complex roots
   correspond to the set of p-adic roots with positive valuation, and
   the complex roots.
   The varargs precpAdic and precCC specify the padic precision used.}
   
  assert IsSquarefree(f);  
    // not implemented since we haven't gotten to this case yet; 
    // we can handle the nonsquarefree case by just keeping track of multiplicities
  n := Integers()!(Degree(f)/2);  // need an even degree polynomial, yo!
  if precpAdic eq 0 then
    precpAdic := 20;
  end if;
  escaped := false;
  repeat
    try
      R0 := pAdicRing(p,precpAdic);
      F0 := FieldOfFractions(R0);
      R := SplittingField(f,R0);  // returns a ring, go figure!
      F := FieldOfFractions(R);
      rts := Roots(f,R);
      assert &and[r[2] eq 1 : r in rts];  // need distinct roots
      rts0 := [r[1] : r in rts | Valuation(r[1]) eq 0];
      rts1 := [r[1] : r in rts | Valuation(r[1]) gt 0];
      assert #{Valuation(r) : r in rts1} eq 1;  // sanity check all have same valuation
      g0s := [];
      g1s := [];
      cfsgs := [];
      _<x> := PolynomialRing(R);
      for c in CartesianPower([0,1],n-1) do
        rtsc0 := [rts0[1]];
        rtsc1 := [rts1[1]];
        for i := 1 to n-1 do
          if c[i] eq 0 then 
            Append(~rtsc0, rts0[i+1]);
            Append(~rtsc1, rts1[i+1]);
          else 
            Append(~rtsc0, rts1[i+1]);
            Append(~rtsc1, rts0[i+1]);
          end if;
        end for;
        g0 := &*[x-r : r in rtsc0];
        g1 := &*[x-r : r in rtsc1];
        Append(~g0s, g0);
        Append(~g1s, g1); 
        cfs0 := Coefficients(g0);
        cfs1 := Coefficients(g1);
        Append(~cfsgs, [(x-cfs0[i])*(x-cfs1[i]) : i in [1..n+1]]);
      end for;
      
      f0 := &*[x-r : r in rts0];
      f1 := &*[x-r : r in rts1]; // we have f = f0*f1 over QQ, so these are quadratic conjugate
      n := Degree(f) div 2; // assert Degree(f) mod 2 eq 0;
      giQQs := [];
      g := 0;
      for i := 0 to n do
        cfs := [Coefficient(f0,i), Coefficient(f1,i)];
        gi := (x-Coefficient(f0,i))*(x-Coefficient(f1,i));
        giQQ := Polynomial([Roots(PowerRelation(F0!c,2),Rationals())[1][1] : c in Coefficients(gi)]);
        if IsIrreducible(giQQ) then
          if g eq 0 then
            g := giQQ;
            Q<gamma> := NumberField(g);
          end if;
        end if;
        Append(~giQQs, giQQ);
      end for;
      // g is assigned, or I don't understand CM!
      assert g ne 0;
      ZQ := Integers(Q);
      iota := hom<Q -> F | Roots(g,F)[1][1]>;
      f1cfs := [];
      for i := 0 to n do
        cfs := [r[1] : r in Roots(giQQs[i+1],Q)];
        maxval, jind := Max([Valuation(Coefficient(f1,i)-iota(cfs[j])) : j in [1..#cfs]]);
        Append(~f1cfs, cfs[jind]);
      end for;
      gQ := Polynomial(f1cfs);
      escaped := true;
    catch e
      precpAdic +:= 20;
      if precpAdic gt 1000 then
        error e;
      end if; 
    end try;
  until escaped;
  v := InfinitePlaces(Q)[1];
  if precCC ne 0 then
    gCC := [Evaluate(c,v : Precision := precCC) : c in Eltseq(gQ)];
  else
    gCC := [Evaluate(c,v) : c in Eltseq(gQ)];
  end if;
  rtsCC := [r[1] : r in Roots(Polynomial(gCC))];
  
  return gQ, rtsCC;
end intrinsic;
*/


/*
Attach("padictocc.m");
_<x> := PolynomialRing(Rationals());
f := x^8 - 5*x^7 + 12*x^6 - 20*x^5 + 29*x^4 - 40*x^3 + 48*x^2 - 40*x + 16;  p := 2;
// f := x^6 + 2*x^4 + 11*x^3 + 10*x^2 + 125;  p := 5;

n := Degree(f);
L := SplittingField(f);
rts1L := [r[1] : r in Roots(f,L)];
rts1CC := [Evaluate(r,InfinitePlaces(L)[1]) : r in rts1L];  // some choice of complex embedding
precCC := Precision(Universe(rts1CC));
rts2pp, rts2CC, G := pAdicToComplexRoots(f,p);
Lpp := FieldOfFractions(Universe(rts2pp));
iotapp := hom<L -> Lpp | Roots(MinimalPolynomial(L.1),Lpp)[1][1]>;
rts1pp := [iotapp(r) : r in rts1L];
sigmapp := Sym(n)![c[2] : c in [<i,j> : i,j in [1..n] | IsWeaklyZero(rts1pp[i]-rts2pp[j])]];
sigmaCC := Sym(n)![c[2] : c in [<i,j> : i,j in [1..n] | Abs(rts1CC[i]-rts2CC[j]) lt 10^(-9/10*precCC)]];
sigmaCC^-1*sigmapp in G;

rts1Ltau := [rts1L[i^(sigmaCC^-1)] : i in [1..n]];
rts1CCtau := [Evaluate(r,InfinitePlaces(L)[1]) : r in rts1Ltau];
rts1pptau := [iotapp(r) : r in rts1Ltau];
sigmapptau := Sym(n)![c[2] : c in [<i,j> : i,j in [1..n] | IsWeaklyZero(rts1pptau[i]-rts2pp[j])]];
sigmaCCtau := Sym(n)![c[2] : c in [<i,j> : i,j in [1..n] | Abs(rts1CCtau[i]-rts2CC[j]) lt 10^(-9/10*precCC)]];
sigmapptau;
sigmaCCtau;
sigmapptau in G;
*/
