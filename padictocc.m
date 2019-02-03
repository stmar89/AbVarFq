// Must change lines 2010, 2132, and 2247 of 
//     package/Ring/GaloisGroup/Galois.m
// to read "prec := 20" (instead of 'prec := 1').
// The assumption made is that the prime chosen for the p-adic computation
// is unramified, so every root is a unit root.  :(

intrinsic pAdicToComplexRoots(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -> 
    SeqEnum[RngPadElt], SeqEnum[FldComElt], GrpPerm
  {Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection is G-equivariant, and the Galois group G.  
   The varargs precpAdic and precCC specify output 
   padic and complex precision.}

  n := Degree(f);
  Gp, rtsp, datp := GaloisGroup(f : Prime := p);
  if precpAdic ne 0 then
    // refine padic roots
    rtsp := [GaloisRoot(f,i,datp : Prec := precpAdic) : i in [1..n]];
  end if;
  GCC, rtsCC, datCC := GaloisGroup(f : Type := "Complex", Prec := precCC);
  
  Sn := Sym(n);
  _, tau := IsConjugate(Sn,Gp,GCC);
  rtsptau := [rtsp[i^(tau^-1)] : i in [1..n]];
  //rtsCCtau := [rtsCC[i^tau] : i in [1..n]];
      // it's either this or rtsCCtau!  :)

  G := GCC;
  NGmodG, mN := quo<Normalizer(Sn,G) | G>;
  rhos := [c@@mN : c in NGmodG];
  
  if #rhos eq 1 then 
    return rtsptau, rtsCC, G;
  end if;

  Finv := RelativeInvariant(Sn,G);
  pvals := [Evaluate(Finv,[rtsptau[i^rho] : i in [1..n]]) : rho in rhos];
  assert #SequenceToSet(pvals) eq #rhos;   // possible precision issue
    // if not, need to increase p-adic precision or 
    // possibly make a change of variables in f to land in a nonempty Zariski open subset
  pval := Integers()!pvals[1];  // assumes invariant is integral
  
  CCvals := [Abs(Evaluate(Finv,[rtsCC[i^rho] : i in [1..n]])-pval) : rho in rhos];
  minval, minind := Min(CCvals);
  assert minval lt 10^(-Precision(Universe(rtsCC))/2);     // possible precision issue
  assert #[c : c in CCvals | c le minval] eq 1;    // possible precision issue
    // if one of these fails, need to increase complex precision
  rho := rhos[minind];
  rtsCCrho := [rtsCC[i^rho] : i in [1..n]];
  return rtsptau, rtsCCrho, GCC;
end intrinsic;

/*
Attach("padictocc.m");
_<x> := PolynomialRing(Rationals());
f := x^8 - 5*x^7 + 12*x^6 - 20*x^5 + 29*x^4 - 40*x^3 + 48*x^2 - 40*x + 16;
p := 2;

L := SplittingField(f);
rts1L := [r[1] : r in Roots(f,L)];
rts1CC := [Evaluate(r,InfinitePlaces(L)[1]) : r in rts1L];  // some choice of complex embedding
rts2pp, rts2CC, G := pAdicToComplexRoots(f,p);
Lpp := FieldOfFractions(Universe(rts2pp));
iotapp := hom<L -> Lpp | Roots(MinimalPolynomial(L.1),Lpp)[1][1]>;
rts1pp := [iotapp(r) : r in rts1L];
sigmapp := Sym(8)![c[2] : c in [<i,j> : i,j in [1..8] | IsWeaklyZero(rts1pp[i]-rts2pp[j])]];
sigmaCC := Sym(8)![c[2] : c in [<i,j> : i,j in [1..8] | IsWeaklyZero(rts1CC[i]-rts2CC[j])]];
*/