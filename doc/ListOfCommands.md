## List of instrinsics in ./IsogenyClasses.m:

> <pre><b>IsWeil</b>(f::RngUPolElt : Precision:=30) -> BoolElt,RngIntElt,RngIntElt,RngIntElt</pre>
<em>Returns whether f is a q-WeilPolynomial, q,p and e, where q=p^e is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "Precision" given as optional parameter (default precision is 30)</em>

> <pre><b>IsCharacteristicPoly</b>(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt</pre>
<em>Given polynomial f, returns whether f is the characteristic polynomial of Frobenius of some isogeny class, together with the minimal exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].</em>

> <pre><b>IsogenyClass</b>( h::RngUPolElt : Check:=true ) -> IsogenyClassFq</pre>
<em>Given a WeilPolynomial h creates the isogeny class determined by h via Honda-Tate theory. The Check parameter (Default true) allows to decide whether to test if the polynomial defines an isogeny class (see IsCharacteristicPoly).</em>

> <pre><b>WeilPolynomial</b>( I::IsogenyClassFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the Weil polynomial h defining it.</em>

> <pre><b>WeilPolynomialFactorization</b>( I::IsogenyClassFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the factorization over Q of Weil polynomial h defining it.</em>

> <pre><b>ZFVOrder</b>(I::IsogenyClassFq)-> AlgEtQOrd,Map</pre>
<em>Given an isogeny class AV(h) defined by the Weil polynomial h with factorization over Q equal to h=g1^s1\*...\*gn^sn, returns the order Z[F,q/F]  in the algebra Q[F]=Q[x]/g where g = prod_i gi.</em>

> <pre><b>FiniteField</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the size of the finite field of definition.</em>

> <pre><b>CharacteristicFiniteField</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the characteristic of the finite field of definition.</em>

> <pre><b>Dimension</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the dimension.</em>

> <pre><b>NumberOfPoints</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the number of rational points of the abelian varities in the isogeny class.</em>

> <pre><b>IsSquarefree</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is squarefree.</em>

> <pre><b>IsPurePower</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is a pure power.</em>

> <pre><b>IsPowerOfBass</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is a pure power and ZFV is a Bass Order.</em>

> <pre><b>Print</b>(I::IsogenyClassFq)</pre>
<em>Prints the isogeny class.</em>

> <pre><b>'eq'</b>(AVh1::IsogenyClassFq , AVh2::IsogenyClassFq ) -> BoolElt</pre>
<em>Checks if the Weil polynomials are the same. It controls that the Universe algbras and ZFV orders are equal as well (to avoid double definitions).</em>

> <pre><b>IsOrdinary</b>(AVf::IsogenyClassFq) -> BoolElt</pre>
<em>Returns if the isogeny class is ordinary.</em>

> <pre><b>IsOrdinary</b>(A::AbelianVarietyFq) -> BoolElt</pre>
<em>Returns if the abelian variety is ordinary.</em>

> <pre><b>IsOrdinary</b>(f::RngUPolElt : Precision:=100) -> BoolElt</pre>
<em>Returns if the input polynomial is an Ordinary q-Weil polynomial, where q is a power of a prime number p, that is if the mid coefficient is coprime with p.</em>

> <pre><b>pRank</b>(I::IsogenyClassFq)->RngIntElt</pre>
<em>Returns the p-Rank of the isogeny class.</em>

> <pre><b>pRank</b>(A::AbelianVarietyFq)->RngIntElt</pre>
<em>Returns the p-Rank of the isogeny class.</em>

> <pre><b>IsAlmostOrdinary</b>(I::IsogenyClassFq)->BoolElt</pre>
<em>Returns whether the isogeny class is almost ordinary.</em>

> <pre><b>IsAlmostOrdinary</b>(A::AbelianVarietyFq)->BoolElt</pre>
<em>Returns whether the abelian variety is almost ordinary.</em>

> <pre><b>IsCentelegheStix</b>(I::IsogenyClassFq : Precision:=30 )->BoolElt</pre>
<em>Returns whether the isogeny class is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.</em>

> <pre><b>IsCentelegheStix</b>(I::AbelianVarietyFq : Precision:=30 )->BoolElt</pre>
<em>Returns whether the abelian variety is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.</em>

> <pre><b>LPolyToWeilPoly</b>(l::RngUPolElt) -> RngUPolElt</pre>
<em>given an L-polynomial l(T) returns the associated Weil polynomial w(T):=T^(2g)\*l(1/T)</em>

> <pre><b>WeilPolyToLPoly</b>(w::RngUPolElt) -> RngUPolElt</pre>
<em>given a Weil polynomial w(T) returns the associated L-polynomial l(T):=T^(2g)\*l(1/T)</em>


## List of instrinsics in ./AbVarAttr.m:

> <pre><b>Print</b>(I::AbelianVarietyFq)</pre>
<em>print the abelian variety</em>

> <pre><b>IsogenyClass</b>( A::AbelianVarietyFq) -> IsogenyClassFq</pre>
<em>Returns the isogeny class of the given abelian variety.</em>

> <pre><b>WeilPolynomial</b>(A::AbelianVarietyFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the Weil polynomial h defining it.</em>

> <pre><b>FiniteField</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the size of the finite field of definition.</em>

> <pre><b>CharacteristicFiniteField</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the characteristic of the finite field of definition.</em>

> <pre><b>Dimension</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the dimension.</em>

> <pre><b>ZFVOrder</b>( A :: AbelianVarietyFq) -> AlgEtQOrd,Map</pre>
<em>Returns the ZFV of the isogeny class of A.</em>


## List of instrinsics in ./DeligneModules.m:

> <pre><b>DeligneAlgebra</b>( I::IsogenyClassFq )-> AlgEtQ,Map</pre>
<em>Given an isogeny class AV(h), defined by the Weil polynomial h with factorization over Q equal to h=g1^s1\*...\*gn^sn, it returns the algebra V=prod_i=1^n (Q[x]/gi)^si, where the DeligneModules live, together with the componentwise diagonal action of ZFV</em>

> <pre><b>FrobeniusEndomorphismOnDeligneAlgebra</b>(I::IsogenyClassFq)-> Map</pre>
<em>Given an isogeny class AV(h) returns the Frobenius endomorphism (acting on the DeligneAlgebra).</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>(AVh::IsogenyClassFq,M::AlgEtQMod)->AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a Z[F,V]-module M. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , I::AlgEtQIdl )->AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a fractional ideal I of the Z[F,V] order of the isogeny class AV(h), where h is the characteristic polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQIdl] )-> AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a direct sum of s fractional ideals of the Z[F,V] order of the isogeny class AV(g^s), where g is the miniml polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQElt] )-> AbelianVarietyFq</pre>
<em>Returns the abelian variety defined defined by the module generated by the elements in seq. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>(AVh::IsogenyClassFq,seq::SeqEnum[Tup])->AbelianVarietyFq</pre>
<em>Given an isogeny class and sequence of pairs  <J_i,v_i> returns the abelin variety in the given isogeny class defined by the Deligne Module J_1v_1+...+J_sv_s. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>DeligneModule</b>(A :: AbelianVarietyFq)->AlgEtQMod</pre>
<em>Returns the DeligneModule defining the variety A.</em>

> <pre><b>DeligneAlgebra</b>( A :: AbelianVarietyFq) -> AlgEqQ</pre>
<em>Returns the DeligneAlgebra where the DeligneModule lives in.</em>

> <pre><b>'eq'</b>( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt</pre>
<em>Checks if two abelin varieties are equal, using the appropriate categorical description.</em>


## List of instrinsics in ./DualVar.m:

> <pre><b>DualAbelianVariety</b>(A::AbelianVarietyFq)->AbelianVarietyFq</pre>
<em>Given an abelian variety A returns the dual abelian variety. The isogeny class needs to be ordinary or Centelghe-Stix.</em>


## List of instrinsics in ./Ends.m:

> <pre><b>EndomorphismRing</b>(A::AbelianVarietyFq)-> AlgEtQOrd</pre>
<em>Returns Endomorphism ring of the abelian variety.</em>


## List of instrinsics in ./IsomClassesDM.m:

> <pre><b>IsIsomorphic</b>(A1::AbelianVarietyFq,A2::AbelianVarietyFq) -> BoolElt,HomAbelianVarietyFq</pre>
<em>Checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism.</em>

> <pre><b>IsomorphismClasses</b>( AVh::IsogenyClassFq )->SeqEnum[AbelianVarietyFq]</pre>
<em>Computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class.</em>


## List of instrinsics in ./RationalPoints.m:

> <pre><b>RationalPoints</b>(A::AbelianVarietyFq,r::RngIntElt)-> GrpAb</pre>
<em>Given an abelian variety over Fq, it returns the group of rational points defined over Fq^r.</em>

> <pre><b>RationalPoints</b>(A::AbelianVarietyFq)-> GrpAb</pre>
<em>Given an abelian variety over Fq, it returns the group of rational points defined over Fq.</em>


## List of instrinsics in ./HomDeligneModules.m:

> <pre><b>Print</b>(m::HomAbelianVarietyFq)</pre>
<em>print the morphism abelian variety</em>

> <pre><b>Domain</b>(m::HomAbelianVarietyFq)->AbelianVarietyFq</pre>
<em>returns the domain the morphism</em>

> <pre><b>Codomain</b>(m::HomAbelianVarietyFq)->AbelianVarietyFq</pre>
<em>returns the codomain the morphism</em>

> <pre><b>MapOnDeligneAlgebras</b>(m::HomAbelianVarietyFq)->Map</pre>
<em>returns underlying homormorphism of Deligne Moduels as a Z[F,V]-linear hom on the DeligneAlgebras</em>

> <pre><b>IsEndomorphism</b>(m::HomAbelianVarietyFq)->BoolElt</pre>
<em>returns whether the morphism is an endomorphism</em>

> <pre><b>Hom</b>(A::AbelianVarietyFq,B::AbelianVarietyFq,map::Map : Check:=true)->HomAbelianVarietyFq</pre>
<em>Creates a morphisms of abelian varieties A->B determined by map, where map is a morphisms of the DeligneAlgebras of A and B. The vararg Check allows to skip the test of the compatibility with the Frobenius.</em>

> <pre><b>FrobeniusEndomorphism</b>(A::AbelianVarietyFq)-> HomAbelianVarietyFq</pre>
<em>Returns the Frobenius endomorphism (acting on the DeligneAlgebra).</em>


## List of instrinsics in ./padictocc.m:

> <pre><b>pAdicToComplexRootsGMod</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection is G-equivariant, and the Galois group G.  
   The varargs precpAdic and precCC specify output 
   padic and complex precision.</em>

> <pre><b>pAdicToComplexRoots</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection arises from roots in a splitting field over 
   the rationals.  The varargs precpAdic and precCC specify (minimum) output 
   padic and complex precision.</em>

> <pre><b>ComplexRootsWithPositiveValuation</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Given an ordinary p-Weil polynomial (half unit roots, half positive valuation)
   return a polynomial over a complex quadratic field whose complex roots
   correspond to the set of p-adic roots with positive valuation, and
   the complex roots.
   The varargs precpAdic and precCC specify the padic precision used.</em>


## List of instrinsics in ./CMType.m:

> <pre><b>AllCMTypes</b>(AVh::IsogenyClassFq : precCC := 30 ) -> SeqEnum[AlgEtQCMType]</pre>
<em>Returns all the AlgEtQCMType of Algebra(ZFVOrder(AVh)).</em>

> <pre><b>pAdicPosCMType</b>(AVh::IsogenyClassFq : precpAdic := 30, precCC := 30 ) -> AlgEtQCMType</pre>
<em>Given an ordinary isogeny class AVh, it computes a AlgEtQCMType of the Algebra determined by the Frobenius of AVh such that the Frobenius has positive p-adic valuation according to some embedding of \barQp in C. The varargs precpAdic and precCC specify (minimum) output padic and complex precision.</em>


## List of instrinsics in ./IsogeniesPolarizations.m:

> <pre><b>IsogeniesManyOfDegree</b>(AIS::SeqEnum[AbelianVarietyFq], AJ::AbelianVarietyFq, N::RngIntElt) -> List</pre>
<em>Given a sequence of source squarefree abelian varieties AIS, a target sqaurefree abelian varity AJ and a positive integet N, it returns for each AI in AIS if there exist an isogeny AI->AJ of degree N. For each AI in AIS, if there exists and isogeny AI->AJ, it is also returned a list of representatives of the isomorphism classes of pairs [\*hom_x , K\*] where: hom_x:AI->AJ, and K=xI subset J, with I and J the fractional ideals representing AI and AJ and x the element representing the isogeny.</em>

> <pre><b>IsogeniesOfDegree</b>(A::AbelianVarietyFq, B::AbelianVarietyFq, N::RngIntElt)->BoolElt,List</pre>
<em>Given a source abelian variety A, a target abelian varity B and a positive integet N, it returns if there exist an isogeny A->B of degree N. If so it is also returned a list of representatives of the isormopshim classes of pairs [\*hom_x , K\*] where: hom_x:A->A, and K=xI subset J, with I and J the fractional ideals representing A and B and x the element representing the isogeny. At the moment it is implement ed only for squarefree abelin varieties.</em>

> <pre><b>IsPolarization</b>(pol::HomAbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt</pre>
<em>Returns whether the hommorphisms is known to be a polarizations for the CM-type phi.</em>

> <pre><b>IsPrincipallyPolarized</b>(A::AbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]</pre>
<em>Returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations.</em>

> <pre><b>HasPolarizationsOfDegree</b>(A::AbelianVarietyFq,PHI::AlgEtQCMType,N::RngIntElt : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]</pre>
<em>Returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations.</em>

> <pre><b>PolarizedAutomorphismGroup</b>(mu::HomAbelianVarietyFq : CheckOrdinary:=true) -> GrpAb</pre>
<em>returns the automorphisms of a polarized abelian variety</em>


## List of instrinsics in ./PeriodMatrices.m:

> <pre><b>PeriodMatrix</b>(pol::HomAbelianVarietyFq , PHI::AlgEtQCMType : CheckOrdinary:=true ) -> AlgMatElt,AlgMatElt</pre>
<em>Given a polarizattion of and abelian variety over a finite field it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.</em>


## List of instrinsics in ./BaseFieldExtension.m:

> <pre><b>BaseFieldExtension</b>( h::RngUPolElt, r::RngIntElt : prec:=3000) -> RngUPolElt</pre>
<em>Given a q-Weil polynomial, it returns the polynomial hr which is the char poly of Frobenius of A\otimes F_(q^r) for each A in AV(h). The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>BaseFieldExtension</b>(I::IsogenyClassFq, Ie::IsogenyClassFq : prec:=3000 )->Map</pre>
<em>Given a squarefree ordinary isogeny class I over Fq and Ie which is the base field extension to F_q^r, the map from the DeligneAlgebra of I to the one of Ie. The Weil polynomials of I and of Ie need to be pure powers of squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>BaseFieldExtension</b>(AVh::IsogenyClassFq, r::RngIntElt : prec:=3000 )->IsogenyClassFq,Map</pre>
<em>Given a squarefree ordinary isogeny class AV(h) and a positive integer r, it returns the isogeny class AV(hr) and maps mUA from the DeligneAlgebra of the AV(h) to the one of AV(hr). The Weil polynomials of AV(h) and of the extension AV(h^r) need to be pure powers of a squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>IsBaseFieldExtensionOf</b>(Ie::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Given an isogeny class over F_(p^r) it returns the sequence of all isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>IsPrimitive</b>(I::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Returns whether the given isogeny class is primitive, that is, if it is not the base extension of an isogeny class defined over a subfield. The computations is done by looking at the roots of the Weil polynomial of I. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>IsBaseFieldExtensionOfPrimitive</b>(Ie::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Given an isogeny class over F_(p^r) it returns the sequence of all primitive isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>BaseFieldExtension</b>(A::AbelianVarietyFq, Ie::IsogenyClassFq, me::Map)->AbelianVarietyFq</pre>
<em>Given an ordinary abelian variety A in the isogeny class I, the base field extension Ie of I, together with the map me from the DeligneAlgebra(I) to the DeligneAlgebra(Ie), it returns the base field extension Ae of A in Ie. The Weil polynomial of I and of Ie need to be pure powers of squarefree polynomials.</em>

> <pre><b>BaseFieldExtension</b>( seq::SeqEnum[AbelianVarietyFq], Ie::IsogenyClassFq )->SeqEnum[List]</pre>
<em>Given a sequence of squarefree ordinary abelian varieties A whose isogeny classes extend to Ie, it returns a sequence of pairs [\*Ae,me\*] consisting of the base field extension of the abelian varieties together with the maps on the DeligneAlgebras. The Weil polynomials of all inputs need to be pure powers of squarefree polynomials</em>

> <pre><b>IsTwistOfOrder</b>( A1::AbelianVarietyFq, A2::AbelianVarietyFq, r :: RngIntElt )-> BoolElt,HomAbelianVarietyFq</pre>
<em>Given two ordinary abelian varieties A1 and A2 (possibly non isogenous) over Fq checks itf they are twist of order r, that is, if they become isomorphic after a base field extension to F_q^r. The Weil polynomials of A1 and A2 and of their extensions need to be pure power of squarefree polynomials. This is the case, for example, if they are simple.</em>


## List of instrinsics in ./IsogenyClasses.m:

> <pre><b>IsWeil</b>(f::RngUPolElt : Precision:=30) -> BoolElt,RngIntElt,RngIntElt,RngIntElt</pre>
<em>Returns whether f is a q-WeilPolynomial, q,p and e, where q=p^e is a prime power polynomial. A polynomial is q-Weil if all the roots have complex absolute value q^(1/2). The check is done with precision "Precision" given as optional parameter (default precision is 30)</em>

> <pre><b>IsCharacteristicPoly</b>(f::RngUPolElt : Precision:=100) -> BoolElt,RngIntElt</pre>
<em>Given polynomial f, returns whether f is the characteristic polynomial of Frobenius of some isogeny class, together with the minimal exponent e, such that there exists a simple abelian variety over \F_q with characteristic polynomial of the Frobenius equal to f^e.
This abelian variety exists and it is uniquely determined up to \F_q-isogeny by Honda-Tate theory. For the method used, see [Wat69, paragraph before the last theorem on page 527].</em>

> <pre><b>IsogenyClass</b>( h::RngUPolElt : Check:=true ) -> IsogenyClassFq</pre>
<em>Given a WeilPolynomial h creates the isogeny class determined by h via Honda-Tate theory. The Check parameter (Default true) allows to decide whether to test if the polynomial defines an isogeny class (see IsCharacteristicPoly).</em>

> <pre><b>WeilPolynomial</b>( I::IsogenyClassFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the Weil polynomial h defining it.</em>

> <pre><b>WeilPolynomialFactorization</b>( I::IsogenyClassFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the factorization over Q of Weil polynomial h defining it.</em>

> <pre><b>ZFVOrder</b>(I::IsogenyClassFq)-> AlgEtQOrd,Map</pre>
<em>Given an isogeny class AV(h) defined by the Weil polynomial h with factorization over Q equal to h=g1^s1\*...\*gn^sn, returns the order Z[F,q/F]  in the algebra Q[F]=Q[x]/g where g = prod_i gi.</em>

> <pre><b>FiniteField</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the size of the finite field of definition.</em>

> <pre><b>CharacteristicFiniteField</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the characteristic of the finite field of definition.</em>

> <pre><b>Dimension</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the dimension.</em>

> <pre><b>NumberOfPoints</b>( I::IsogenyClassFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the number of rational points of the abelian varities in the isogeny class.</em>

> <pre><b>IsSquarefree</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is squarefree.</em>

> <pre><b>IsPurePower</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is a pure power.</em>

> <pre><b>IsPowerOfBass</b>(I::IsogenyClassFq)-> BoolElt</pre>
<em>Given an isogeny class AV(h) returns whether h is a pure power and ZFV is a Bass Order.</em>

> <pre><b>Print</b>(I::IsogenyClassFq)</pre>
<em>Prints the isogeny class.</em>

> <pre><b>'eq'</b>(AVh1::IsogenyClassFq , AVh2::IsogenyClassFq ) -> BoolElt</pre>
<em>Checks if the Weil polynomials are the same. It controls that the Universe algbras and ZFV orders are equal as well (to avoid double definitions).</em>

> <pre><b>IsOrdinary</b>(AVf::IsogenyClassFq) -> BoolElt</pre>
<em>Returns if the isogeny class is ordinary.</em>

> <pre><b>IsOrdinary</b>(A::AbelianVarietyFq) -> BoolElt</pre>
<em>Returns if the abelian variety is ordinary.</em>

> <pre><b>IsOrdinary</b>(f::RngUPolElt : Precision:=100) -> BoolElt</pre>
<em>Returns if the input polynomial is an Ordinary q-Weil polynomial, where q is a power of a prime number p, that is if the mid coefficient is coprime with p.</em>

> <pre><b>pRank</b>(I::IsogenyClassFq)->RngIntElt</pre>
<em>Returns the p-Rank of the isogeny class.</em>

> <pre><b>pRank</b>(A::AbelianVarietyFq)->RngIntElt</pre>
<em>Returns the p-Rank of the isogeny class.</em>

> <pre><b>IsAlmostOrdinary</b>(I::IsogenyClassFq)->BoolElt</pre>
<em>Returns whether the isogeny class is almost ordinary.</em>

> <pre><b>IsAlmostOrdinary</b>(A::AbelianVarietyFq)->BoolElt</pre>
<em>Returns whether the abelian variety is almost ordinary.</em>

> <pre><b>IsCentelegheStix</b>(I::IsogenyClassFq : Precision:=30 )->BoolElt</pre>
<em>Returns whether the isogeny class is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.</em>

> <pre><b>IsCentelegheStix</b>(I::AbelianVarietyFq : Precision:=30 )->BoolElt</pre>
<em>Returns whether the abelian variety is Centeleghe-Stix, that is, defined over Fp and the Weil poly has no real roots.</em>

> <pre><b>LPolyToWeilPoly</b>(l::RngUPolElt) -> RngUPolElt</pre>
<em>given an L-polynomial l(T) returns the associated Weil polynomial w(T):=T^(2g)\*l(1/T)</em>

> <pre><b>WeilPolyToLPoly</b>(w::RngUPolElt) -> RngUPolElt</pre>
<em>given a Weil polynomial w(T) returns the associated L-polynomial l(T):=T^(2g)\*l(1/T)</em>


## List of instrinsics in ./AbVarAttr.m:

> <pre><b>Print</b>(I::AbelianVarietyFq)</pre>
<em>print the abelian variety</em>

> <pre><b>IsogenyClass</b>( A::AbelianVarietyFq) -> IsogenyClassFq</pre>
<em>Returns the isogeny class of the given abelian variety.</em>

> <pre><b>WeilPolynomial</b>(A::AbelianVarietyFq )-> RngUpolElt</pre>
<em>Given an isogeny class AV(h) returns the Weil polynomial h defining it.</em>

> <pre><b>FiniteField</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the size of the finite field of definition.</em>

> <pre><b>CharacteristicFiniteField</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the characteristic of the finite field of definition.</em>

> <pre><b>Dimension</b>( A :: AbelianVarietyFq )-> RngInt</pre>
<em>Given an isogeny class AV(h) returns the dimension.</em>

> <pre><b>ZFVOrder</b>( A :: AbelianVarietyFq) -> AlgEtQOrd,Map</pre>
<em>Returns the ZFV of the isogeny class of A.</em>


## List of instrinsics in ./DeligneModules.m:

> <pre><b>DeligneAlgebra</b>( I::IsogenyClassFq )-> AlgEtQ,Map</pre>
<em>Given an isogeny class AV(h), defined by the Weil polynomial h with factorization over Q equal to h=g1^s1\*...\*gn^sn, it returns the algebra V=prod_i=1^n (Q[x]/gi)^si, where the DeligneModules live, together with the componentwise diagonal action of ZFV</em>

> <pre><b>FrobeniusEndomorphismOnDeligneAlgebra</b>(I::IsogenyClassFq)-> Map</pre>
<em>Given an isogeny class AV(h) returns the Frobenius endomorphism (acting on the DeligneAlgebra).</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>(AVh::IsogenyClassFq,M::AlgEtQMod)->AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a Z[F,V]-module M. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , I::AlgEtQIdl )->AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a fractional ideal I of the Z[F,V] order of the isogeny class AV(h), where h is the characteristic polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQIdl] )-> AbelianVarietyFq</pre>
<em>Returns the abelian variety defined by a direct sum of s fractional ideals of the Z[F,V] order of the isogeny class AV(g^s), where g is the miniml polynomial of the Frobenius. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>( AVh::IsogenyClassFq , seq::SeqEnum[AlgEtQElt] )-> AbelianVarietyFq</pre>
<em>Returns the abelian variety defined defined by the module generated by the elements in seq. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>AbelianVarietyFromDeligneModule</b>(AVh::IsogenyClassFq,seq::SeqEnum[Tup])->AbelianVarietyFq</pre>
<em>Given an isogeny class and sequence of pairs  <J_i,v_i> returns the abelin variety in the given isogeny class defined by the Deligne Module J_1v_1+...+J_sv_s. The isogeny class needs to be ordinary or CentelegheStix.</em>

> <pre><b>DeligneModule</b>(A :: AbelianVarietyFq)->AlgEtQMod</pre>
<em>Returns the DeligneModule defining the variety A.</em>

> <pre><b>DeligneAlgebra</b>( A :: AbelianVarietyFq) -> AlgEqQ</pre>
<em>Returns the DeligneAlgebra where the DeligneModule lives in.</em>

> <pre><b>'eq'</b>( A1 :: AbelianVarietyFq , A2 :: AbelianVarietyFq ) -> BoolElt</pre>
<em>Checks if two abelin varieties are equal, using the appropriate categorical description.</em>


## List of instrinsics in ./DualVar.m:

> <pre><b>DualAbelianVariety</b>(A::AbelianVarietyFq)->AbelianVarietyFq</pre>
<em>Given an abelian variety A returns the dual abelian variety. The isogeny class needs to be ordinary or Centelghe-Stix.</em>


## List of instrinsics in ./Ends.m:

> <pre><b>EndomorphismRing</b>(A::AbelianVarietyFq)-> AlgEtQOrd</pre>
<em>Returns Endomorphism ring of the abelian variety.</em>


## List of instrinsics in ./IsomClassesDM.m:

> <pre><b>IsIsomorphic</b>(A1::AbelianVarietyFq,A2::AbelianVarietyFq) -> BoolElt,HomAbelianVarietyFq</pre>
<em>Checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism.</em>

> <pre><b>IsomorphismClasses</b>( AVh::IsogenyClassFq )->SeqEnum[AbelianVarietyFq]</pre>
<em>Computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class.</em>


## List of instrinsics in ./RationalPoints.m:

> <pre><b>RationalPoints</b>(A::AbelianVarietyFq,r::RngIntElt)-> GrpAb</pre>
<em>Given an abelian variety over Fq, it returns the group of rational points defined over Fq^r.</em>

> <pre><b>RationalPoints</b>(A::AbelianVarietyFq)-> GrpAb</pre>
<em>Given an abelian variety over Fq, it returns the group of rational points defined over Fq.</em>


## List of instrinsics in ./HomDeligneModules.m:

> <pre><b>Print</b>(m::HomAbelianVarietyFq)</pre>
<em>print the morphism abelian variety</em>

> <pre><b>Domain</b>(m::HomAbelianVarietyFq)->AbelianVarietyFq</pre>
<em>returns the domain the morphism</em>

> <pre><b>Codomain</b>(m::HomAbelianVarietyFq)->AbelianVarietyFq</pre>
<em>returns the codomain the morphism</em>

> <pre><b>MapOnDeligneAlgebras</b>(m::HomAbelianVarietyFq)->Map</pre>
<em>returns underlying homormorphism of Deligne Moduels as a Z[F,V]-linear hom on the DeligneAlgebras</em>

> <pre><b>IsEndomorphism</b>(m::HomAbelianVarietyFq)->BoolElt</pre>
<em>returns whether the morphism is an endomorphism</em>

> <pre><b>Hom</b>(A::AbelianVarietyFq,B::AbelianVarietyFq,map::Map : Check:=true)->HomAbelianVarietyFq</pre>
<em>Creates a morphisms of abelian varieties A->B determined by map, where map is a morphisms of the DeligneAlgebras of A and B. The vararg Check allows to skip the test of the compatibility with the Frobenius.</em>

> <pre><b>FrobeniusEndomorphism</b>(A::AbelianVarietyFq)-> HomAbelianVarietyFq</pre>
<em>Returns the Frobenius endomorphism (acting on the DeligneAlgebra).</em>


## List of instrinsics in ./padictocc.m:

> <pre><b>pAdicToComplexRootsGMod</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection is G-equivariant, and the Galois group G.  
   The varargs precpAdic and precCC specify output 
   padic and complex precision.</em>

> <pre><b>pAdicToComplexRoots</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection arises from roots in a splitting field over 
   the rationals.  The varargs precpAdic and precCC specify (minimum) output 
   padic and complex precision.</em>

> <pre><b>ComplexRootsWithPositiveValuation</b>(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -></pre>
<em>Given an ordinary p-Weil polynomial (half unit roots, half positive valuation)
   return a polynomial over a complex quadratic field whose complex roots
   correspond to the set of p-adic roots with positive valuation, and
   the complex roots.
   The varargs precpAdic and precCC specify the padic precision used.</em>


## List of instrinsics in ./CMType.m:

> <pre><b>AllCMTypes</b>(AVh::IsogenyClassFq : precCC := 30 ) -> SeqEnum[AlgEtQCMType]</pre>
<em>Returns all the AlgEtQCMType of Algebra(ZFVOrder(AVh)).</em>

> <pre><b>pAdicPosCMType</b>(AVh::IsogenyClassFq : precpAdic := 30, precCC := 30 ) -> AlgEtQCMType</pre>
<em>Given an ordinary isogeny class AVh, it computes a AlgEtQCMType of the Algebra determined by the Frobenius of AVh such that the Frobenius has positive p-adic valuation according to some embedding of \barQp in C. The varargs precpAdic and precCC specify (minimum) output padic and complex precision.</em>


## List of instrinsics in ./IsogeniesPolarizations.m:

> <pre><b>IsogeniesManyOfDegree</b>(AIS::SeqEnum[AbelianVarietyFq], AJ::AbelianVarietyFq, N::RngIntElt) -> List</pre>
<em>Given a sequence of source squarefree abelian varieties AIS, a target sqaurefree abelian varity AJ and a positive integet N, it returns for each AI in AIS if there exist an isogeny AI->AJ of degree N. For each AI in AIS, if there exists and isogeny AI->AJ, it is also returned a list of representatives of the isomorphism classes of pairs [\*hom_x , K\*] where: hom_x:AI->AJ, and K=xI subset J, with I and J the fractional ideals representing AI and AJ and x the element representing the isogeny.</em>

> <pre><b>IsogeniesOfDegree</b>(A::AbelianVarietyFq, B::AbelianVarietyFq, N::RngIntElt)->BoolElt,List</pre>
<em>Given a source abelian variety A, a target abelian varity B and a positive integet N, it returns if there exist an isogeny A->B of degree N. If so it is also returned a list of representatives of the isormopshim classes of pairs [\*hom_x , K\*] where: hom_x:A->A, and K=xI subset J, with I and J the fractional ideals representing A and B and x the element representing the isogeny. At the moment it is implement ed only for squarefree abelin varieties.</em>

> <pre><b>IsPolarization</b>(pol::HomAbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt</pre>
<em>Returns whether the hommorphisms is known to be a polarizations for the CM-type phi.</em>

> <pre><b>IsPrincipallyPolarized</b>(A::AbelianVarietyFq, phi::AlgEtQCMType : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]</pre>
<em>Returns if the abelian variety is principally polarized and if so returns also all the non isomorphic polarizations.</em>

> <pre><b>HasPolarizationsOfDegree</b>(A::AbelianVarietyFq,PHI::AlgEtQCMType,N::RngIntElt : CheckOrdinary:=true)->BoolElt, SeqEnum[HomAbelianVarietyFq]</pre>
<em>Returns if the abelian variety has a polarization of degree N and if so it returns also all the non isomorphic polarizations.</em>

> <pre><b>PolarizedAutomorphismGroup</b>(mu::HomAbelianVarietyFq : CheckOrdinary:=true) -> GrpAb</pre>
<em>returns the automorphisms of a polarized abelian variety</em>


## List of instrinsics in ./PeriodMatrices.m:

> <pre><b>PeriodMatrix</b>(pol::HomAbelianVarietyFq , PHI::AlgEtQCMType : CheckOrdinary:=true ) -> AlgMatElt,AlgMatElt</pre>
<em>Given a polarizattion of and abelian variety over a finite field it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.</em>


## List of instrinsics in ./BaseFieldExtension.m:

> <pre><b>BaseFieldExtension</b>( h::RngUPolElt, r::RngIntElt : prec:=3000) -> RngUPolElt</pre>
<em>Given a q-Weil polynomial, it returns the polynomial hr which is the char poly of Frobenius of A\otimes F_(q^r) for each A in AV(h). The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>BaseFieldExtension</b>(I::IsogenyClassFq, Ie::IsogenyClassFq : prec:=3000 )->Map</pre>
<em>Given a squarefree ordinary isogeny class I over Fq and Ie which is the base field extension to F_q^r, the map from the DeligneAlgebra of I to the one of Ie. The Weil polynomials of I and of Ie need to be pure powers of squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>BaseFieldExtension</b>(AVh::IsogenyClassFq, r::RngIntElt : prec:=3000 )->IsogenyClassFq,Map</pre>
<em>Given a squarefree ordinary isogeny class AV(h) and a positive integer r, it returns the isogeny class AV(hr) and maps mUA from the DeligneAlgebra of the AV(h) to the one of AV(hr). The Weil polynomials of AV(h) and of the extension AV(h^r) need to be pure powers of a squarefree polynomials. The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.</em>

> <pre><b>IsBaseFieldExtensionOf</b>(Ie::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Given an isogeny class over F_(p^r) it returns the sequence of all isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>IsPrimitive</b>(I::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Returns whether the given isogeny class is primitive, that is, if it is not the base extension of an isogeny class defined over a subfield. The computations is done by looking at the roots of the Weil polynomial of I. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>IsBaseFieldExtensionOfPrimitive</b>(Ie::IsogenyClassFq : Precision:=300)->SeqEnum</pre>
<em>Given an isogeny class over F_(p^r) it returns the sequence of all primitive isogeny classes over FF_(p^s) that extend to Ie. The computations is done by looking at the roots of the Weil polynomial of Ie. The precision of such computations can be set by using the vararg "Precision".</em>

> <pre><b>BaseFieldExtension</b>(A::AbelianVarietyFq, Ie::IsogenyClassFq, me::Map)->AbelianVarietyFq</pre>
<em>Given an ordinary abelian variety A in the isogeny class I, the base field extension Ie of I, together with the map me from the DeligneAlgebra(I) to the DeligneAlgebra(Ie), it returns the base field extension Ae of A in Ie. The Weil polynomial of I and of Ie need to be pure powers of squarefree polynomials.</em>

> <pre><b>BaseFieldExtension</b>( seq::SeqEnum[AbelianVarietyFq], Ie::IsogenyClassFq )->SeqEnum[List]</pre>
<em>Given a sequence of squarefree ordinary abelian varieties A whose isogeny classes extend to Ie, it returns a sequence of pairs [\*Ae,me\*] consisting of the base field extension of the abelian varieties together with the maps on the DeligneAlgebras. The Weil polynomials of all inputs need to be pure powers of squarefree polynomials</em>

> <pre><b>IsTwistOfOrder</b>( A1::AbelianVarietyFq, A2::AbelianVarietyFq, r :: RngIntElt )-> BoolElt,HomAbelianVarietyFq</pre>
<em>Given two ordinary abelian varieties A1 and A2 (possibly non isogenous) over Fq checks itf they are twist of order r, that is, if they become isomorphic after a base field extension to F_q^r. The Weil polynomials of A1 and A2 and of their extensions need to be pure power of squarefree polynomials. This is the case, for example, if they are simple.</em>


