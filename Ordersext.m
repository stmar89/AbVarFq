freeze;

/////////////////////////////////////////////////////
// Ideal Class monoid for Etale Q algebras
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

import "usefulfunctions.m": AllPossibilities;
declare verbose Ordersext, 1;

/* LIST of functions
intrinsic PrimesAbove(I::AlgAssVOrdIdl) -> SeqEnum[AlgAssVOrdIdl]
intrinsic IsPrime(I::AlgAssVOrdIdl) -> BoolElt
intrinsic '!'(T::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
intrinsic MultiplicatorRing(R::AlgAssVOrd) -> AlgAssVOrd
intrinsic '/'(a::AlgAssElt,b::AlgAssElt)->AlgAssElt
intrinsic IsFiniteEtale(A::AlgAss) -> BoolElt
intrinsic MinimalInteger(I::AlgAssVOrdIdl) -> RngIntElt
intrinsic ListToSequence(L::List)->SeqEnum
intrinsic IsZeroDivisor2(x::AlgAssElt) -> BoolElt
intrinsic Random(I::AlgAssVOrdIdl) -> AlgAssElt
intrinsic CoprimeRepresentative(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> AlgAssElt
intrinsic ChineseRemainderTheorem(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl,a::AlgAssElt,b::AlgAssElt)-> AlgAssElt
intrinsic ResidueRing(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> GpAb , Map //WORK IN PROGRESS
intrinsic 'meet'(I::AlgAssVOrdIdl, S::AlgAssVOrd) -> AlgAssVOrdIdl
intrinsic 'meet'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
intrinsic IsCoprime(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> BoolElt
intrinsic IsIntegral(I::AlgAssVOrdIdl) -> BoolElt, RngIntElt
intrinsic 'eq'(I::AlgAssVOrdIdl,S::AlgAssVOrd)->BoolElt
intrinsic 'eq'(S::AlgAssVOrd,I::AlgAssVOrdIdl)->BoolElt
intrinsic 'subset'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> BoolElt
intrinsic 'subset'(I::AlgAssVOrdIdl,S::AlgAssVOrd) -> BoolElt
intrinsic ProdEqOrders(A::AlgAss)->AlgAssVOrd
intrinsic Index(S::AlgAssVOrd, I::AlgAssVOrdIdl) -> RngIntElt
intrinsic Index(S::AlgAssVOrd, T::AlgAssVOrd) -> RngIntElt
intrinsic HomsToC(A::AlgAss : Precision:=30)->SeqEnum[Map]
intrinsic FindOverOrders(E::AlgAssVOrd)->SeqEnum
intrinsic FindOverOrders(E::AlgAssVOrd,O::AlgAssVOrd)-> SeqEnum
intrinsic WKICM_bar(S::AlgAssVOrd) -> SeqEnum
intrinsic WKICM(E::AlgAssVOrd)->SeqEnum
intrinsic ICM_bar(S::AlgAssVOrd) -> SeqEnum
intrinsic ICM(S::AlgAssVOrd) -> SeqEnum
intrinsic IsBass(S::AlgAssVOrd) -> BoolElt
intrinsic IsClifford(S::AlgAssVOrd) -> BoolElt
intrinsic EquationOrder(A::AlgAss) -> AlgAssVOrd
intrinsic ColonIdeal(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
intrinsic ColonIdeal(O::AlgAssVOrd,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
intrinsic ColonIdeal(I::AlgAssVOrdIdl,O::AlgAssVOrd)->AlgAssVOrdIdl
intrinsic Inverse(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
intrinsic Conductor(O::AlgAssVOrd) ->AlgAssVOrdIdl
intrinsic IsWeakEquivalent(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->BoolElt
intrinsic IsWeakEquivalent(O1::AlgAssVOrd,O2::AlgAssVOrd)->BoolElt
intrinsic IsWeakEquivalent(O::AlgAssVOrd,J::AlgAssVOrdIdl)->BoolElt
intrinsic IsWeakEquivalent(J::AlgAssVOrdIdl,O::AlgAssVOrd)->BoolElt
intrinsic IsInvertible(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
intrinsic IsGorenstein(O::AlgAssVOrd)->BoolElt
intrinsic OrthogonalIdempotents(A::AlgAss)->SeqEnum
intrinsic AssociativeAlgebra(f::RngUPolElt) -> AlgAss
intrinsic AssociativeAlgebra(S::SeqEnum[FldNum]) -> AlgAss
intrinsic SplittingAlgebra(A::AlgAss) -> AlgAss, Map
intrinsic PrimitiveElement(A::AlgAss) -> AlgAssElt
intrinsic DefiningPolynomial(A::AlgAss) -> RngUPolElt
intrinsic '^'(I::AlgAssVOrdIdl,n::RngIntElt) -> AlgAssVOrdIdl
intrinsic IsProductOfOrders(O::AlgAssVOrd)->BoolElt, Tup
intrinsic IsProductOfIdeals(I::AlgAssVOrdIdl)->BoolElt, Tup
intrinsic IsIsomorphic2(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> BoolElt, AlgAssElt
function factorizationMaximalOrder(I)
intrinsic Factorization(I::AlgAssVOrdIdl) -> SeqEnum
intrinsic Components(x::AlgAssElt) -> SeqEnum
intrinsic TraceDualIdeal(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
intrinsic TraceDualIdeal(O::AlgAssVOrd) -> AlgAssVOrdIdl
intrinsic IsFractionalIdl(I::AlgAssVOrdIdl) -> BoolElt
intrinsic IsMaximal(O::AlgAssVOrd) -> BoolElt
intrinsic 'subset'(O1 :: AlgAssVOrd, O2 :: AlgAssVOrd) -> BoolElt
intrinsic 'subset'(I1 :: AlgAssVOrdIdl, I2 :: AlgAssVOrdIdl) -> BoolElt
intrinsic IdealsOfIndex(I::RngOrdIdl, N::RngIntElt) -> SeqEnum[RngOrdIdl]
intrinsic IdealsOfIndex(I::RngOrdFracIdl, N::RngIntElt) -> SeqEnum[RngOrdFracIdl]
intrinsic IdealsOfIndexProduct(Is::Tup, N::RngIntElt) -> SeqEnum[Tup]
intrinsic IdealsOfIndex(I::AlgAssVOrdIdl[RngOrd], N::RngIntElt : Al := "Default") -> SeqEnum[AlgAssVOrdIdl]
//what follows overwrites bugged functions
intrinsic 'in'(a::RngElt, I::AlgAssVOrdIdl) -> BoolElt
function IsOrder(O);
function order_over(Z_F, S, I : Check := true)
intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : Check := true) -> AlgAssVOrd
intrinsic '+'(O1::AlgAssVOrd[RngOrd], O2::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl, AlgAssVOrdIdl
//Test
RunTests:=procedure();
*/

/*TODO:
-check that in the Edgar's code on IDealsOfIndex there is no requirement on the multiplicatorRing, as that is called in AbelianVarieties.m
-compare my IsZeroDivisor2 with the already built-in IsUnit
-IsFiniteEtale is wrong!!! it does not recognize the base ring, on the other hand, when I define an AssociativeAlgebra, I set the test to be true, so it is sort of harmless.
-Put all the "if assigned ??" in dedicated functions
-Rewrite FindOverOrders as follows: it should be possible to give an optional argument "oo" that contains all the overorders and then the function only creates the Poset, i.e. assignes the S'OverOrders parameter to speed up the rest of the computation
-WKICM_bar prime per prime;
*/

RANF_protected:=RationalsAsNumberField();

declare attributes AlgAss:NumberFields;
declare attributes AlgAss:isFiniteEtale;
declare attributes AlgAss:CMType;
declare attributes AlgAssVOrd:OverOrders;

intrinsic PrimesAbove(I::AlgAssVOrdIdl) -> SeqEnum[AlgAssVOrdIdl]
{given an integral S-ideal, returns the sequence of maximal ideals P of S above I}
	require IsIntegral(I): "the ideal must be integral";
	S:=Order(I);
	if One(S) in I then
		return [];
	else
		O:=MaximalOrder(S);
		IO:=O!I;
		fac:=Factorization(IO);
		primes:= Setseq({ S meet (S!PO[1]) : PO in fac });
		assert forall{P : P in primes | I subset P};
		return primes;
	end if;
end intrinsic;

intrinsic IsPrime(I::AlgAssVOrdIdl) -> BoolElt
{given an integral S-ideal, returns if the ideal is a prime fractional ideal of S, that is a maximal S ideal}
	require IsIntegral(I): "the ideal must be integral";
	prim:=PrimesAbove(I);
	if #prim eq 1 and I eq prim[1] then
		return true;
	else
		return false;
	end if;
end intrinsic;

intrinsic '!'(T::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{given an S-ideal I and an order T, returns the extension IT as a T-ideal. Note that if T is in S, then IT=I}
	S:=Order(I);
	return ideal<T|ZBasis(I)>;
end intrinsic;

intrinsic MultiplicatorRing(R::AlgAssVOrd) -> AlgAssVOrd
{returns the MultiplicatorRing of an order R, that is R itself}
	return R;
end intrinsic;

intrinsic '/'(a::AlgAssElt,b::AlgAssElt)->AlgAssElt
{ given a and b, a non-zero divisor, it returs a/b}
	require Parent(a) eq Parent(b): "the elements must belong to the same algebra";
	require not IsZeroDivisor2(b): "the denominator must be an invertible element";
	return a*b^-1;
end intrinsic;

intrinsic IsFiniteEtale(A::AlgAss) -> BoolElt
{returns if A is a finite etale algebra over Q, that is a finite product of number fields}
	if assigned A`isFiniteEtale then
		return A`isFiniteEtale;
	else //it does not recognize the BaseRing!!! the next part is useless
		t:=BaseRing(A) eq RANF_protected and IsCommutative(A) and IsFinite(Degree(A)) and assigned A`NumberFields;
		A`isFiniteEtale:=t;
		return t;
	end if;
end intrinsic;

intrinsic MinimalInteger(I::AlgAssVOrdIdl) -> RngIntElt
{returns the smallest integer contained in the ideal I}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	require IsIntegral(I): "the ideal must be integral";
	S:=Order(I);
	ind:=Integers() ! Index(S,I);
	divs:=Divisors(ind);
	for i in [1..#divs-1] do
		if divs[i] in I and not divs[i+1] in I then
			return divs[i];
		end if;
	end for;
	assert divs[#divs] in I;
	return divs[#divs];
end intrinsic;

intrinsic ListToSequence(L::List)->SeqEnum
{given a list of elements returns the same sequence}
	return [s : s in L];
end intrinsic;

intrinsic IsZeroDivisor2(x::AlgAssElt) -> BoolElt
{returns if the element x is a zero divisor}
	require IsFiniteEtale(Parent(x)): "the algebra of definition must be finite and etale over Q";
	return exists{c : c in Components(x)|c eq Zero(Parent(c))};
end intrinsic;

intrinsic Random(I::AlgAssVOrdIdl : bound:=3) -> AlgAssElt
{Returns a random (small coefficient) element of I}
	A := Algebra(Order(I));
	B := ZBasis(I);
	return A ! &+[ Random([-bound..bound])*b : b in B];
end intrinsic;

intrinsic CoprimeRepresentative(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> AlgAssElt
{return an element x such that x*I is an integral ideal coprime with J. The first ideal must be invertible and the second should be integral}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	require IsIntegral(J) : "the second ideal must be integral";
	S:=Order(I);
	require S eq Order(J): "the ideals must be defined over the same order";
	require IsInvertible(I): "The first ideal must be invertible";
	invI:=ColonIdeal(S,I);
	repeat
		x:=Random(invI);
	until (not IsZeroDivisor2(x) and IsCoprime(x*I,J)); //integrality of x*I is checked in IsCoprime
	return x;
end intrinsic;

intrinsic ChineseRemainderTheorem(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl,a::AlgAssElt,b::AlgAssElt)-> AlgAssElt
{given two coprime ideals I and J of S, two elements a,b in S, finds e such that (e-a) in I and (e-b) in J}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	require IsCoprime(I,J) : "the ideals must be coprime";
	S:=Order(I);
	require a in S and b in S:"the elements must lie in order of definition of the ideals";
	require S eq Order(J): "the ideals must be of the same order";
	K:=Algebra(S);
	n:=Degree(K);
	//I need to modify the ZBasis(S) in a way that One(K) is the first element of Zbasis_S
	Zbasis_S:=ZBasis(S);
	pos:=Position(Eltseq(S ! One(K)),1); //Eltseq(S ! One(K)) does not distinguish 1 from -1.....
	temp:=Zbasis_S[1];
	Zbasis_S[1]:=One(K);
	if pos ne 1 then
		Zbasis_S[pos]:=temp;
	end if;
	assert Order(Zbasis_S) eq S;
	M:=Matrix(Zbasis_S);
	A:=ChangeRing(Matrix(ZBasis(I))*M^-1,Integers());
	B:=ChangeRing(Matrix(ZBasis(J))*M^-1,Integers());
	I_min:=MinimalInteger(I);
	J_min:=MinimalInteger(J);
	g,c1,d1:=XGCD(I_min,J_min);
	assert I_min*One(K) in I and J_min*One(K) in J;
	if g ne 1 then
		C:=VerticalJoin(A,B);
		H,U:=HermiteForm(C); //U*C = H;
		z:=ZeroMatrix(Integers(),n,n);
		s:=ScalarMatrix(n,1);
		assert H eq VerticalJoin(s,z);
		P:=VerticalJoin(HorizontalJoin(z,s),HorizontalJoin(s,z));
		U1:=Transpose(U)*P; //I need the (n+1)st column of U1
		Z:=Transpose(U1)[n+1];
		X:=Matrix(Integers(),1,n,[Z[i] : i in [1..n]]);
		Y:=X*A;
		c:=&+[Y[1,i]*Zbasis_S[i] : i in [1..n]];
		assert c in I;
		d:=One(K)-c;
		assert d in J;
	else
		//g:=c1*I_min+d1*J_min
		c:=c1*I_min;
		d:=d1*J_min;
	end if;
	e:=a*d+b*c;
	assert e-a in I; assert e-b in J;
	return e;
end intrinsic;

intrinsic ResidueRing(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> GpAb , Map
{given an integral ideal I of S, returns the abelian group S/I and the epimorphism pi:S -> S/I (with inverse map). Important: the domain of pi is the Algebra of S, since the elements of S are usually expressed al elements of A. For eg Parent(Random(S)) = Algebra(S)}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	require Order(I) eq S and IsIntegral(I): "I must be an integral ideal os S";
	A:=Algebra(S);
	N:=Degree(A);
	F:=FreeAbelianGroup(N);
	matS:=Transpose(Matrix(ZBasis(S)));
	matP:=Transpose(Matrix(ZBasis(I)));
	S_to_F:=function(x)
	assert Parent(x) eq A;
	assert x in S;
	clmn_vec_x:=Transpose(Matrix(x));
	x_inS:=matS^-1*clmn_vec_x; //column vector of wrt the ZBasis(S)
	assert N eq #Eltseq(x_inS);
	return (F ! Eltseq(x_inS)) ;
	end function;
	F_to_S:=function(y)
	clmn_vec_y:=Transpose(Matrix(Vector(Eltseq(y))));
	y_inA:=&+[ZBasis(S)[i]*Eltseq(clmn_vec_y)[i] : i in [1..N]];
	return y_inA;
	end function;
	StoF:=map< A -> F | x :-> S_to_F(x), y :-> F_to_S(y)>;
	rel:=[F ! Eltseq(x) : x in Rows(Transpose(matS^-1 * matP))];
	Q,q:=quo<F|rel>; //Q=S/I
	m:=StoF*q; //m is a map from S to Q
	assert #Q eq Index(S,I);
	assert forall{x : x in ZBasis(I) | m(x) eq Zero(Q)};
	assert forall{x : x in ZBasis(S) | ((m(x))@@m - x) in I};
	return Q,m;
end intrinsic;

intrinsic 'meet'(I::AlgAssVOrdIdl, S::AlgAssVOrd) -> AlgAssVOrdIdl
{given an ideal I of S, return S cap I}
	require Order(I) eq S: "the second argument must be an ideal of the first argument";
	return S meet I;
end intrinsic;

intrinsic 'meet'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{given an ideal I of S, return S cap I}
	require Order(I) eq S: "the second argument must be an ideal of the first argument";
	idS:=ideal<S|One(S)>;
	output:=idS meet I;
	return output;
end intrinsic;

intrinsic IsCoprime(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl) -> BoolElt
{given two integral ideals I and J of an order S, returns whether I+J=R}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	S:=Order(J);
	require Order(I) eq S: "the ideals must be over the same order";
	require IsIntegral(I) and IsIntegral(J): "the ideals must be integral";
	return I+J eq S;
end intrinsic;

intrinsic IsIntegral(I::AlgAssVOrdIdl) -> BoolElt, RngIntElt
{returns wheter the ideal I of S is integral, that is I \subseteq S, and a minimal integer d such that (d)*I \subseteq S.}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	S:=Order(I);
	d:=Index(I,S meet I);
assert Denominator(d) eq 1;
assert d*I subset S;
	d:=Integers() ! d;
	if d eq 1 then
		return true,d;
	else
		for y in Divisors(d) do
			if (y*I) subset S then
				assert Denominator(Index(S,(y*I))) eq 1;
				return false,y;
				break y;
			end if;
		end for;
	end if;
end intrinsic;

intrinsic 'eq'(I::AlgAssVOrdIdl,S::AlgAssVOrd)->BoolElt
{return if I eq S. I needs to be an indeal of S}
	if I eq ideal<S|One(S)> then
		assert Index(S,I) eq 1;
		return true;
	else
		assert Index(S,I) ne 1;
		return false;
	end if;
end intrinsic;

intrinsic 'eq'(S::AlgAssVOrd,I::AlgAssVOrdIdl)->BoolElt
{return if I eq S. I needs to be an indeal of S}
	return I eq S;
end intrinsic;

intrinsic 'subset'(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> BoolElt
{given an ideal I of S, return if S subseteq I}
	require Order(I) eq S: "the second argument must be an ideal of the first argument";
	idS:=ideal<S|One(S)>;
	return idS subset I;
end intrinsic;

intrinsic 'subset'(I::AlgAssVOrdIdl,S::AlgAssVOrd) -> BoolElt
{given an ideal I of S, return if I subseteq S}
	require Order(I) eq S: "the first argument must be an ideal of the second argument";
	idS:=ideal<S|One(S)>;
	return I subset idS;
end intrinsic;

intrinsic ProdEqOrders(A::AlgAss)->AlgAssVOrd
{given a product of number fields A, returns the order consisting of the product of the equation orders of the number fields}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	gen_inA:=[];
	for L in A`NumberFields do
		EL:=EquationOrder(L[1]);
		gen_inA:=gen_inA cat [L[2](y) : y in Basis(EL,L[1])];
	end for;
	return Order(gen_inA);
end intrinsic;

intrinsic Index(S::AlgAssVOrd, T::AlgAssVOrd) -> RngIntElt
{given two orders T \subset S, returns [S:T] = #S/T }
	require T subset S :"the first argument must be a subset of the second";
	matS:=Matrix(ZBasis(S));
	matT:=Matrix(ZBasis(T));
	return Abs( Integers() ! Determinant(matT*matS^-1));
end intrinsic;

intrinsic Index(J::AlgAssVOrdIdl, I::AlgAssVOrdIdl) -> FldRatElt
{given fractional ideals J and I defined over the same order returns [J:I] = [J:J cap I]/[I : J cap I]}
	require Order(I) eq Order(J): "the ideals must be of the same order";
	mat := Matrix(Coordinates(ZBasis(I), ZBasis(J)));
	return Abs(Rationals() ! Determinant(mat));
end intrinsic;

intrinsic Index(S::AlgAssVOrd, I::AlgAssVOrdIdl) -> FldRatElt
{given and ideal I of an order S returns [S:I] = [S:S cap I]/[I : S cap I] }
	require Order(I) eq S: "the ideal must be of the appropriate order";
	return Index(ideal<S|One(S)>,I);
end intrinsic;

intrinsic Automorphisms(A::AlgAss) -> SeqEnum[Maps]
{returns the automorphisms of A as a sequence of maps. A must be a product of number fields and the maps are componentwise automorphisms}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	S:=[ Automorphisms(L[1]) : L in A`NumberFields ];
	output:=[];
	for s in AllPossibilities(S) do
		r:=#A`NumberFields;
		assert #s eq r;
		map_s:=map< A->A | x:-> &+[A`NumberFields[i,2](s[i](Components(x)[i])) : i in [1..r]] >;
		Append(~output, map_s);
	end for;
	return output;
end intrinsic;

intrinsic HomsToC(A::AlgAss : Precision:=30)->SeqEnum[Map]
{returns Hom(A,\C) as a sequence of maps. The precision of \C is given by the optional parameter "Precision". Default value is 30}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	CC:=ComplexField(Precision);
	images:=function(x)
		return &cat[[CC ! z : z in Conjugates(y : Precision:=Precision)] :y in Components(x)];
	end function;
	maps:=< map< A -> CC | x:-> images(x)[k] > : k in [1..Degree(A)] >;
	f:=&*[DefiningPolynomial(L[1]) : L in A`NumberFields];
	assert &and [ Abs(Evaluate(f,g(PrimitiveElement(A)))) lt 10^-10 : g in maps]; //the precision here is quite arbitrary...
	return maps;
end intrinsic;

intrinsic FindOverOrders(E::AlgAssVOrd)->SeqEnum
{returns all the overorders of E}
	if assigned E`OverOrders then
		return E`OverOrders;
	else
		A:=Algebra(E);
		require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
		if assigned A`MaximalOrder then
			O:=A`MaximalOrder;
		else 
			O:=MaximalOrder(A);
			A`MaximalOrder:=O;
		end if;
		if O eq E then
			E`OverOrders:=[E];
			return [E];
		end if;
		seq:=FindOverOrders(E,O);
		for i in [1..#seq] do
			S:=seq[i];
			if not assigned S`OverOrders then
				S`OverOrders := [T : T in seq | S subset T];
			end if;
		end for;
		return seq;
	end if;
end intrinsic;

intrinsic FindOverOrders(E::AlgAssVOrd,O::AlgAssVOrd)-> SeqEnum
{given E subset O, returns the sequence of orders between E and O}
//15/02/2018 we add the LowIndexProcess
	require IsFiniteEtale(Algebra(E)): "the algebra of definition must be finite and etale over Q";
	require E subset O : "the first argument must be a subset of the second";
	if assigned E`OverOrders then
		return [S: S in E`OverOrders | S subset O];
	else
		F:=FreeAbelianGroup(Degree(O));
		E_ZBasis:=ZBasis(E);
		O_ZBasis:=ZBasis(O);
		rel:=[F ! Eltseq(x) : x in Coordinates(E_ZBasis,ZBasis(O))];
		Q,q:=quo<F|rel>; //q:F->Q quotient map
		FP,f:=FPGroup(Q); //f:FP->Q isomorphism
		N:=#FP;
		subg:=LowIndexProcess(FP,<1,N>);
		seqOO:=[];
		while not IsEmpty(subg) do
			H := ExtractGroup(subg);
			NextSubgroup(~subg);
			geninF:=[(f(FP ! x))@@q : x in Generators(H)];
			coeff:=[Eltseq(x) : x in geninF];
			coeff:=[Eltseq(x) : x in geninF];
			S:=Order([&+[O_ZBasis[i]*x[i] : i in [1..Degree(Algebra(O))]] : x in coeff] cat E_ZBasis);
			if not exists{T : T in seqOO | S eq T} then
				Append(~seqOO,S);
			end if;
		end while;
		Exclude(~seqOO,O); Append(~seqOO,O); //in this way O is the last of the list
		assert E in seqOO and O in seqOO;
		return seqOO;
	end if;
end intrinsic;

function factorizationMaximalOrder(I)
//given an ideal of the maximal order of an algebra, returns the factorization into a product of prime ideals
	O:=Order(I);
	assert IsMaximal(O);
	A:=Algebra(O);
	_,IasProd:=IsProductOfIdeals(I);
	fac:=[]; //this will be the factorization of I
	for i in [1..#A`NumberFields] do
		L:=A`NumberFields[i,1];
		mL:=A`NumberFields[i,2];
		IL:=IasProd[i];
		assert IsMaximal(Order(IL));
		facL:=Factorization(IL);
		for p in facL do
			genPinA:=[mL(x) : x in Basis(p[1],L)] cat [F[2](One(F[1])) : F in A`NumberFields | F[1] ne L];
			P:=ideal<O | genPinA>;
			Append(~fac,<P,p[2]>);
		end for;
	end for;
	assert I eq &*[p[1]^p[2] : p in fac];
	return fac;
end function;

intrinsic Factorization(I::AlgAssVOrdIdl) -> Tup
{given a proper integral S-ideal I coprime with the conductor of S (hence invertible in S), returns its factorization into a product of primes of S}
	S:=Order(I);
	require IsIntegral(I) and I ne ideal<S|One(S)>: "the argument must be a proper integral ideal";
	if IsMaximal(S) then
		return factorizationMaximalOrder(I);
	else
		fS:=Conductor(S);
		require IsCoprime(fS,I): "the ideal must be coprime with the conductor of the order of definition";
		require assigned Algebra(I)`NumberFields :"it must be a product of number fields";
		O:=MaximalOrder(S);
		IO:=O ! I;
		facO:=factorizationMaximalOrder(IO);
		primesO:=[ p[1] : p in facO ];
		primesS:=Setseq({ S meet (S!PO) : PO in primesO }); //this should cancel the doubles
		facS:=<>;
		for P in primesS do
			expP:=&+([ pO[2] : pO in facO | (S meet (S!pO[1])) eq P ]);
			Append(~facS, <P,expP>);
		end for;
		assert I eq &*([ p[1]^p[2] : p in facS ]);
		return facS;
	end if;
end intrinsic;

intrinsic WKICM_bar(S::AlgAssVOrd) -> SeqEnum
{returns all the weak eq classes I, such that (I:I)=S}
//TODO : prime per prime;
	require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
	if IsGorenstein(S) then
		return [ideal<S|One(S)>];
	else
		A:=Algebra(S);
		degA:=Degree(A);
		seqWk_bar:=[];
		St:=TraceDualIdeal(S);
		T:=&meet([ T : T in FindOverOrders(S) | IsInvertible(T ! St) ]);
		//this construction of T is conjectural, hence the next assert. If the assert fails, please report it.
		assert IsInvertible(T ! St);
		T_ZBasis:=ZBasis(T);
		ff:=ColonIdeal(S,ideal<S|T_ZBasis>);
		ff_ZBasis:=ZBasis(ff);
		seqWk_bar:=[];
		F:=FreeAbelianGroup(Degree(Algebra(S)));
		matT:=Matrix(T_ZBasis);
		matff:=Matrix(ff_ZBasis);
		rel:=[F ! Eltseq(x) : x in Rows(matff*matT^-1)];
		Q,q:=quo<F|rel>; //Q=T/(S:T)
		QP,f:=FPGroup(Q);
		subg:=LowIndexProcess(QP,<1,#QP>);
		while not IsEmpty(subg) do
			H := ExtractGroup(subg);
			NextSubgroup(~subg);
			geninF:=[(f(QP ! x))@@q : x in Generators(H)];
			coeff:=[Eltseq(x) : x in geninF];
			I:=ideal<S| [&+[T_ZBasis[i]*x[i] : i in [1..degA]] : x in coeff] cat ff_ZBasis>;
			if MultiplicatorRing(I) eq S and not exists{J : J in seqWk_bar | IsWeakEquivalent(I,J)} then 
				Append(~seqWk_bar,I);
			end if;
		end while;
		return seqWk_bar;
	end if;
end intrinsic;

intrinsic WKICM(E::AlgAssVOrd)->SeqEnum
{computes the Weak equivalence class monoid of E}
	A:=Algebra(E);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	if assigned A`MaximalOrder then O:=A`MaximalOrder; else O:=MaximalOrder(A); A`MaximalOrder:=O; end if;
	if assigned E`OverOrders then seqOO:=E`OverOrders; else seqOO:=FindOverOrders(E); E`OverOrders:=seqOO; end if;
	return &cat[[ideal<E | ZBasis(I)> : I in WKICM_bar(S)] : S in seqOO ];
end intrinsic;

intrinsic ICM_bar(S::AlgAssVOrd) -> SeqEnum
{returns the ideal classes of the order S having S as MultiplicatorRing, that is the orbits of the action of PicardGroup(S) on WKICM_bar(S)}
	require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
	seqWKS_bar:=WKICM_bar(S);
	GS,gS:=PicardGroup(S);
	repS:=[gS(x) : x in GS];
	ICM_barS := &cat[[ideal<S|ZBasis(I)>*ideal<S|ZBasis(J)> : I in seqWKS_bar] : J in repS];
	assert forall{J : J in ICM_barS | MultiplicatorRing(J) eq S};
	assert forall{J : J in ICM_barS | Order(J) eq S};
	return ICM_barS;
end intrinsic;

intrinsic ICM(S::AlgAssVOrd) -> SeqEnum
{returns the ideal class monoid of the order, that is a set of representatives for the isomorphism classes of the fractiona ideals}
	require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
	seqOO:=FindOverOrders(S);
	seqICM:=[];
	for T in seqOO do
		ICM_barT := [ideal<S|ZBasis(I)> : I in ICM_bar(T)];
		assert forall{J : J in ICM_barT | MultiplicatorRing(J) eq T};
		assert forall{J : J in ICM_barT | Order(J) eq S};
		seqICM:=seqICM cat ICM_barT;
	end for;
	assert forall{I: I in seqICM | Order(I) eq S};
	return seqICM;
end intrinsic;

intrinsic IsBass(S::AlgAssVOrd) -> BoolElt
{checks if all the over orders of S are Gorenstein}
	require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
	if assigned S`OverOrders then
		seqOO:=S`OverOrders;
	else
		seqOO:=FindOverOrders(S);
		S`OverOrders:=seqOO;
	end if;
	return forall{T : T in seqOO | IsGorenstein(T)};
end intrinsic;

intrinsic IsClifford(S::AlgAssVOrd) -> BoolElt
{checks if all the over orders of S are Gorenstein}
	return IsBass(S);
end intrinsic;

intrinsic EquationOrder(A::AlgAss) -> AlgAssVOrd
{given an associative algebra defined by a polynomial, returns the monogenic order defined by the same polynomial}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	F:=PrimitiveElement(A);
	E:=Order([F^i : i in [0..Degree(A)-1]]);
	return E;
end intrinsic;

intrinsic ColonIdeal(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
{computes the colon ideal (I:J) (as an O-ideal) of two O-ideals}
// require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	O := Order(I);
	require Order(J) eq O : "the ideals must be of the same order";
	C := Colon(I,J);
	C := PseudoMatrix(CoefficientIdeals(C), Matrix(C) * Matrix(PseudoMatrix(O))^-1 );
	IJ := ideal<O|C>;
	return IJ;
end intrinsic;

intrinsic ColonIdeal(O::AlgAssVOrd,J::AlgAssVOrdIdl)->AlgAssVOrdIdl
{computes the colon ideal (1*O:J) (as an O-ideal)}
	require Order(J) eq O : "the ideals must be of the same order";
	I:=ideal<O|One(O)>;
	return ColonIdeal(I,J);
end intrinsic;

intrinsic ColonIdeal(I::AlgAssVOrdIdl,O::AlgAssVOrd)->AlgAssVOrdIdl
{computes the colon ideal (I:1*O) (as an O-ideal)}
	require Order(I) eq O : "the ideals must be of the same order";
	J:=ideal<O|One(O)>;
	return ColonIdeal(I,J);
end intrinsic;

intrinsic Inverse(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
{computes the inverse of an ideal of a maximal order}
	O:=Order(I);
	require (assigned O`IsMaximal and O`IsMaximal) or IsMaximal(O): "only for ideals in maximal orders. use ColonIdeal otherwise";
	return ColonIdeal(O,I);
end intrinsic;

intrinsic Conductor(O::AlgAssVOrd) ->AlgAssVOrdIdl
{computes the conductor of an order}
	A:=Algebra(O);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	if assigned A`MaximalOrder then
		OA:=A`MaximalOrder;
	else
		OA:=MaximalOrder(A);
		A`MaximalOrder:=OA;
	end if;
	return ColonIdeal(O,ideal<O|ZBasis(OA)>);
end intrinsic;

intrinsic IsWeakEquivalent(I::AlgAssVOrdIdl,J::AlgAssVOrdIdl)->BoolElt
{ checks if 1 \in (I:J)*(J:I). This function does not require that the ideals are defined over the same order. }
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	S := MultiplicatorRing(I);
	if MultiplicatorRing(J) ne S then
		return false;
	else
		IS:=ideal<S|ZBasis(I)>;
		JS:=ideal<S|ZBasis(J)>;
		CIJ:=ColonIdeal(IS,JS);
		CJI:=ColonIdeal(JS,IS);
		test:=ideal<S|One(S)> eq (CIJ*CJI); //note that this test does not depend on the order of definition of the ideals.
		return test;
		end if;
end intrinsic;

intrinsic IsWeakEquivalent(O1::AlgAssVOrd,O2::AlgAssVOrd)->BoolElt
{ check if the two orders are weakly equivalent, that is equal }
	require IsFiniteEtale(Algebra(O1)): "the algebra of definition must be finite and etale over Q";
	return O1 eq O2;
end intrinsic;

intrinsic IsWeakEquivalent(O::AlgAssVOrd,J::AlgAssVOrdIdl)->BoolElt
{ checks if the second argument is weakly equivalent to the first argument }
	require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
	I:=ideal<O|One(O)>;
	return IsWeakEquivalent(I,J);
end intrinsic;

intrinsic IsWeakEquivalent(J::AlgAssVOrdIdl,O::AlgAssVOrd)->BoolElt
{ checks if the second argument is weakly equivalent to the first argument }
	require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
	I:=ideal<O|One(O)>;
	return IsWeakEquivalent(I,J);
end intrinsic;

intrinsic IsInvertible(I::AlgAssVOrdIdl) ->AlgAssVOrdIdl
{ checks if the ideal is invertible in its order of definition }
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	O:=Order(I);
	return IsWeakEquivalent(I,O);
end intrinsic;

intrinsic IsGorenstein(O::AlgAssVOrd)->BoolElt
{ checks if the order O is Gorenstein }
	require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
	T:=TraceDualIdeal(O);
	return IsInvertible(T);
end intrinsic

intrinsic OrthogonalIdempotents(A::AlgAss)->SeqEnum
{returns a sequence containing the orthogonal ideampotents of the algebra, that is the image of the units of the number fields the algebra is product of}
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	return [L[2](One(L[1])) : L in A`NumberFields ];
end intrinsic;

intrinsic AssociativeAlgebra(f::RngUPolElt) -> AlgAss
{given a integer polynomial f generates the Associative algebra over Q given by the factors of f with multiplicity}
	QQ:=RANF_protected;
	f_fac:=Factorization(f);
	num_fields:=[NumberField(g[1]) : j in [1..g[2]] , g in f_fac];
	return AssociativeAlgebra(num_fields);
end intrinsic;

intrinsic AssociativeAlgebra(S::SeqEnum[FldNum]) -> AlgAss
{given given a sequence of number fields, it returns the associative algebra given by the product of the number field}
	QQ:=RANF_protected;
	num_fields:=S;
	deg:=&+[Degree(Ai): Ai in S];

	// let's build A = \prod A_i
	A_matrix:=ZeroMatrix(QQ,deg,deg^2);
	for i in [1..#num_fields] do
		deg_fi:=Degree(num_fields[i]);
		if i eq 1 then
			deg_prev:=0;
		else
			deg_prev:=&+[Degree(num_fields[j]) : j in [1..(i-1)]];
		end if;
		if i eq #num_fields then
			deg_next:=0;
		else
			deg_next:=&+[Degree(num_fields[j]) : j in [(i+1)..(#num_fields)]];
		end if;
		Ai:=num_fields[i];
		mult_table:=MultiplicationTable(EquationOrder(DefiningPolynomial(Ai))); // the table has to be defined via DefiningPolynomial to avoid an issue with SplittingAlgebra(AssociativeAlgebra(x^4+4*x^3+6*x^2+44*x+121));
		for k in [1..#mult_table] do
			InsertBlock(~A_matrix, ChangeRing(mult_table[k],QQ) , deg_prev+1, deg_prev*deg+deg*(k-1)+deg_prev+1);
		end for;
	end for;
	A:=AssociativeAlgebra<QQ,deg | &cat(RowSequence(A_matrix))>;
	A`NumberFields:=[**];
	//let's build the maps from the number fields to K
	deg_prev:=0;
	for L in num_fields do
		Lass,LToLass:=Algebra(L,QQ);
		LassToA:=hom<Lass -> A | [A.j : j in [deg_prev+1..deg_prev+Degree(L)]]>;
		deg_prev:=deg_prev+Degree(L);
		Append(~A`NumberFields, <L,LToLass * LassToA>);
	end for;
	A`isFiniteEtale:=true;
	return A;
end intrinsic;

splittingfield_internal:=function(K)
//given a number field K returns a pair L,l where L is the SplittingField of K and l is an embedding K in L
//it is much faster then the in-built function SplittingField(K)
	f:=DefiningPolynomial(K);
	F:=PrimitiveElement(K);
	L:=SplittingField(f);
	pL:=PolynomialRing(L);
	fact:=Factorization(pL!f);
	l:=hom<K->L | F:->Coefficients(fact[1,1])[1]>;
	return L,l;
end function;

intrinsic SplittingAlgebra(A::AlgAss) -> AlgAss, Map
{ given a product of number fields A, returns the product of the splitting fields and a map from A }
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	split_fields:=[];
	split_fields_embeddings:=[];
	for K in A`NumberFields do
		L,l:=splittingfield_internal(K[1]);
		Append(~split_fields,L);
		Append(~split_fields_embeddings,l);
	end for;
	AA:=AssociativeAlgebra(split_fields);
	assert #A`NumberFields eq #AA`NumberFields;
	map_AtoAA:=map< A -> AA | x :-> &+[AA`NumberFields[i][2](split_fields_embeddings[i](Components(x)[i])) : i in [1..#AA`NumberFields]]>;
	return AA, map_AtoAA;
end intrinsic;

intrinsic PrimitiveElement(A::AlgAss) -> AlgAssElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	return &+[L[2](PrimitiveElement(L[1])) : L in A`NumberFields];
end intrinsic;

intrinsic DefiningPolynomial(A::AlgAss) -> RngUPolElt
{ it returns an element which corresponds to the class of X in Q[X]/(f(X)) }
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	return &*[DefiningPolynomial(L[1]) : L in A`NumberFields];
end intrinsic;

intrinsic '^'(I::AlgAssVOrdIdl,n::RngIntElt) -> AlgAssVOrdIdl
{ compute the nth power of an ideal }
	S:=Order(I);
	power_positive:=function(I,n)
		id:=I;
		bin_exp:=IntegerToSequence(n,2);
		squares_id:=[ideal<S|One(S)>];
		for i in [1..#bin_exp] do
			if bin_exp[i] eq 1 then
				Append(~squares_id,id);
			end if;
			id:=id*id;
		end for;
		output:=squares_id[1];
		for i in [2..#squares_id] do
			output:=output*squares_id[i];
		end for;
		return output;
	end function;

	if n eq 0 then
		return ideal<Order(I)|One(Order(I))>;
	else
		if n gt 0 then
			return power_positive(I,n);
		end if;
		if n lt 0 then
			require IsInvertible(I) :"the ideal must be invertible";
			invI:=ColonIdeal(Order(I),I);
			return power_positive(invI,-n);
		end if;
	end if;
end intrinsic;

intrinsic IsProductOfOrders(O::AlgAssVOrd)->BoolElt, Tup
{return if the argument is a product of orders in a product of number fields, and if so return also the sequence of these orders}
	A:=Algebra(O);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	idem:=OrthogonalIdempotents(A);
	test:=forall{x : x in idem | x in O};
	O_asProd:=<>;
	if test then
		for i in [1..#A`NumberFields] do
			L:=A`NumberFields[i];
			gen_L:=[(x*idem[i])@@L[2]: x in ZBasis(O)];
			O_L:=Order(gen_L);
			Append(~O_asProd,O_L);
		end for;
		return true, O_asProd;
	else
		return false,<>;
	end if;
end intrinsic;

intrinsic IsProductOfIdeals(I::AlgAssVOrdIdl) -> BoolElt, Tup
{return if the argument is a product of ideals in a product of number fields, and if so return also the sequence of these ideals (in the appropriate orders)}
	O:=MultiplicatorRing(I);
	A:=Algebra(O);
	require IsFiniteEtale(A): "the algebra of definition must be finite and etale over Q";
	test,O_asProd:=IsProductOfOrders(O);
	I_asProd:=<>;
	if test then
		idem:=OrthogonalIdempotents(A);
		for i in [1..#A`NumberFields] do
			L:=A`NumberFields[i];
			gen_L:=[(x*idem[i])@@L[2]: x in ZBasis(I)];
			I_L:=ideal<O_asProd[i]|gen_L>;
			Append(~I_asProd,I_L);
		end for;
		return true, I_asProd;
	else
		return false,<>;
	end if;
end intrinsic;

intrinsic IsIsomorphic2(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> BoolElt, AlgAssElt
{checks if I=x*J, for some x. If so, also x is returned}
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	test:=IsWeakEquivalent(I,J); //if so I=(I:J)*J and (I:J) is invertible in its MultiplicatorRing
	if test then
		S:=MultiplicatorRing(I);
		IS:=ideal<S| ZBasis(I)>;
		JS:=ideal<S| ZBasis(J)>;
		CIJ:=ColonIdeal(IS,JS);
		test2,x:= IsPrincipal(CIJ);
		if test2 then
			return test2,x;
		else
			return false, _ ;
		end if;
	else
		return false , _ ;
	end if;
end intrinsic;

intrinsic Components(x::AlgAssElt) -> SeqEnum
{returns the components of the element as in the product of number fields}
	A:=Parent(x);
	require IsFiniteEtale(Parent(x)): "the algebra of definition must be finite and etale over Q";
	idem:=OrthogonalIdempotents(A);
	x_asProd:=[**];
	for i in [1..#A`NumberFields] do
		L:=A`NumberFields[i];
		x_L:=(x*idem[i])@@L[2];
		Append(~x_asProd,x_L);
	end for;
	return x_asProd;
end intrinsic;

intrinsic TraceDualIdeal(I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{ returns the trace dual ideal of an ideal in an order in an associative algebra }
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	S:=Order(I);
	B:=ZBasis(I);
	n:=#B;
	Q:=MatrixRing(RationalField(), n)![Trace(B[i]*B[j]): i, j in [1..n] ];
	QQ:=Q^-1;
	BB:=[&+[ (QQ[i,j]*B[j]): j in [1..n]] : i in [1..n]] ;
	return ideal<S|BB>;
end intrinsic;

intrinsic TraceDualIdeal(O::AlgAssVOrd) -> AlgAssVOrdIdl
{ returns the trace dual ideal of an order in an associative algebra }
	require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
	I:=ideal<O|One(O)>;
	return TraceDualIdeal(I);
end intrinsic;

intrinsic IsFractionalIdl(I::AlgAssVOrdIdl) -> BoolElt
{ checks if the ideal is fractional, that is if contains a non-zero-divisor }
	require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
	num_gens:=#Generators(I); //note that the number of generators depends on the rank as an abelian group
	return num_gens eq Dimension(Algebra(I));
end intrinsic;

intrinsic IsMaximal(O::AlgAssVOrd) -> BoolElt
{ checks if the order is the maximal order of its associative algebra}
	A:=Algebra(O);
	require IsFiniteEtale(Algebra(O)): "the algebra of definition must be finite and etale over Q";
	if assigned A`MaximalOrder then OK:=A`MaximalOrder; else OK:=MaximalOrder(Algebra(O)); A`MaximalOrder:=OK; end if;
	return (OK eq O);
end intrinsic;

intrinsic 'subset'(O1 :: AlgAssVOrd, O2 :: AlgAssVOrd) -> BoolElt
{Checks if the first argument is inside the second.}
	require Algebra(O1) cmpeq Algebra(O2) : "The orders must be in the same algebra.";
	assert (O1+O2 eq O2) eq (O1 meet O2 eq O1);
	return ((O1 meet O2) eq O1);
end intrinsic;

intrinsic 'subset'(I1 :: AlgAssVOrdIdl, I2 :: AlgAssVOrdIdl) -> BoolElt
{Checks if the first argument is inside the second. The ideals need to be fractional}
	require Order(I1) eq Order(I2) : "The ideals must be in the same order.";
	return ((I1 meet I2) eq I1);
end intrinsic;

function IdealsOfIndex(I,N)
// Given an ideal I in an order O in a number field and a positive integer N, with N coprime with the conductor, returns all the ideals J contained in I with index [I:J]=N.
// If N>1 the we require I to be invertible in O (we do not test it! since it is not implement for non-maximal orders)}
// 
// by Edgar Costa, modified by Stefano (since we cannot check all the required hyp I have changed into a function. The hyp on I (being invertible is checked in the intrinsic below)
	vprintf Ordersext : "IdealsOfIndex Int\n";
	if N eq 1 then
		return [I];
	end if;
	d := Denominator(I);
	O := Order(I);
	I := Order(I)!!(d*I);
	//assert IsIvertible(I); //not implement for non-maximal O :(
	ff:=Conductor(O);
	OK := MaximalOrder(NumberField(O));
	ffOK:=OK !! ff;
	index_OK_O := Index(OK, O);
	//require N gt 0 and GCD(index_OK_O, N) eq 1: "N must be a positive integer coprime with the conductor of O";
	//N is coprime with the conductor ff iff N is coprime with ind=[OK:O]. 
	//Pf: ff meet Z = exp(OK/O)=e and e|ind and ind|e^k for some k.
	Js := IdealsUpTo(N, OK); //IdealsUpTo works only for maximal orders.
	result := [];
	for J in Reverse(Js) do
		if Norm(J) eq N then
			assert J + ffOK eq 1*OK; //J should be coprime with the conductor. I added this assert because I couldn't check the code of IdealsUpTo
			K := (O meet J) * I; // OK/J=O/(J meet O)=I/K, where the second isomorphism holds because I is invertible in O (no need I to be coprime with ff).
			assert K subset I;
			Append(~result, K);
		else
			break; //the other ideals in Js will have norm < N.
		end if;
	end for;
	return [J/d : J in result]; //we reintroduce the denominator d.
end function;

function IdealsOfIndexProduct(Is, N)
// Given a list Is of ideals representing the ideal I as a product and positive integer N, returns all the ideals of index N.
// N has to be coprime with the conductor.
// If N>1 then I should be invertible (and hence all ideals in Is should be invertible). This we cannot check since it is implemented only for maximal orders.
//
// by Edgar Costa, modified by Stefano (since we cannot check all the required hyp I have changed into a function. The hyp on I (being invertible is checked in the intrinsic below)
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
end function;

intrinsic IdealsOfIndex(I::AlgAssVOrdIdl[RngOrd], N::RngIntElt : Al := "Default") -> SeqEnum[AlgAssVOrdIdl]
{Given an O-ideal I in O and integer N returns all the subideals of index N
 The function is very fast if N=1 or, N is coprime to the conductor of O and I is invertible in O. If this conditions are not satisfied a slow algorithm is used which doesn't require additional hypothesis.
 One can force the slow-naive by setting the vararg Al:="Naive".}
//by Stefano Marseglia and Edgar Costa
	if N eq 1 then
		return [I];
	end if;
	if Al eq "Naive" then
		test := false;
	elif not IsWeakEquivalent(I,1*Order(I)) //I is not invertible
	then
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
			Append(~result, ideal<Order(I) | gen_inA>);
		end for;
		return result;
	else
		result := [];
		vprintf Ordersext : "Naive version!!\n";
		// this is extremely NAIVE, but it always works.
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


//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
/*what follows overwrites "bugged" functions*/
//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

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

///////////////////TO WORK ON!!!!!!!!!!!!!!

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
          if not s*t in O then
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

function order_over(Z_F, S, I : Check := true)
  A := Universe(S);
  F := BaseRing(A);
  n := Dimension(A);
  if (A!1 notin S) then
    Append(~S, 1);
    Append(~I, 1*Z_F);
  end if;
  // Find an initial pseudobasis
  M := Matrix(F,#S,n, &cat[Eltseq(s) : s in S]);
  P := PseudoMatrix(I,M);
  P := HermiteForm(P);
  I := CoefficientIdeals(P);
  M := ChangeRing(Matrix(P),F);
  S := [A ! Eltseq(M[i]) : i in [1..Nrows(M)]];

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

  error if Rank(M_new) ne n,
         "The given elements don't generate a lattice of full rank";
  M := MatrixRing(F,n) ! M_new;
  I:=I_new;
  O := Order(A, M, I);

  assert IsOrder(O);
  return O;
end function;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : Check := true) -> AlgAssVOrd
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

intrinsic '+'(O1::AlgAssVOrd[RngOrd], O2::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
  {Computes the sum O1+O2, the smallest order containing both O1 and O2.}

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

intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl, AlgAssVOrdIdl
{Product of ideals I and J.}

  A:=Algebra(I);
  require IsFiniteEtale(A): "Arguments must be ideals of orders in an Finite Etale Algebra over Q";
  O:=Order(I);
  require A cmpeq Algebra(Order(J)) : "Arguments must be ideals of orders in the same algebra";
  require O cmpeq Order(J) : "Arguments must be ideals of orders in the same algebra";
//   require IsTwoSidedIdeal(I) and IsTwoSidedIdeal(J): "the ideals must be two-sided";

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


