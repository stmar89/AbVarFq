/*
This package includes functions do work with torsion-free R modules of finite rank, where R is a Bass order in an etale algebra K.Note that every such module M, say of rank r, is R-isomorphic to a direct sum of r fractional ideals of R.
Also two such modules, I_1+...+I_r and J_1+...+J_r are R-isomorphic if and only if for every i=1,..,r we have (I_i:I_i)=(J_i:J_i) and the Steinintz classes are R-isomorphic, that is there is a non-zero divisor x  of K such that \prod_iI_i=x*\prod_iJ_i.
In particular, every module of rank is R-isomorphic to S_1+...+S_{r-1}+I with (I:I)\supseteq S_{r-1}.
We use this results to produce functions to list representatives of all classes and to check whether two modules are R-isomorphic

It requires Ordersext. and Picardext. and AbelianVarieties.

LIST OF FUNCTIONS
chains_of_overorders:=procedure(r,~chain,~all_chains)
direct_sums_overorders:=function(R,r)
intrinsic SteinitzClass(bc::Tub)->AlgAssVOrdIdl
intrinsic AllBassClasses(R::AlgAssVOrd, r::RngIntElt)->SeqEnum[AlgAssVOrdIdl]

*/

chains_of_overorders:=procedure(r,~chain,~all_chains)
	if #chain eq r then 
		Append(~all_chains,chain); 
	else
		T:=chain[#chain];        
		for S in FindOverOrders(T) do
			chain1:=chain;
			Append(~chain1,S);
			$$(r,~chain1,~all_chains);
		end for;
	end if;
end procedure;

direct_sums_overorders:=function(R,r)
//given a (Bass) order R and a rank r, it returns all sequences S_1,..,S_r where R\subseteq S_
	choo:=<>;
	oo:=FindOverOrders(R);
	for S in oo do
		ch:=<S>;
		chains_of_overorders(r,~ch,~choo);
	end for;
	return choo;
end function;

intrinsic AllBassClasses(R::AlgAssVOrd, r::RngIntElt)->SeqEnum[AlgAssVOrdIdl]
{Given a Bass order R and a rank r, it returns representatives of all the isormorphism classes of torsion-free R modules of rank r}
	require IsBass(R) : "the first input must be a Bass order";  
	require r gt 0 : "the second input must be a positive integer";  
	output:=<>;
	choo:=direct_sums_overorders(R,r);
	for ch in choo do
		P,p:=PicardGroup(ch[r]);
		pic:=[p(g) : g in P];
		ch_rem:=Prune(ch);
		for I in pic do
			Append(~output,Append(ch_rem,I));
		end for;
	end for;
	return output;
end intrinsic;

intrinsic SteinitzClass(bc::Tup)->AlgAssVOrdIdl
{returns the product of the fractional ideals in the input}
	S:=MultiplicatorRing(bc[1]);
	st:=&*[ideal<S|ZBasis(bc[i])> : i in [1..#bc] ];
	return st;
end intrinsic; 

intrinsic IsBassIsomorphic(bc1::Tup,bc2::Tup)->BoolElt,AlgAssElt
{Given two sequences of frational R-ideals, where R is a Bass order, it returns wheter their direct sums are R-isomorphic, and if that is the case also an element x that sends the Steinitz class of the first direct sum into the Steinintz class of the second direct sum. We require that the fractional ideals in the decomposition are ordered wrt MultiplicatorRings, i.e. (I1:I1) subseteq (I2:I2) ...}    
	assert #bc1 eq #bc2;
        N:=#bc1;
	assert forall{i : i in [1..N] | Algebra(bc1[i]) eq Algebra(bc2[i])};    
	S1i:=MultiplicatorRing(bc1[1]);
	S2i:=MultiplicatorRing(bc2[1]);
	for i in [1..N-1] do
		S1i_next:=MultiplicatorRing(bc1[i+1]);
		S2i_next:=MultiplicatorRing(bc2[i+1]);
		if i lt N then
			require S1i subset S1i_next and S2i subset S2i_next : "the fractional ideals should be permutated such that the MultiplicatorRings are in incresing order";
		end if;
		if not S1i eq S2i then
			return false,_;
		end if;
		S1i:=S1i_next;
		S2i:=S2i_next;
	end for;
	//the orders are the same
        st1:=SteinitzClass(bc1);
        st2:=SteinitzClass(bc2);
        return IsIsomorphic2(st1,st2);    
end intrinsic;


/*
//TESTS

AttachSpec("packages.spec");
Attach("packages/PowerBass.m");

_<x>:=PolynomialRing(Integers());
f:=x^6-x^5+2*x^4-2*x^3+4*x^2-4*x+8;
A:=AssociativeAlgebra(f);
F:=PrimitiveElement(A);
R:=Order([F,ComplexConjugate(F)]);
iso_cl:=AllBassClasses(R,3);
assert #iso_cl eq 6;
for cl in iso_cl do
        cl_dual:=< ComplexConjugate(TraceDualIdeal(I)) : I in  cl>;
        IsBassIsomorphic(cl,cl_dual);
end for;


_<x>:=PolynomialRing(Integers());
f:=x^4 + 3*x^3 + 8*x^2 + 39*x + 169;
A:=AssociativeAlgebra(f);
F:=PrimitiveElement(A);
q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
R:=Order([F,q/F]);
ver:=[62,97,144,206,286,387,512,664,846,1061];
res:=[#AllBassClasses(R,i) : i in [1..10]];
assert res eq ver;


*/
