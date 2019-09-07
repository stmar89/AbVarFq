//AttachSpec("packages.spec"); 

/*
by Taylor Dupuy

1) Enumerate the lattice of orders between R=ZZ[F,V] and OK as a graph

2) For each S in Order, compute Weak Equivalence classes for S

3) For [S,T] adjacent in lattice with T above S, and each [IS,IT] pair 
of weak equivalence representatives, compute find minimal elements 
of (IS:IT)

4) Span by Picards. THIS STEP IS NOT IMPLEMENTED

TODO: 
-Find smallest isogenies between horizontal components
-Find smallest isogenies between vertical components
-Dualize
-Frobenius twist
-Vershiebung twist 
*/


//********************************************************
//SORTING/LABELLING 
//********************************************************

/*
Pretty self explanatory, this is a bunch of functions for sorting and ordering our lists. 
Currently it allows us to apply a label for orders using the comparison with the basis [V^{g-1}, ..., 1, F, ... , F^{g}]. 
Many of the functions here require some other things to be run. 
I am assuming we are going to due this in the script that outputs the large tuples. 
*/


function CompareLowerTriangular(A,B)
/*
Magma Documentation On Comparison Functions:The comparison function C must take two arguments and return an integer less than, equal to, or greater than 0
according to whether the first argument is less than, equal to, or greater than the second argument 
*/

    n:=Nrows(A); 
    //Assumes that they are both square and dimensions of A,B same

    //TODO:add test to check to see if matrix is integer valued and lower triangular.
    for i in [1..n] do
	    for j in [1..i] do
    	    if A[i,j] gt B[i,j] then
	    	    return 1;
		    end if;
		    if A[i,j] lt B[i,j] then
		        return -1;
			end if;
		end for;
	end for;
	
	return 0;
end function;


function LeastCommonDenom(C)
/*
INPUT: Matrix with rational entries.
OUTPUT: Least common multiple of the denominators
*/
    list:=Eltseq(C);
	denoms:=[Denominator(x) : x in list];
	lcd := LeastCommonMultiple(denoms);
	return lcd;
end function;

function HNFify(I)
/*
INPUT: Order in an associative algebra
OUTPUT: d,A,H,T 
    -matrix A whose columns are its generators in terms of the lmfdb basis
	-integer d, the least common denominator of entries of A
	-lower triangular Hermite normal form, H
	-T the matrix such that dA*T = H
*/

/*
Assumes objects have been instantiated
f:=x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125; //or some choice
A:=AssociativeAlgebra(f);
is_weil, q := IsWeil(f);
g := Degree(f)/2;
K:= AssociativeAlgebra(f);
F:= PrimitiveElement(K);
V:= q/F;
R:= Order([F,q/F]);
OK := MaximalOrder(R);
std_beta := Reverse([V^i : i in [0..g-1]]) cat [F^i : i in [1..g] ]; 
chg_of_basis:=Transpose(Matrix(std_beta)); 
inverse_chg_of_basis:=chg_of_basis^-1;
*/	
    IR := ZBasis(I);
    gens_power:=Transpose(Matrix(IR));
    gens_lmfdb:=inverse_chg_of_basis*gens_power;
    d:=LeastCommonDenom(gens_lmfdb);
    n:=Nrows(gens_lmfdb); 
    M:=MatrixAlgebra(Integers(),n);
	gens_lmfdb_ZZ := d*gens_lmfdb;
    gens_lmfdb_ZZ := (M ! gens_lmfdb_ZZ);
    Ht,Tt := HermiteForm(Transpose(gens_lmfdb_ZZ)); // Tt At = Ht
    H := Transpose(Ht);
    T:= Transpose(Tt); // A*T = H (only allows col operations which act on the choice of basis for the ideal)
	return d,gens_lmfdb_ZZ,H,T;
end function;

function CompareLattices(I,J)
/*
Magma Documentation On Comparison Functions: The comparison function C must take two arguments and return an integer less than, equal to, or greater than 0.
according to whether the first argument is less than, equal to, or greater than the second argument 
*/

/*
Assumes objects have been instantiated
f:=x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125; //or some choice
A:=AssociativeAlgebra(f);
is_weil, q := IsWeil(f);
g := Degree(f)/2;
K:= AssociativeAlgebra(f);
F:= PrimitiveElement(K);
V:= q/F;
R:= Order([F,q/F]);
*/	
    dI, AI,HI,TI := HNFify(I);
    dJ, AJ,HJ,TJ := HNFify(J);

    if dI gt dJ then
        return 1;
    end if;
	
	return CompareLowerTriangular(HI,HJ);
end function;

function CompareOrders(O1,O2)
/*
Magma Documentation On Comparison Functions:The comparison function C must take two arguments and return an integer less than, equal to, or greater than 0.
according to whether the first argument is less than, equal to, or greater than the second argument 
*/
    
/*
Assumes objects have been instantiated
f:=x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125; //or some choice
is_weil, q := IsWeil(f);
g := Degree(f)/2;
K:= AssociativeAlgebra(f);
F:= PrimitiveElement(K);
V:= q/F;
R:= Order([F,q/F]);
OK := MaximalOrder(R);
std_beta := Reverse([V^i : i in [0..g-1]]) cat [F^i : i in [1..g] ]; 
chg_of_basis:=Transpose(Matrix(std_beta)); 
inverse_chg_of_basis:=chg_of_basis^-1;

*/	

//TODO: prove that this is a total order

    ind1 := Index(OK,O1);
    ind2 := Index(OK,O2);
    
	if ind1 gt ind2 then
        return 1;
    end if;

    if ind2 gt ind1 then
        return -1;
    end if;
	
	return CompareLattices(O1,O2);
	
end function;

//***************************************************
// DATA FUNCTIONS
//***************************************************


//function DeligneModuleGenerators();




//function PeriodLattice(IR):
//This might be wrong:
//Take Gram Matrix and Compare Diagonal Entries in LMFDB
//

//function DualAV(IR)
//Input needs to be over R
//returns the fractional ideal dual to IR, this is just the trace dual

//function FrobeniusTwist(IR)
//Input needs to be over R
//Relative Frobenius
//Note: This allows you to compute the base field F_q by iterating.



//******************************************
//Isogeny Graph Functions
//******************************************
/*
It turns out we can compute Hom(A,B) quite easily. 
If T(A) = I, and T(B)=J then Hom(A,B) is just the elements which map I into J, this is just (J:I).
Note that (J:I) is a lattice in K and hence isomorphic to one of the lattices in the database.
The isogenies of degree d are the elements of (J:I) giving an isogeny of degree d

Neron Sevari: Hom(A,A^t)
Picard Number: rank NS(A)

TODO: Move Edgar's Function Here

*/

function ugly_order_graph(orders)
//ADDING THE INDEX OF THE SUBGROUPS HERE WILL BE MESSY
    n := #orders;
	order_lattice := [ ];
    for i in [1..n] do
	    for j in [1..n] do
		    if orders[i] ne orders[j] and orders[i] subset orders[j] then
			    Include(~order_lattice,[i,j]);
			end if;
		end for;
	end for;
	return order_lattice;
end function;
		    
function simplify_graph(my_graph,n)
//input a graph on n vertices labeled 1 through n 
//and remove redundant edges
//TODO: We need to add functionality to add some functionality for the index
//[Index(MaximalOrder(K),S) : S in ordersR];
    clean_graph := my_graph;
    for edge in my_graph do
        for vertex in [1..n] do
	        if edge[1] ne vertex and edge[2] ne vertex and [edge[1],vertex] in clean_graph and [vertex,edge[2]] in clean_graph then
		        Exclude(~clean_graph,edge);
	        end if;
	    end for;
	end for;
	return clean_graph;
end function;

function trace_pairing(x,y)
    return Trace(x*ComplexConjugate(y));
end function;

function IsogDegree(I,J,alpha)
/*
Given two lattices inside K = Algebra(I) and Algebra(J) is computes the order. 
You may need to check that they are both considered over R = ZZ[F,1/F]
*/
    return Index(I,alpha*J); //I think this is just the norm too
end function;

//function Kernel(I,J,alpha)
/*
Find the group scheme of the kernel of a particular isogeny
*/



function FindShortestElements(J)
//Needs that Algebra(J) be a CM field with ComplexConjugationMethod.
//We use that the Minkowski Embedding is an isomorphism of lattices:
//we take 
//It uses that 
    g := Degree(Algebra(J));
    basis := ZBasis(J);
    gram_matrix_data :=[];
    for v in basis do
        new_row := [Trace(v*ComplexConjugate(w)) : w in basis];
	    Append(~gram_matrix_data, new_row);
    end for;
    Gram := Matrix(gram_matrix_data);
    ZZGram := ChangeRing(Gram,Integers());
    L := LatticeWithGram(ZZGram);
    shorts := ShortestVectors(L); //ShortVectors <- take a lattice and a number
    J_shorts := [];
	for short in shorts do
	    size :=0;
	    size:=Norm(short);
		element := &+[ shorts[1][i]*basis[i] : i in [1..g]];
		Append(~J_shorts,[element,size]);
	end for;
	return J_shorts;
end function;

function GetShortIsogs(IR,JR)
//Input needs to be over R
//returns short elements lambda such that lambda J subset I
	Hom12 := ColonIdeal(IR,JR);
	shortest_elements := FindShortestElements(Hom12);
	isogs := [* *];
	for short in shortest_elements do
	    isog := [* *];
	    isog := [* short[1],IsogDegree(IR,JR,short[1]) *];
	    Append(~isogs,isog);
	end for;
	
	return isogs;
end function;


/*EXAMPLE FOR SIMPLIFY GRAPH
stupid_graph := [ ];
for i in [1..10] do
    for j in [1..10] do
	    if i lt j then
		    Append(~stupid_graph,[i,j]);
	    end if;
    end for;
end for;
*/
//run this to test the simplify graph function


/*
//This is an old version of the HNFify code. The HNFify orders has been replaces by this. 

function HNFify(I)
//
//INPUT: fractional ideal (as returned from Stefano's code
//OUTPUT: A,H,T where 
//
//-A presentations of I in LMFDB form
//-H lower triangular integer valued matrix
//-T tranformation matrix 
//
//They satisfy A = H*T where A is the matrix we have in LMFDB form.



//Assumes objects have been instantiated
//P<x> :=PolynomialRing(Integers());
//f:=x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125; //or some choice
//A:=AssociativeAlgebra(f);
//is_weil, q := IsWeil(f);
//g := Degree(f)/2;
////K:= AssociativeAlgebra(f);
//F:= PrimitiveElement(K);
//V:= q/F;
//R:= Order([F,q/F]);
//std_beta := Reverse([V^i : i in [0..g-1]]) cat [F^i : i in [1..g] ]; 
//chg_of_basis:=Transpose(Matrix(std_beta)); 
//inverse_chg_of_basis:=chg_of_basis^-1;
	
    IR:=ZBasis(I);
    gens_power:=Transpose(Matrix(IR)); 
    gens_lmfdb:=inverse_chg_of_basis*gens_power;
    k := (Integers() ! g);
	k := 2*k;
    M := MatrixAlgebra(Rationals(),k); 
    gens_lmfdb_QQ:=(M ! gens_lmfdb);
    Ht,Tt := HermiteForm(Transpose(gens_lmfdb_QQ)); // Tt At = Ht
    H := Transpose(Ht);
    T:= Transpose(Tt); // A*T = H (only allows col operations which act on the choice of basis for the ideal)
	return gens_lmfdb_ZZ,H,T;
end function;

*/


