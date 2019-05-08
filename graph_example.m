
/*
THIS CODE USES STEFANO MARSEGLIA'S LIBRARY TO GENERATE ISOGENY GRAPHS OF CURVES. 
TO RUN IT, OPEN A MAGMA TERMINAL AND EXECUTE
    load "C:/Users/tdupuy/Dropbox/computing/AbVarFq/graph_example.m"
THE VERTICES OF THE GRAPH ARE INDEXED WITH LABELS [[i,j], d] WHERE i IS THE INDEX
OF THE ORDER/ENDOMORPHISM ALGEBRA AND j IS THE INDEX OF THE WEAK EQUIVALENCE CLASS IN THAT ORDER.
THE ORDERING IS JUST CURRENTLY DETERMINED BY WHAT STEPHANO'S CODE OUTPUTS SO DOESN'T DO MUCH. 

TODO: 
-COMBINE WITH EDGAR'S FUNCTIONS FOR COMPUTING ISOGENIES
-DO THE HORIZONTAL ISOGENIES
-COMPUTE ISOGENIES ACROSS PRIME ORDERS. 
-THEORETICAL: FIGURE OUT A MINIMAL SET OF ISOGENIES NEEDED TO GENERATE THE GRAPH. 

IN THE FUTURE WE WILL REPLACE THE VERTICIES OF THE GRAPH WITH THE LMFDB LABELS.

DISPLAYS DURING THE MEETING 02/03/2019 WERE DONE BY MODIFYING THE OUTPUT DATA BY HAND IN COCALC.
IF YOU WANT TO SEE THESE EMAIL ME. 

TAYLOR DUPUY 02/02/2019

/*



AttachSpec("C:/Users/tdupuy/Dropbox/computing/AbVarFq/packages.spec");
load "C:/Users/tdupuy/Dropbox/computing/AbVarFq/graph_builder.m";

//f:=x^6 + 3*x^4 - 11*x^3 + 15*x^2 + 125;
// f:=x^6 - x^5 + 6*x^4 + 4*x^3 + 30*x^2 - 25*x + 125 //Bass Example
//f:=27-9*x-4*x^3-x^5+x^6; (for q=5 this gave a good bug) (q=3, this is integrally closed)
//f:= 27-9*x-3*x^2 +3*x^3 -2*x^4-x^5+x^6 //Also integrally closed.
//f:= x^6−2*x^4−2*x^2−6*x^2+27
// Irreducible, Non-Bass, Small Number of Orders
//f:= x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125 //Really Fast at finding orders!
//f:= x^6 - 3*x^4 + 4*x^3 - 15*x^2 + 125
//f:= x^6 + 3*x^4 - 8*x^3 + 15*x^2 + 125
//f:= x^6 + 3*x^4 + 8*x^3 + 15*x^2 + 125
//f:= x^6 + 5*x^4 - 4*x^3 + 25*x^2 + 125
//f:= x^6 + 5*x^4 + 4*x^3 + 25*x^2 + 125
//f:= x^6 + x^4 - 12*x^3 + 5*x^2 + 125
//g:=Degree(f)/2
//q:=Evaluate(f,0);


P<x> := PolynomialRing(Integers());
f:= x^6 - 3*x^4 - 4*x^3 - 15*x^2 + 125;
is_weil, q := IsWeil(f); //Maybe on works from primes, need to test on prime powers.
IsIrreducible(f);
g:= Degree(f)/2;
K:=AssociativeAlgebra(f);
F:=PrimitiveElement(K);
R:=Order([F,q/F]);

//Step 1: Compute the Order Graph
ordersR:=FindOverOrders(R);
n:=#ordersR;
ugly_graph:=ugly_order_graph(ordersR);
//ugly_graph; will output the correct thing
pretty_order_graph := simplify_graph(ugly_graph,n);

//IF INDEX IS TO BE ADDED TO A WEIGHT OF THE SUBRING LATTICE
// USE THIS: [Index(MaximalOrder(K),S) : S in ordersR];
// TOGETHER WITH THE TOWER RELATION

//IN BETWEEN THE TWO PROCESSES ABOVE WE WILL WANT TO 
//ADD THE INDEX OF EACH OF THE SUBGROUPS.

//Step 2: Weak Equivalence Classes
//for each order count the number of weak classes 
weak_classes := [* *];
weak_class_numbers := [];
for i in [1..n] do
    weak_class := WKICM_bar(ordersR[i]);
	weak_class_number := #weak_class;
    Append(~weak_classes,[* i,weak_class *]);
	Append(~weak_class_numbers,weak_class_number);
end for;

//Step 3: Isogenies Between Representatives of Weak Equiavalence Classes
/*

vertical_isogeny_data := [* *];
//THE OUTPUT OF THIS PROCEDURE IS HORRENDOUS, I ADDED SOME CODE TO CLEAN IT UP BELOW. 
for edge in pretty_order_graph do
    w1 := weak_classes[edge[1]]; w2 := weak_classes[edge[2]];
	h1 := weak_class_numbers[edge[1]]; h2 := weak_class_numbers[edge[2]];
	edge_data := [* *];
	for i in [1..h1] do
  	    for j in [1..h2] do
	    I1 := w1[2][i]; I2:= w2[2][j];
	    I1R := ideal<R|ZBasis(I1)>; 
		I2R := ideal<R|ZBasis(I2)>;
	    short_isogs := GetShortIsogs(I1R,I2R);
		Append(~edge_data, [* [i,j], short_isogs *]);
		end for;
	end for;
    Append(~vertical_isogeny_data,[* edge,edge_data *] );	
end for;

vertical_isogeny_graph := [* *];
//CLEAN UP TO GIVE A WEIGHTED GRAPH
for entry in vertical_isogeny_data do
    order_index1 := entry[1][1];
	order_index2 := entry[1][2];
	weak_entries := entry[2];
	for weak_entry in weak_entries do
		weak_index1:= weak_entry[1][1];
	    weak_index2:= weak_entry[1][2];
		isog_degree:= weak_entry[2][1][2];
		new_edge := [* [order_index1,weak_index1], [order_index2,weak_index2], isog_degree *];
		Append(~vertical_isogeny_graph,new_edge);
	end for;
end for;


/* SOME TEST CODE FOR BUILDING THE GRAPHS
w1 := weak_classes[myedge[1]];
w2 := weak_classes[myedge[2]]; //first entry of this is index of order, second is the representatives of the classes
I1:=w1[2][1]; w2[2][1];
I1:=w1[2][1]; I2:=w2[2][1];
I2R := ideal<R| ZBasis(I2)>;
I1R := ideal<R| ZBasis(I1)>;
Hom12 := ColonIdeal(I1R,I2R);
edge_data := [* *]
short_elements := Find_Shortest_Elements(Hom12);
ele := short_elements[1][1];
*/

/* SOME OUTPUT I DONT UNDERSTAND: THE BOUND WE ARE USING IS BASED ON THE GEOMETRIC-ARITHMETIC MEAN INEQUALITY. 
Trace(ele);
12
> Norm(ele);
64
> Trace(ele*ComplexConjugate(ele));
24
> ele*I2 subset I1;
>> ele*I2 subset I1;
          ^Runtime error: The ideals must be in the same order.
> ele*I2R subset I1R;
true
> Index(I1R,ele*I2R);
64
*/


/*	TEST CODE FOR PRODUCING THE SMALLEST ISOGENY IN AN EXAMPLE 
--- THIS ONE TURNED OUT TO BE REDUCIBLE BUT WORKS FOR ONE OF THE WEIL POLYNOMIALS LISTED ABOUT
w1 := weak_classes[3]; w2 := weak_classes[6];
I3 := w3[2][1]; I6 := w6[2][1];
I3R := ideal<R| ZBasis(I3) >;
I6R := ideal<R| ZBasis(I6) >;
Hom36 := ColonIdeal(I3R,I6R);
hom_basis := ZBasis(Hom36);
gram_matrix_data :=[];
for v in hom_basis do
    new_row := [Trace(v*ComplexConjugate(w)) : w in hom_basis];
	Append(~gram_matrix_data, new_row);
end for;
Gram := Matrix(gram_matrix_data);
ZZGram := ChangeRing(Gram,Integers());
L := LatticeWithGram(ZZGram);
shorts := ShortestVectors(L);
Norm(shorts[1]); //This was 12
element := &+[ shorts[1][i]*hom_basis[i] : i in [1..g]];
Hom36_degree := Index(I3,element*I6);
*/










/*
AN UNTESTED IMPLEMENTATION OF CODE USING WHAT EDGAR WAS WORKING ON 

vertical_isogeny_graph_data := []
for edge in pretty_order_graph do
    for k in [1..weak_class_number[i]] and l in [1..weak_class_number[j]] do
	    isogs := Isogenies(I,J,2);
		if #isos ne 0 then 
		    Append(vertical_isogeny_graph_data, [edge, [ [l,k], isogs ] ]);
		end if; 
	end for;
end for;
*/ 




/*
EXAMPLES: 
> [3,6] in pretty_order_graph;
true
> ordersR[3] subset ordersR[6];
true

>Matrix(gram_matrix_data);
[ 2 -1  2 -1  2  2]
[-1 10 -1 10 -1 -1]
[ 2 -1  6  0  2  4]
[-1 10  0 30  7 -8]
[ 2 -1  2  7 16 -3]
[ 2 -1  4 -8 -3  8]


>element*Generators(I6)[2] in I3;
true
*/

/* JUNK CODE I WAS USING TO BUILD THE ISOGENY FUNCTION. 
hom_basis := ZBasis(Hom36);
gram_matrix_data :=[];
for v in hom_basis do
    new_row := [Trace(v*ComplexConjugate(w)) : w in hom_basis];
	Append(~gram_matrix_data, new_row);
end for;
Gram := Matrix(gram_matrix_data);
ZZGram := ChangeRing(Gram,Integers());
L := LatticeWithGram(ZZGram);
shorts := ShortestVectors(L);
Norm(shorts[1]); //This was 12
element := &+[ shorts[1][i]*hom_basis[i] : i in [1..6]];
*/

