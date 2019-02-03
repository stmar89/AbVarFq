//run this
//AttachSpec("packages.spec"); 

/*
1) Enumerate the lattice of orders between R=ZZ[F,V] and OK as a graph

2) For each S in Order, compute Weak Equivalence classes for S

3) For [S,T] adjacent in lattice with T above S, and each [IS,IT] pair 
of weak equivalence representatives, compute find minimal elements 
of (IS:IT)

4) Span by Picards. THIS STEP IS NOT IMPLEMENTS

WE ALSO NEED TO FIND ISOGENIES GOING BACKWARDS AND BETWEEN HORIZONTAL COMPONENTS. 
IT WOULD ALSO BE NICE TO SEE HOW DUALIZING AND THE FROBENIUS WORK IN THIS CONTEXT. 
*/

AttachSpec("C:/Users/tdupuy/Dropbox/computing/AbVarFq/packages.spec");
load "C:/Users/tdupuy/Dropbox/computing/LMFDB/stephano-loose-code/graph_builder.m"


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
    return Index(I,alpha*J);
end function;

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
    shorts := ShortestVectors(L);
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

//run this to test the simplify graph function

*/