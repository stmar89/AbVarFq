//load "C:/Users/tdupuy/Dropbox/computing/LMFDB/stephano-loose-code/graph_builder.m"
//load "C:/Users/tdupuy/Dropbox/computing/LMFDB/stephano-loose-code/graph_example.m"

AttachSpec("C:/Users/tdupuy/Dropbox/computing/AbVarFq/packages.spec");

stupid_graph := [ ];
for i in [1..10] do
    for j in [1..10] do
	    if i lt j then
		    Append(~stupid_graph,[i,j]);
	    end if;
    end for;
end for;

P<x> := PolynomialRing(Integers());
f:=x^6 + 3*x^4 - 11*x^3 + 15*x^2 + 125;
K:=AssociativeAlgebra(f);
F:=PrimitiveElement(K);
q:=5;
R:=Order([F,q/F]);

//Step 1: Compute the Order Graph
ordersR:=FindOverOrders(R);
n:=#ordersR;
ugly_graph:=ugly_order_graph(ordersR);
//ugly_graph; will output the correct thing
pretty_order_graph := simplify_graph(ugly_graph,n);

/*

> [3,6] in pretty_order_graph;
true

> ordersR[3] subset ordersR[6];
true

*/

//Step 2: Weak Equivalence Classes
weak_classes := [* *];
for i in [1..n] do
    Append(~weak_classes,WKICM_bar(ordersR[i]));
end for;

for edge in pretty_order_graph;
    for I in weak_classes[i] and J in weak_classes[j] do
	    isog
    
    


