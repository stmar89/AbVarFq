//run this
//AttachSpec("packages.spec"); load "C:/Users/tdupuy/Dropbox/computing/LMFDB/stephano-loose-code/graph_builder.m"
//

/*

1) Enumerate the lattice of orders between R=ZZ[F,V] and OK as a graph

2) For each S in Order, compute Weak Equivalence classes for S

3) For [S,T] adjacent in lattice with T above S, and each [IS,IT] pair 
of weak equivalence representatives, compute find minimal elements 
of (IS:IT)

4) Span by Picards. 

*/


function ugly_order_graph(orders)
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