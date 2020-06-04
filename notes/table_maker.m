/* vim: set syntax=magma : */
// 
//---David Roe, Stefano Marseglia 02/03/2019
/*
on the list from David Roe
For each isogeny class, write lines to two files

isomorphism_classes.txt (one line per ideal)
isog_label:frac_ideal:rep_type:is_reduced:cm_elt:is_product
e.g.
1.251.v:{{1,0},{0,1}}:0:f:{21,2}:f
isogeny_classes.txt (one line per class)
isog_label:order_is_bass:order_is_maximal:size
e.g.
1.251.v:t:t:9

*/

AttachSpec("packages.spec");

input:="easy.txt";

PP<x>:=PolynomialRing(Integers());

FOpen:=POpen("cat " cat input , "r");
s:=Gets(FOpen);
while not IsEof(s) do
    s;
	s1:=eval(s);
	isog_label:=s1[1];
	f:=PP ! s1[2];
	A:=AssociativeAlgebra(f);
	g:=Degree(f) div 2;
    q:=Integers() ! ((Coefficients(f)[1])^(2/Degree(f)));
    F:=PrimitiveElement(A);
    V:=q/F;
    R:=Order([F,V]);
    
    //if IsMaximal(R) then //already checked by David
            icm:=ICM(R);
            newbas:=[ V^(g-j) : j in [0..g] ] cat [ F^i : i in [1..g-1] ];
            
//isog_label:order_is_bass:order_is_maximal:size    
            order_is_bass:="1";
            order_is_maximal:="1";
            size:=Sprintf("%o",#icm);
            
            string_isog:=isog_label cat ":" cat order_is_bass cat ":" cat order_is_maximal cat ":" cat size  cat "\n";
            fprintf "isogeny_classes_easy.txt",string_isog;
            
            cm_elt:="\\N";


            for I in icm do            
                _,nI:=IsIntegral(I);
                I0:=nI*I;
                cc:=Coordinates(ZBasis(I0),newbas);
                strI:="{";
                for gen in cc do
                    strI:=strI cat "{";
                    for coord in gen do
                        strI:=strI cat Sprintf("%o,",coord);
                    end for;
                    strI:=Prune(strI) cat "},";
                end for;
                frac_ideal:=Prune(strI) cat "}";
                if IsProductOfIdeals(I) then 
                    is_product:="1";
                else
                    is_product:="0";
                end if;
                string:=isog_label cat ":" cat frac_ideal cat ":0:" cat cm_elt cat ":" cat is_product cat "\n";
                fprintf "isomorphism_classes_easy.txt",string;
            end for;
    //end if;
    s:=Gets(FOpen);
end while;
