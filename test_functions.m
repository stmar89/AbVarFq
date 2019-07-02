/*TEST functions*/

/////////////////////////////////////////////////////
// test functions for the other packages
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

find_all_princ_pol_ab:=function(A,phi)
  f:=DefiningPolynomial(A);
  q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
  F:=PrimitiveElement(A);
  V:=q*F^-1;
  E:=Order([V,F]);
  seqOO:=FindOverOrders(E);
  ICM_conjstable:=&cat[[ ideal<E| ZBasis(I)> : I in ICM_bar(S)] : S in seqOO | ComplexConjugate(S) eq S ];
  output:=[];
  for I in ICM_conjstable do
    test,pols:=IsPrincPolarized(I,phi);
    if test then 
      Append(~output, < I, pols, #AutomorphismsPol(I)  >);
    end if;
  end for;
  return output;
end function;

intrinsic RunTests() -> BoolElt
{ a bunch of checks }
    test:=true;
    time_begin:=Realtime();
    R<x>:=PolynomialRing(Integers());

    list_of_poly:=[
//     x^3 - 1000*x^2 - 1000*x - 1000, //domain with 25 wk classes, but very big ICM, should be 69116, but attention to the BUG!!!!
    x^3+31*x^2+43*x+77, //domain with 23 wk classes and 59 iso classes
    elt<R|[4, -6, 6, -3, 1]>, //not all OverOrders of E are products
    elt<R|[ 8, -20, 26, -22, 13, -5, 1 ]> //non trivial PicardGroups, not all OverOrders of E are prodcuts
//     (x^2+5)*(x^2+191) //E not a product //problems with the CRT
 //   need and example with non-cyclic PicardGroups
    ];
    for f in list_of_poly do
        K:=AssociativeAlgebra(f);
        E:=EquationOrder(K);
        O:=MaximalOrder(K);
//         seqOO:=FindOverOrders(E); #seqOO;
        U,u:=UnitGroup2(O);
        GE,gE:=PicardGroup(E);
".";        
    end for;
    
    f:=x^4-1000*x^3-1000*x^2-1000*x-1000;
    K:=AssociativeAlgebra(f);
    E:=EquationOrder(K);
    SeqWC:=WKICM(E);
    if #SeqWC ne 25 then
      test:=false;
      printf"\nERROR: SeqWC of f=%o\n",f;
    end if;
".";
    f:=x^4+291*x^3-988*x^2-1000*x-1000;
    K:=AssociativeAlgebra(f);
    E:=EquationOrder(K);
    SeqWC:=WKICM(E);
    if #SeqWC ne 20 then
      test:=false;
      printf"\nERROR: SeqWC of f=%o\n",f;
    end if;
".";
    f:=x^3+31*x^2+43*x+77;
    K:=AssociativeAlgebra(f);
    E:=EquationOrder(K);
    if #FindOverOrders(E) ne 15 then 
      test:=false;
      printf"\nERROR: OverOrders of f=%o\n",f;
    end if;
    SeqWC:=WKICM(E);
    if #SeqWC ne 23 then
      test:=false;
      printf"\nERROR: SeqWC of f=%o\n",f;
    end if;
 ".";
    f:=x^4+4*x^3+6*x^2+44*x+121;
    K:=AssociativeAlgebra(f);
    cm:=CMType(K);
    if #cm ne 1 then
      test:=false;
      printf"\nERROR: CMType of f=%o\n",f;
    end if;
    phi:=cm[1];
    SeqPpol:=find_all_princ_pol_ab(K,phi);      
    SeqAut:=[I[3] : i in I[2] , I in SeqPpol];
    if #SeqAut ne 10 or &+SeqAut ne 28 then
      test:=false;
      printf"\nERROR: SeqAut of f=%o\n",f;
    end if;
".";
    f:=x^6-2*x^5-3*x^4+24*x^3-15*x^2-50*x+125;
    K:=AssociativeAlgebra(f);
    cm:=CMType(K);
    if #cm ne 1 then
      test:=false;
      printf"\nERROR: CMType of f=%o\n",f;
    end if;
    phi:=cm[1];
    SeqPpol:=find_all_princ_pol_ab(K,phi);      
    SeqAut:=[I[3] : i in I[2] , I in SeqPpol];
    if #SeqAut ne 8 or &+SeqAut ne 20 then
      test:=false;
      printf"\nERROR: SeqAut of f=%o\n",f;
    end if;
".";
    f:=elt<R|[81,-135,117,-75,44,-25,13,-5,1]>;
    K:=AssociativeAlgebra(f);
    cm:=CMType(K);
    if #cm ne 1 then
      test:=false;
      printf"\nERROR: CMType of f=%o\n",f;
    end if;
    phi:=cm[1];
    SeqPpol:=find_all_princ_pol_ab(K,phi);      
    SeqAut:=[I[3] : i in I[2] , I in SeqPpol];
    if #SeqAut ne 10 or &+SeqAut ne 28 then
      test:=false;
      printf"\nERROR: SeqAut of f=%o\n",f;
    end if;
".";

//TEST errors_from_old_computations
    poly_list:=[
    x^4+x^2+529,

    x^4+11*x^3+73*x^2+319*x+841,
    x^4-4*x^3+8*x^2-116*x+841,
    x^4+4*x^3+8*x^2+116*x+841,
    x^4-17*x^2+841,

    x^4-x^3+26*x^2-31*x+961,
    x^4-6*x^3+43*x^2-186*x+961,
    x^4-4*x^3+8*x^2-124*x+961,
    x^4+2*x^3+52*x^2+62*x+961,
    x^4+x^3+26*x^2+31*x+961
    ];
    results:=[Rationals() | ];
for f in poly_list do
    K:=AssociativeAlgebra(f);
    cm:=CMType(K);
    if #cm ne 1 then
      test:=false;
      printf"\nERROR: CMType of f=%o\n",f;
    end if;
    phi:=cm[1];
    SeqPpol:=find_all_princ_pol_ab(K,phi);      
    SeqAut:=[I[3] : i in I[2] , I in SeqPpol];
    Append(~results,&+[1/n : n in SeqAut]);
    results;
".";
end for;
results_correct:=[25,31/2,25,25,28,16,40,53/4,31,16];
if not results eq results_correct then
    test:=false;
    printf"\nerrors_from_old_computations\n",f;
end if;
     time_used:=(Integers() ! Round(Realtime(time_begin)));
     hours_used:=time_used div (60*60);
     time_used:=time_used-hours_used*3600;
     min_used:=time_used div 60;
     sec_used:=time_used - min_used*60;
     printf"\nTotal time for tests: %o h, %o m, %o s\n",hours_used,min_used,sec_used;
     if test then printf"\n!Congratulations! All tests passed.\n"; end if;
     return test;
end intrinsic;
