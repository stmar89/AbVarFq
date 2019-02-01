/**/

/////////////////////////////////////////////////////
// useful functions for the otehr packages
// Stefano Marseglia, Stockholm University, stefanom@math.su.se
/////////////////////////////////////////////////////

/*
LIST of functions
AllPossibilities := function(S)
*/

AllPossibilities := function(S)
    N:=&*[#s : s in S];
    r:=#S;
    Nhat:=[1];
    for i in [1..r] do
//       Append(~Nhat, &*Nhat*#(S[i])); //this seems wrong.
         Append(~Nhat, Nhat[#Nhat]*#(S[i]));
    end for;
    //Nhat=[1,n_1,n_1*n_2,n_1*n_2*n_3, ..... , \prod_{i=1}^r(n_i)], i.e. Nhat[k] = \prod_{i=0}^(k-1)(n_i), with n_0=1
    all_possibilities:=[];
    for i in [0..N-1] do
      out:=[* *];
      for k in [1..r] do
        i_k:= Integers() ! (((i mod Nhat[k+1]) - (i mod Nhat[k])) / Nhat[k]);
        Append(~out,S[k][i_k+1]);
      end for;
      Append(~all_possibilities,out);
    end for;
    assert #all_possibilities eq N;
    return all_possibilities;
end function;