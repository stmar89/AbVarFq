/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Abelian varieties and Isogeny classes
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

declare attributes AbelianVarietyFq : EndomorphismRing;

/////////////////////////////////////////////////////
// Dual Abelian Variety 
/////////////////////////////////////////////////////

intrinsic DualAbelianVariety(A::AbelianVarietyFq)->AbelianVarietyFq
{Given an abelian variety A returns the dual abelian variety. The isogeny class needs to be ordinary or Centelghe-Stix.}
    require IsOrdinary(A) or CentelegheStix(IsogenyClass(A)): "implemented only for ordinary/CentelgehsStix isogeny classes";
    B:=ZBasis(DeligneModule(A));
    n:=#B;
    Q:=Matrix([[Trace(B[i]*B[j]): i in [1..n] ] : j in [1..n]]);
    QQ:=Q^-1;
    BB:=[&+[ (QQ[i,j]*B[j]): j in [1..n]] : i in [1..n]] ;
    BBc:=[ ComplexConjugate(b) : b in BB ];
    Av:=AbelianVariety(IsogenyClass(A),BBc); //the direct sum of ideal is not computed here
    return Av;
end intrinsic;
