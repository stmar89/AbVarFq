/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Abelian varieties and Isogeny classes
// Stefano Marseglia, Utrecht University, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose AbelianVarieties, 1;

declare attributes AbelianVarietyFq : IsogenyClass;

/////////////////////////////////////////////////////
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic IsogenyClass( A::AbelianVarietyFq) -> IsogenyClassFq
{Returns the isogeny class of the given abelian variety.}
    return A`IsogenyClass;
end intrinsic;

intrinsic WeilPolynomial(A::AbelianVarietyFq )-> RngUpolElt
{Given an isogeny class AV(h) returns the Weil polynomial h defining it.}
    return WeilPolynomial(IsogenyClass(A));
end intrinsic;

intrinsic FiniteField( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the size of the finite field of definition.}
    return FiniteField(IsogenyClass(A));
end intrinsic;

intrinsic CharacteristicFiniteField( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the characteristic of the finite field of definition.}
    return CharacteristicFiniteField(IsogenyClass(A));
end intrinsic;

intrinsic Dimension( A :: AbelianVarietyFq )-> RngInt
{Given an isogeny class AV(h) returns the dimension.}
    return Dimension(IsogenyClass(A));
end intrinsic;

intrinsic UniverseAlgebra( A :: AbelianVarietyFq) -> AlgAss
{Returns the UniverseAlgebra where the DeligneModule lives in.}
    return UniverseAlgebra(IsogenyClass(A));
end intrinsic;

intrinsic ZFVOrder( A :: AbelianVarietyFq) -> AlgAssVOrd,Map
{Returns the ZFV of the isogeny class of A.}
    return ZFVOrder(IsogenyClass(A));
end intrinsic;

