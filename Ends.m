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
// Access functions for AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic EndomorphismRing(A::AbelianVarietyFq)-> AlgAssVOrd
{Returns Endomorphism ring of the abelian variety.}
    require IsSquarefree(IsogenyClass(A)):"at the moment it is implemented only for squarefree abelian varieties";
    I:=IsogenyClass(A);
    if not assigned A`EndomorphismRing then
        if IsOrdinary(I) or IsCentelegheStix(I) then
            A`EndomorphismRing:=compute_multiplicator_overorder(DeligneModule(M));
        elif IsSquarefree(I) then
            error "TODO"; //from the new paper
        else
            error "not implemented yet";
        end if;
    end if;
    return A`EndomorphismRing;
end intrinsic;

