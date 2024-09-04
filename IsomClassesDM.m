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

intrinsic IsIsomorphic(A1::AbelianVarietyFq,A2::AbelianVarietyFq) -> BoolElt,HomAbelianVarietyFq
{Checks if two abelin varieties are isomorphic and eventually it returns also a Z[F,V]-linear isomorphism from the common UniverseAlgebra.}
    vprintf AbelianVarieties,1 : " IsIsomorphic :";
    I:=IsogenyClass(A1);
    if I eq IsogenyClass(A2) then
        if IsOrdinary(I) or IsCentelegheStix(I) then
            test,map:=IsIsomorphic(DeligneModule(A1),DeligneModule(A2));
            if test then
                return true,Hom(A1,A2,map);
            else
                return false;
            end if;
        elif IsSquarefree(I) then
            error "TODO"; 
        else
            error "not implemented"; 
        end if; 
    else
        vprintf AbelianVarieties : "IsIsomorphic : the abelian varities are not in the same isogeny class \n";
        return false,_;
    end if;
end intrinsic;

/////////////////////////////////////////////////////
// Compute all isomorphism classes in a given Isogeny class
/////////////////////////////////////////////////////

intrinsic ComputeIsomorphismClasses( AVh::IsogenyClassFq )->SeqEnum[AbelianVarietyFq]
{Computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class.}
    if not assigned AVh`IsomorphismClasses then
        h:=WeilPolynomial(AVh);
        R,map:=ZFVOrder(AVh);
        if IsOrdinary(AVh) or IsCentelegheStix(AVh) then
            isom_DMs:=IsomorphismClasses(R,map);
            AVh`IsomorphismClasses:=[AbelianVariety(AVh,M):M in isom_DMs];
        elif IsSquarefree(AVh) then
            error "TODO"; 
        else
            error "not implemented for such an isogeny class"; 
        end if;
    end if;
    return AVh`IsomorphismClasses;
end intrinsic;

//intrinsic ComputeIsomorphismClassesWithEndomorphismRing( AVh::IsogenyClassFq , S::AlgAssVOrd )->SeqEnum[AbelianVarietyFq]
//{ computes a list of representatives of isomorphisms classes of abelian varieties with endomorphism ring S in the given squarefree isogeny class }
//    require IsSquarefree(AVh) : "the given isogeny class is not squarefree ";
//    R,_:=ZFVOrder(AVh);
//    require R subset S : "the given order is not the endomorphism ring of an abelian variety in the given isogeny class";
//    if assigned AVh`IsomorphismClasses then
//        isoS:=[ A : A in ComputeIsomorphismClasses(AVh) | EndomorphismRing(A) eq S ];
//    else
//        isoS:=[ AbelianVariety(AVh,R!I) : I in ICM_bar(S) ];
//    end if;
//    return isoS;
//end intrinsic;
