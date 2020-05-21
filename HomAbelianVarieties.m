/* vim: set syntax=magma :*/

freeze;

/////////////////////////////////////////////////////
// Morphisms of Abelian varieties over Finite Fields
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
// with the help of Edgar Costa
/////////////////////////////////////////////////////

declare verbose HomAbelianVarieties, 1;




/////////////////////////////////////////////////////
// NewType: HomAbelianVarietyFqA
// a morphism of abelin varieties over Fq
/////////////////////////////////////////////////////

declare type HomAbelianVarietyFq;
declare attributes HomAbelianVarietyFq : Domain,
                                         Codomain,
                                         // Image, //does it makes sense?
                                         // Kernel, //what should this be? 
                                         MapOnUniverseAlgebras,
                                         IsIsogeny, // a pair true or false, Degree
                                         IsIsomorphism,
                                         IsEndomorphism;

/////////////////////////////////////////////////////
// Access, Print 
/////////////////////////////////////////////////////

intrinsic Print(m::HomAbelianVarietyFq)
{ print the morphism abelian variety }
    printf "Morphism from %o to %o",Domain(m),Codomain(m);
end intrinsic;

intrinsic Domain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the domain the morphism}
    return m`Domain;
end intrinsic;

intrinsic Codomain(m::HomAbelianVarietyFq)->AbelianVarietyFq
{returns the codomain the morphism}
    return m`Codomain;
end intrinsic;

intrinsic MapOnUniverseAlgebras(m::HomAbelianVarietyFq)->Map
{returns underlying homormorphism of Deligne Moduels as a Z[F,V]-linear hom on the UniverseAlgebras}
    return m`MapOnUniverseAlgebras;
end intrinsic;

intrinsic IsEndomorphism(m::HomAbelianVarietyFq)->BoolElt 
{returns whether the morphism is an endomorphism}
    if not assigned m`IsEndomorphism then
        m`IsEndomorphism:=Domain(m) eq Codomain(m);
    end if;
    return m`IsEndomorphism;
end intrinsic;

// intrinsic IsIsogeny(m::HomAbelianVarietyFq)->BoolElt,RngInt
// {returns whether the morphism is an isogeny and if so it returns also the degree}
//     if not assigned m`IsIsogeny then
//         if IsogenyClass(Domain(m)) ne IsogenyClass(Codomain(m)) then
//             return false,_;
//         else
//             h:=MapOnUniverseAlgebras(m);
//             A:=UniverseAlgebra(Domain(m));
//             //TODO
//         end if;
//     end if;
//     return m`IsIsogeny[1],m`IsIsogeny[2];
// end intrinsic;

// TODO IsIsogeny, Degree, IsIsomorphsim 

/////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////

intrinsic Hom(A::AbelianVarietyFq,B::AbelianVarietyFq,map::Map : Check:=true)->HomAbelianVarietyFq
{ creates a morphisms of abelian varieties A->B determined by map, where map is a morphisms of the universe algebras of A and B 
  The vararg Check allows to skip the test of the compatibility with the Frobenius
}
    if Check then
        FA:=MapOnUniverseAlgebras(FrobeniusEndomorphism(A));
        FB:=MapOnUniverseAlgebras(FrobeniusEndomorphism(B));
        UA:=UniverseAlgebra(A);
        require UA eq Domain(map) and UniverseAlgebra(B) eq Codomain(map) and 
                forall{ i : i in [1..Dimension(UA)] | map(FA(UA.i)) eq FB(map(UA.i)) } //the map must be Frobanius-linear
                          : "the map does not define a morphism of abelian varieties";
    end if;
    hom:=New(HomAbelianVarietyFq);
    hom`Domain:=A;
    hom`Codomain:=B;
    hom`MapOnUniverseAlgebras:=map;
    return hom;
end intrinsic;

/////////////////////////////////////////////////////
// Frobenius
/////////////////////////////////////////////////////

intrinsic FrobeniusEndomorphism(A::AbelianVarietyFq)-> HomAbelianVarietyFq
{ returns the Frobenius endomorphism (acting on the UniverseAlgebra) }
    if not assigned A`FrobeniusEndomorphism then
        FUA:=FrobeniusEndomorphism(IsogenyClass(A));
        A`FrobeniusEndomorphism:=Hom(A,A,FUA : Check:=false ); //the Check:=false is necessary to prevent a loop
    end if;
    return A`FrobeniusEndomorphism;
end intrinsic;



// TEST see AbelianVarieties.m
