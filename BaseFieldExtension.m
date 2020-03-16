
//freeze;

/////////////////////////////////////////////////////
// Base Field Extension of IsogenyClassesFq and AbelianVarietiesFq
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

declare verbose BaseFieldExtension, 1;


// ------------------- //
// Instrinsic: Extend q-Weil Poly
// ------------------- //

intrinsic BaseFieldExtension( h::RngUPolElt, r::RngIntElt : prec:=3000) -> RngUPolElt
{ Given a q-Weil polynomial, it returns the polynomial hr which is the char poly of Frobenius of A\otimes F_(q^r) for each A in AV(h). The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    require r gt 0 : "the integer must be positive";
    CC:=ComplexField(prec);
    PP:=Parent(h);
    PPCC:=PolynomialRing(CC);
    roots:=Roots(h,CC);
    roots_ext:=&cat([ [s[1]^r : i in [1..s[2]] ] : s in roots ]);
    hrCC:=&*[ PPCC.1-ro : ro in roots_ext ];
    //assert forall{ c : c in Coefficients(hrCC) | IsWeaklyZero(Im(c)) and IsWeaklyZero(Abs(Re(c)-Round(Re(c)))) };
    return PP![Round(Re(c)) : c in Coefficients(hrCC)]; 
end intrinsic;

// ------------------- //
// Extend IsogenyClassFq
// ------------------- //

intrinsic BaseFieldExtension(AVh::IsogenyClassFq, r::RngIntElt : prec:=3000 )->IsogenyClassFq,Map
{ given an isogeny class AV(h) and a positive integer r, it returns the isogeny class AV(hr) and maps mUA from the UniverseAlgebra of the AV(h) to the one of AV(hr).
The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    hr:=BaseFieldExtension(WeilPolynomial(AVh),r : prec:=prec);
    AVhr:=IsogenyClass(hr);
    UAh:=UniverseAlgebra(AVh);
    UAhr:=UniverseAlgebra(AVhr);
    Rh,mh:=ZFVOrder(AVh);
    Rhr,mhr:=ZFVOrder(AVhr);
    Ah:=Algebra(Rh);
    Ahr:=Algebra(Rhr);
    fac:=Factorization(hr);
    g:=&*[ f[1] : f in fac ] ;
    s:=fac[1,2];
    assert IsSquarefree(g);
    assert g eq DefiningPolynomial(Ahr);
    assert Dimension(UAhr) eq Dimension(UAh);
    assert s eq (Dimension(UAhr) div Dimension(Ahr)); 
    t:=Dimension(UAh) div Dimension(Ah);
    s0:=s div t;
    // the next two lines are not very pretty
    Fh:=PrimitiveElement(Ah);
    new_basis_Ah:=&cat[ [Fh^j*(Fh^r)^i : i in [0..Degree(g)-1] ] : j in [0..s0-1] ];
    assert #new_basis_Ah eq Dimension(Ah);
    new_basis_UAh:=&cat[ [ UAh ! &cat[ (j eq i) select Eltseq(bb) else Eltseq(Ah!0) : j in [1..t] ] : bb in new_basis_Ah] : i in [1..t] ] ;
    mat:=Matrix(Coordinates([UAh.i : i in [1..Dimension(UAh)] ],new_basis_UAh));
    images:=[ UAhr ! Eltseq(r) : r in Rows(mat) ];
    VUAh,vUAh:=VectorSpace(UAh); //vUAh:UAhr->VUAh
    VUAhr,vUAhr:=VectorSpace(UAhr); //vUAhr:UAhr->VUAhr
    map:=hom< VUAh -> VUAhr | [ vUAhr(i) : i in  images] >;
    assert Dimension(Kernel(map)) eq 0 and Dimension(Image(map)) eq Dimension(UAhr);
    mUA:=(vUAh*map)*Inverse(vUAhr);
    // mUA:=hom< UAh->UAhr | images >; // fails to be recognized as an isom. go figure....
    // mUA is not an algebra hom, so it is not surprising that something goes wrong. but I don't unerstand why the image is smaller...
    return AVhr,mUA;
end intrinsic;
    
intrinsic BaseFieldExtension(I::IsogenyClassFq, Ie::IsogenyClassFq : prec:=3000 )->Map
{ given an isogeny class I over Fq and Ie which is the base field extension to F_q^r, the map from the UniverseAlgebra of the of I to the one of Ie.
The VarArg prec determines the precision to which the complex roots of the Weil polynomial are computed in order to extend it.}
    require WeilPolynomial(Ie) eq BaseFieldExtension(WeilPolynomial(I),Ilog(FiniteField(I),FiniteField(Ie)) : prec:=prec ) : "Ie is not a base field extension of I";
    UA:=UniverseAlgebra(I);
    UAe:=UniverseAlgebra(Ie);
    R,m:=ZFVOrder(I);
    Re,me:=ZFVOrder(Ie);
    A:=Algebra(R);
    Ae:=Algebra(Re);
    fac:=Factorization(WeilPolynomial(Ie));
    g:=&*[ f[1] : f in fac ] ;
    s:=fac[1,2];
    assert IsSquarefree(g);
    assert g eq DefiningPolynomial(Ae);
    assert Dimension(UAe) eq Dimension(UA);
    assert s eq (Dimension(UAe) div Dimension(Ae)); 
    t:=Dimension(UA) div Dimension(A);
    s0:=s div t;
    r:=Ilog(FiniteField(I),FiniteField(Ie));
    // the next two lines are not very pretty
    F:=PrimitiveElement(A);
    new_basis_A:=&cat[ [F^j*(F^r)^i : i in [0..Degree(g)-1] ] : j in [0..s0-1] ];
    assert #new_basis_A eq Dimension(A);
    new_basis_UA:=&cat[ [ UA ! &cat[ (j eq i) select Eltseq(bb) else Eltseq(A!0) : j in [1..t] ] : bb in new_basis_A] : i in [1..t] ] ;
    mat:=Matrix(Coordinates([UA.i : i in [1..Dimension(UA)] ],new_basis_UA));
    images:=[ UAe ! Eltseq(r) : r in Rows(mat) ];
    VUA,vUA:=VectorSpace(UA); //vUA:UA->VUA
    VUAe,vUAe:=VectorSpace(UAe); //vUAe:UAe->VUAe
    map:=hom< VUA -> VUAe | [ vUAe(i) : i in  images] >;
    assert Dimension(Kernel(map)) eq 0 and Dimension(Image(map)) eq Dimension(UAe);
    mUA:=(vUA*map)*Inverse(vUAe);
    return mUA;
end intrinsic;

// ------------------- //
// Extend AbelianVarietyFq
// ------------------- //

intrinsic BaseFieldExtension(A::AbelianVarietyFq, Ie::IsogenyClassFq, me::Map)->AbelianVarietyFq
{ Given an abelian variety A in the isogeny class I, the base field extension Ie of I, together with the map me from the UniverseAlgebra(I) to the UniverseAlgebra(Ie), it returns the base field extension Ae of A in Ie.  }
    assert WeilPolynomial(Ie) eq BaseFieldExtension(WeilPolynomial(A),Ilog(FiniteField(A),FiniteField(Ie))); //the given abelin variety does not extend to Ie
    require Domain(me) eq UniverseAlgebra(IsogenyClass(A)) and Codomain(me) eq UniverseAlgebra(Ie) : "the input does not correspond to a base field extension data"; 
        return AbelianVariety(Ie,[me(g) : g in DeligneModuleZBasis(A)]);
end intrinsic;

intrinsic BaseFieldExtension( seq::SeqEnum[AbelianVarietyFq], Ie::IsogenyClassFq )->SeqEnum[List]
{ Given a sequence of abelian varieties A whose isogeny cclasses extend to Ie, it returns a sequence of pairs [*Ae,me*] onsisting of the base field extension of the abelian varieties together with the maps on the UnvierseAlgebras }
    isog:={@ IsogenyClass(A) : A in seq @};
    isog_maps:=[ BaseFieldExtension(I,Ie) : I in isog ];
    seq_e:=[ ];
    for A in seq do
        me:=isog_maps[Index(isog,IsogenyClass(A))];
        Append(~seq_e,[*BaseFieldExtension(A,Ie,me),me*]);
    end for;
    return seq_e;
end intrinsic;

// ------------------- //
// Instrinsic: IsTwistOfOrder
// ------------------- //

intrinsic IsTwistOfOrder( A1::AbelianVarietyFq, A2::AbelianVarietyFq ,r :: RngIntElt )-> BoolElt,Map
{ given two abelian varieties A1 and A2 (possibly non isogenous) over Fq checks itf they are twist of order r, that is, if they become isomorphic after a base field extension to F_q^r  }
    Ie,me:=BaseFieldExtension(IsogenyClass(A1),r);
    Ie2,_:=BaseFieldExtension(IsogenyClass(A2),r);
    if WeilPolynomial(Ie) eq WeilPolynomial(Ie2) then
        seq_e:=BaseFieldExtension([A1,A2],Ie);
        return IsIsomorphic(seq_e[1,1],seq_e[2,1]);
    else 
        return false,_;
    end if;
end intrinsic;

/* TESTS

AttachSpec("packages.spec");
P<x>:=PolynomialRing(Integers());

// Example 1
h:=x^6 - x^3 + 8;
AVh:=IsogenyClass(h);
r:=6;
I6,m6:=BaseFieldExtension(AVh,r);

iso:=ComputeIsomorphismClasses(AVh);
#iso;
iso_6:=ComputeIsomorphismClasses(I6);
#iso_6;


for A in iso do 
    Ae:=BaseFieldExtension(A,I6,m6);
    R,mR:=ZFVOrder(Ae);
    Me:=BassModule(R,mR,DeligneModuleZBasis(Ae));
    exists{ B : B in iso_6 | IsIsomorphic(Ae,B) }; //I get an error in IsIsomorphic BassMod
end for;

for A in iso do
    for B in iso do
        IsTwistOfOrder(A,B,r);
    end for;
end for;

// Example 2
h:=x^6 + 4*x^3 + 27;
AVh:=IsogenyClass(h);
r:=3;
I3,m3:=BaseFieldExtension(AVh,r);

iso:=ComputeIsomorphismClasses(AVh);
#iso;
for A in iso do 
    Ae:=BaseFieldExtension(A,I3,m3);
end for;

// Example 3
AttachSpec("packages.spec");
_<x>:=PolynomialRing(Integers());
h1:=x^4 - 205*x^2 + 10609;
h2:=(x^2-x+103)*(x^2+x+103);
g3:=(x^2-x+103); h3:=g3^2;
g4:=(x^2+x+103); h4:=g4^2;
Ah1:=IsogenyClass(h1);
isoh1:=ComputeIsomorphismClasses(Ah1);
Ah2:=IsogenyClass(h2);
isoh2:=ComputeIsomorphismClasses(Ah2);
Ah3:=IsogenyClass(h3);
isoh3:=ComputeIsomorphismClasses(Ah3);
Ah4:=IsogenyClass(h4);
isoh4:=ComputeIsomorphismClasses(Ah4);

"isom classes: ", #isoh1, #isoh2, #isoh3, #isoh4;

assert 1 eq #{ WeilPolynomial(BaseFieldExtension(Ahi,4)) : Ahi in [Ah1,Ah2,Ah3,Ah4] };

for I in [Ah1,Ah2,Ah3,Ah4] do
    WeilPolynomial(BaseFieldExtension(I,2));
end for;
// the last 3 isogeny classes extend to the same isogeny class over F_103^2

Ah_2,_:=BaseFieldExtension(Ah2,2);
seq_2:=BaseFieldExtension(isoh2 cat isoh3 cat isoh4 , Ah_2);
Ah_4,_:=BaseFieldExtension(Ah2,4);
seq_4:=BaseFieldExtension(isoh2 cat isoh3 cat isoh4 , Ah_4);
seq_2_4:=BaseFieldExtension([s[1] : s in seq_2],Ah_4);
assert #seq_4 eq #seq_2_4;
assert forall{ i : i in [1..#seq_4] | seq_4[i,1] eq seq_2_4[i,1] };
// we test that the base extension of the base extension is equal to a single base extension

all_iso:=isoh1 cat isoh2 cat isoh4 cat isoh4 ;
for A in all_iso do
    for B in all_iso do
        if IsTwistOfOrder(A,B,2) then
            printf "1 ";
        else
            printf "0 ";
        end if;
    end for;
    printf "\n";
end for;

all_ext:=BaseFieldExtension(all_iso,Ah_4);
for A in all_ext do
    for B in all_ext do
        if IsIsomorphic(A[1],B[1]) then
            printf "1 ";
        else
            printf "0 ";
        end if;
    end for;
    printf "\n";
end for;



// Example 4 - continutation of the previous

AttachSpec("packages.spec");
_<x>:=PolynomialRing(Integers());
h1:=x^4 - 205*x^2 + 10609;
h2:=(x^2-x+103)*(x^2+x+103);
g3:=(x^2-x+103); h3:=g3^2;
g4:=(x^2+x+103); h4:=g4^2;
Ah1:=IsogenyClass(h1);
isoh1:=ComputeIsomorphismClasses(Ah1);
Ah2:=IsogenyClass(h2);
isoh2:=ComputeIsomorphismClasses(Ah2);
Ah3:=IsogenyClass(h3);
isoh3:=ComputeIsomorphismClasses(Ah3);
Ah4:=IsogenyClass(h4);
isoh4:=ComputeIsomorphismClasses(Ah4);
A:=isoh1[1];
UA:=UniverseAlgebra(A);
F:=FrobeniusEndomorphism(A);
U,u:=UnitGroup2(MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]));
TAut:=[ hom<UA->UA|[u(t)*b:b in Basis(UA)]> : t in TorsionSubgroup(U) ];
TF:=[ t*F : t in TAut ];
assert forall{ t : t in TAut | F*t eq t*F };
all_iso:=isoh1 cat isoh2 cat isoh4 cat isoh4 ;
Ah_4,_:=BaseFieldExtension(Ah1,4);
all_ext:=BaseFieldExtension(all_iso,Ah_4);
Ae:=all_ext[1,1];
mAe:=all_ext[1,2];
TF_mAe:=[ tf*mAe : tf in TF];


the next lines are wrong I should use the Frobenius over Fq not the one over Fq^r!!!!!
for B in all_ext do
    test,iso:=IsIsomorphic(Ae,B[1]);
    if test then
        FB:=FrobeniusEndomorphism(B[1]);
        mB:=iso*FB*Inverse(iso);
        exists{ a : a in TF_mAe | a eq mB };
    end if;
end for;



// Example 4.2 - continutation of the previous. second version of the test

AttachSpec("packages.spec");
P<x>:=PolynomialRing(Integers());
h:=x^4 - 205*x^2 + 10609;
Ah:=IsogenyClass(h);
Ah_4,_:=BaseFieldExtension(Ah,4);
h_4:=WeilPolynomial(Ah_4);
hs:=[];
rr:=Roots(h_4,ComplexField());
ccsq:=[ Roots(x^4-r[1]) : i in [1..r[2]] ,  r in rr];
ccsq:=CartesianProduct(ccsq);
for c in ccsq do 
    coCC:=Coefficients(&*[ x-cc[1] : cc in c ]); 
    coZZ:=[ Round(Re(c)) : c in coCC ];
    if forall{ i : i in [1..#coCC] | Abs(coCC[i] - coZZ[i]) lt 10^(-15) } then
        ht:=P!coZZ;
        Append(~hs,ht);
    end if;
end for;

hs:=[h] cat Exclude(Setseq(Seqset(hs)),h); hs;
assert hs[1] eq h;

all_iso:=&cat[ ComputeIsomorphismClasses(IsogenyClass(ht)) : ht in hs ];
all_ext:=BaseFieldExtension(all_iso,Ah_4);
#all_iso,#all_ext;

for i in [1..#ComputeIsomorphismClasses(Ah)] do
    A:=all_iso[i];
    UA:=UniverseAlgebra(A);
    RA,mRA:=ZFVOrder(A);
    FA_elt:=mRA(PrimitiveElement(Algebra(RA)));
    FA:=FrobeniusEndomorphism(A);
    U,u:=UnitGroup2(MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]));
    Tors:=[ t : t in TorsionSubgroup(U)];
    TAut:=[ hom<UA->UA|[u(t)*b:b in Basis(UA)]> : t in Tors ];
    Ae:=all_ext[i,1];
    mAe:=all_ext[i,2];
    UAe:=UniverseAlgebra(Ae);
    TF_mAe:=[ Inverse(mAe)*t*FA*mAe : t in TAut ];
    TF_mAe_mats:=[Matrix([t(b) :b in Basis(UAe)]) : t in TF_mAe];
    for j in [1..#all_ext] do
        B:=all_iso[j];
        Be:=all_ext[j,1];
        mBe:=all_ext[j,2];
        test,iso:=IsIsomorphic(Ae,Be);
        if test then
            RB,mRB:=ZFVOrder(B);
            FB_elt:=mRB(PrimitiveElement(Algebra(RB)));
            FB:=FrobeniusEndomorphism(B);
            map:=iso*Inverse(mBe)*FB*mBe*Inverse(iso);
            map_mat:=Matrix([map(b) : b in Basis(UAe)]);
            if exists(a){ a : a in [1..#TF_mAe_mats] | TF_mAe_mats[a] eq map_mat } then 
                aut:=u(Tors[a]);
                phi:=HomsToC(Parent(aut))[1];
                if aut eq 1 then printf "1 ";
                elif aut eq -1 then printf "-1 ";
                elif aut^2 eq -1 and Im(phi(aut)) gt 0 then printf "i ";
                elif aut^2 eq -1 and Im(phi(aut)) lt 0 then printf "-i ";
                end if;
            else printf "0 ";
            end if;
        else
            printf "_ ";
        end if;
    end for;
    printf "\n";
end for;

// Example 5 - this is absolutely simple

AttachSpec("packages.spec");
P<x>:=PolynomialRing(Integers());
h:=x^6 - 4*x^5 + 12*x^4 - 36*x^3 + 60*x^2 - 100*x + 125;
Ah:=IsogenyClass(h);
Ah_4,_:=BaseFieldExtension(Ah,4);
h_4:=WeilPolynomial(Ah_4);
hs:=[];
rr:=Roots(h_4,ComplexField());
ccsq:=[ Roots(x^4-r[1]) : i in [1..r[2]] ,  r in rr];
ccsq:=CartesianProduct(ccsq);
for c in ccsq do 
    coCC:=Coefficients(&*[ x-cc[1] : cc in c ]); 
    coZZ:=[ Round(Re(c)) : c in coCC ];
    if forall{ i : i in [1..#coCC] | Abs(coCC[i] - coZZ[i]) lt 10^(-15) } then
        ht:=P!coZZ;
        Append(~hs,ht);
    end if;
end for;

hs;

all_iso:=&cat[ ComputeIsomorphismClasses(IsogenyClass(ht)) : ht in hs ];
all_ext:=BaseFieldExtension(all_iso,Ah_4);
#all_iso,#all_ext;


for i in [1..#all_ext] do
    A:=all_iso[i];
    UA:=UniverseAlgebra(A);
    RA,mRA:=ZFVOrder(A);
    FA_elt:=mRA(PrimitiveElement(Algebra(RA)));
    FA:=FrobeniusEndomorphism(A);
    U,u:=UnitGroup2(MultiplicatorRing(DeligneModuleAsDirectSum(A)[1,1]));
    Tors:=[ t : t in TorsionSubgroup(U)];
    TAut:=[ hom<UA->UA|[u(t)*b:b in Basis(UA)]> : t in Tors ];
    Ae:=all_ext[i,1];
    mAe:=all_ext[i,2];
    UAe:=UniverseAlgebra(Ae);
    TF_mAe:=[ Inverse(mAe)*t*FA*mAe : t in TAut ];
    TF_mAe_mats:=[Matrix([t(b) :b in Basis(UAe)]) : t in TF_mAe];
    for j in [1..#all_ext] do
        B:=all_iso[j];
        Be:=all_ext[j,1];
        mBe:=all_ext[j,2];
        test,iso:=IsIsomorphic(Ae,Be);
        if test then
            RB,mRB:=ZFVOrder(B);
            FB_elt:=mRB(PrimitiveElement(Algebra(RB)));
            FB:=FrobeniusEndomorphism(B);
            map:=iso*Inverse(mBe)*FB*mBe*Inverse(iso);
            map_mat:=Matrix([map(b) : b in Basis(UAe)]);
            if exists(a){ a : a in [1..#TF_mAe_mats] | TF_mAe_mats[a] eq map_mat } then 
                aut:=u(Tors[a]);
                phi:=HomsToC(Parent(aut))[1];
                if aut eq 1 then printf "1 ";
                    elif aut eq -1 then printf "-1 ";
                    elif aut^2 eq -1 and Im(phi(aut)) gt 0 then printf "i ";
                    elif aut^2 eq -1 and Im(phi(aut)) lt 0 then printf "-i ";
                end if;
            else printf "0 ";
            end if;
        else
            printf "_ ";
        end if;
    end for;
    printf "\n";
end for;

*/
