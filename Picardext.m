freeze;

/////////////////////////////////////////////////////
// Picard Group of orders in etale algebras over \Q
// Stefano Marseglia, Utrecht University, s.marseglia@uu.nl
// http://www.staff.science.uu.nl/~marse004/
/////////////////////////////////////////////////////

declare attributes AlgAssVOrd:PicardGroup;
declare attributes AlgAssVOrd:UnitGroup;

intrinsic ResidueRingUnits(S::AlgAssVOrd,I::AlgAssVOrdIdl) -> GrpAb,Map
{returns the group (S/I)^* and a map (S/I)^* -> S. It is required S to be maximal }
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    //the following code works only for maximal orders in etale algebras
    require IsMaximal(S): "implemented only for the maximal order";
    test,I_asProd:=IsProductOfIdeals(I);
    assert test;
    A:=Algebra(S);
    n:=#I_asProd;
    ray_res_rings:=[];
    ray_res_rings_maps:=[**];
    for i in [1..n] do
        IL:=I_asProd[i];
        OL:=Order(IL);
        assert IsMaximal(OL);
        R,r:=RayResidueRing(IL);
        Append(~ray_res_rings,R);
        Append(~ray_res_rings_maps,r);
    end for;
    D,mRD,mDR:=DirectSum(ray_res_rings);
    map_ResRing_S:=function(x)
        return &+[A`NumberFields[i,2](ray_res_rings_maps[i](mDR[i](x))) : i in [1..n]];
    end function;
    map_S_ResRing:=function(y)
        comp:=Components(y);
        assert #ray_res_rings_maps eq #comp;
        return &+[mRD[i](comp[i]@@ray_res_rings_maps[i]) : i in [1..n]];
    end function;
    map:=map<D -> A | x:->map_ResRing_S(x) , y:->map_S_ResRing(y) >;
    assert2 forall{ gen: gen in Generators(D) | (map(gen))@@map eq gen };
    return D,map;
end intrinsic;

residue_class_field_primitive_element := function(P)
//given a maximal ideal P in S, returns a generator of (S/P)* as an element of S;
    S:=Order(P);
    Q,m:=ResidueRing(S,P);
    ord:=#Q-1; //ord = #(S/P)-1;
    assert IsPrimePower(#Q); // #(S/P) must be a prime power
    proper_divisors_ord:=Exclude(Divisors(ord),ord);
    repeat
        repeat 
            a:=Random(Q);
        until a ne Zero(Q);
    until forall{f : f in proper_divisors_ord | m((a@@m)^f) ne m(One(Algebra(S)))};
    assert2 (m((a@@m)^ord) eq m(One(Algebra(S)))); 
    return a@@m;
end function;

residue_class_ring_unit_subgroup_generators:=function(S, F)
// determine generators of the subgroup of (S/F)^* as elements of A=Algebra(S)
	A:=Algebra(S);
	O:=MaximalOrder(A);
	Fm:=ideal<O| ZBasis(F)>;
	l:=Factorization(Fm);
	l2:=[<ideal<S|ZBasis(x[1])> meet S,x[2]>: x in l]; 
	primes:={x[1]:x in l2};
	primes:=[<x, Maximum([y[2]: y in l2 |y[1] eq x])>:x in primes];
	elts:={};
	for a in primes do
		a1a2:=a[1]^a[2];
		idp:=a[1];
		rest:=OneIdeal(S);
		for b in primes do
			if b[1] ne idp then
				rest:=rest*(b[1]^b[2]);
			end if;
		end for;
		//Compute primitive elt for residue field
		c:=residue_class_field_primitive_element(idp);
		c:=ChineseRemainderTheorem(a1a2,rest,c,One(A));
		Include(~elts,c);
		b:=1;
		while b lt a[2] do
			M:=ZBasis(idp);
			M:=[1+x:x in M];
			for elt in M do
				c:=ChineseRemainderTheorem((a1a2),rest,elt,One(A));
				Include(~elts,c);
			end for;
			b:=b*2;
			idp:=idp^2;
		end while;
	end for;
	assert2 forall{x : x in elts | x in S and not x in F};
	return elts;
end function;

IsPrincipal_prod_internal:=function( I , GRH )
//returns if the argument is a principal ideal; if so the function returns also the generator. It works only for products of ideals
    assert IsMaximal(Order(I)); //this function should be called only for ideals of the maximal order
    test,I_asProd:=IsProductOfIdeals(I);
    assert test; //this function should be called only for ideals of the maximal order, hence I is a product
    S:=Order(I);
    A:=Algebra(S);
    gen:=Zero(A);
    if GRH then
        SetClassGroupBounds("GRH");
    end if;
    for i in [1..#I_asProd] do
        IL:=I_asProd[i];
        L:=A`NumberFields[i];
         //The next call is to prevent a bug of the in-built function IsPrincipal (which might have been corrected by now...).
         //Also if one wants to use the GRH bound rather than one needs to precompute the class groups, since IsPrincipal does not accepts varargs )       
        OL,oL:=ClassGroup(Order(IL));
        testL,genL:=IsPrincipal(IL);
        assert2 (Zero(OL) eq (IL@@oL)) eq testL;
        if not testL then
            return false,_;
        end if;
        gen:=gen+L[2](L[1] ! genL);
    end for;
    assert2 ideal<S|gen> eq I;
    return true,gen;
end function;


intrinsic IsPrincipal(I1::AlgAssVOrdIdl : GRH:=false )->BoolElt, AlgAssElt
{   
    Return if the argument is a principal ideal; if so the function returns also the generator.
    The optional argument "GRH" decides wheter the bound for the IsPrincipal test should be conditional. The default value is "false".
}
//wouldn't an LLL test be faster?
    require IsFiniteEtale(Algebra(I1)): "the algebra of definition must be finite and etale over Q";
    if not IsInvertible(I1) then return false,_; end if;
    S:=Order(I1);
    if IsMaximal(S) then
        return IsPrincipal_prod_internal(I1,GRH);
    end if;
    A:=Algebra(S);
    O:=MaximalOrder(A);
    F:=Conductor(S);
    FO:=ideal<O|ZBasis(F)>;
    cop:=CoprimeRepresentative(I1,F);
    I:=cop*I1;
    IO:=ideal<O|ZBasis(I)>; 
    is_princ_IO,gen_IO:=IsPrincipal_prod_internal(IO,GRH);
    if not is_princ_IO then
        return false,_;
    end if;
    R,r:=ResidueRingUnits(O,FO);
    if Order(R) eq 1 then
        assert2 ideal<S|gen_IO> eq I;
        return true, gen_IO*cop^-1;
    end if;
    UO,uO:=UnitGroup2(O : GRH:=GRH );
    Sgens:=residue_class_ring_unit_subgroup_generators(S,F);
    B,b:=quo<R|[gen@@r : gen in Sgens]>;
    gens_UO_inB:=[ b(uO(UO.i)@@r) : i in [1..#Generators(UO)]  ];
    h:=hom<UO -> B | gens_UO_inB >;
    hUO:=Image(h);
    if not b(gen_IO@@r) in hUO then
        return false,_;
    end if;
    //now we know that I is principal. let's find a generator
    UQ,qQ:=quo<UO|Kernel(h)>;  //UQ = O*/S*
    alpha:=hom<UQ -> B | [UQ.i@@qQ @uO @@r @b : i in [1..#Generators(UQ)]]>;
    is_princ,elt:=HasPreimage(gen_IO@@r@b,alpha);
    if is_princ then
        gen_I:=gen_IO*(elt@@qQ@uO)^-1;
        gen_I1:=gen_I*cop^-1;
        assert2 ideal<S|gen_I1> eq I1;
        return true,gen_I1;
    else
        return false, _;
    end if;  
end intrinsic;

PicardGroup_prod_internal:=function( O , GRH )
//computes the PicardGroup of a product of order in a product of number fields and returns the group (as a direct product) and a sequence of representatives
    if assigned O`PicardGroup then return O`PicardGroup[1],O`PicardGroup[2]; end if;
    A:=Algebra(O);
    assert IsMaximal(O); // this function should be used only for maximal orders
    test,O_asProd:=IsProductOfOrders(O);
    assert test; //O must be a product of orders
    assert #A`NumberFields eq #O_asProd;
    groups_maps_fields_maps:=[**];
    if GRH then
        SetClassGroupBounds("GRH");
    end if;
    for i in [1..#O_asProd] do
        L:=A`NumberFields[i];
        OL:=O_asProd[i];
        GL,gL:=ClassGroup(OL);
        assert2 forall{y : y in [gL(z) : z in GL] | MultiplicatorRing(y) eq OL};
        //this is a detector for bugs for the PicardGroup function.
        Append(~groups_maps_fields_maps,<GL,gL,L[1],L[2]>);
    end for;
    assert #groups_maps_fields_maps eq #A`NumberFields;
    G,g,Gproj:=DirectSum([T[1] : T in groups_maps_fields_maps]);

    if #G eq 1 then
        from_G_to_ideals:=function(x)
            return OneIdeal(O);
        end function;
        from_ideals_to_G:=function(y)
            assert Order(y) eq O;
            return Zero(G);
        end function;
        codomain:=Parent(OneIdeal(O));
        return G,map<G -> codomain | x:-> from_G_to_ideals(x) , y:->from_ideals_to_G(y) >;
    else
        zerosinO:=[ ideal<O|[ T[4](y) : y in Basis(T[2](Zero(T[1])),T[3])]> : T in groups_maps_fields_maps];
        assert2 &+zerosinO eq OneIdeal(O);
        geninO:=[]; //this will contain the the ideals of O corresponding to the generators of G
        for i in [1..#Generators(G)] do
            gen:=G.i;
            gens_inA:=[];
            for i in [1..#groups_maps_fields_maps] do
                T:=groups_maps_fields_maps[i];
                gLi:=T[2];
                idLi:=gLi(Gproj[i](gen));
                gens_inA:=gens_inA cat[T[4](g) : g in Basis(idLi,T[3])];
            end for;
            gen_O:=ideal<O|gens_inA>;
            Append(~geninO,gen_O);
        end for;
        assert #geninO eq #Generators(G);      
        rep_idinA:= function(x)
            coeff:=Eltseq(x);
            id:=&*[geninO[i]^coeff[i] : i in [1..#coeff]];
            return id;
        end function;
        inverse_map:=function(id)
            if not IsIntegral(id) then
                id:=MakeIntegral(id);
            end if;
            test,id_asprod:=IsProductOfIdeals(id);
            assert test;
            return &+[g[i](id_asprod[i]@@groups_maps_fields_maps[i,2]) : i in [1..#id_asprod]];
        end function;
        Codomain:=Parent(rep_idinA(Zero(G)));
        mapGtoO:=map<G -> Codomain | rep:-> rep_idinA(rep) , y:->inverse_map(y) >; 
        assert2 forall{a : a in Generators(G)| (mapGtoO(a))@@mapGtoO eq a};
        O`PicardGroup:=<G,mapGtoO>;
        return G,mapGtoO;
    end if;
end function;

intrinsic PicardGroup( S::AlgAssVOrd : GRH:=false ) -> GrpAb, Map
{
    Return the PicardGroup of the order S, which is not required to be maximal, and a map from the PicardGroup to a set of representatives of the ideal classes
    The optional argument "GRH" decides the bound for the computations of the ClassGroup and UnitGroup of the maximal order. The default value is "false".
}
    if assigned S`PicardGroup then return S`PicardGroup[1],S`PicardGroup[2]; end if;
    if IsMaximal(S) then return PicardGroup_prod_internal(S,GRH); end if;
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    A:=Algebra(S);
    O:=MaximalOrder(A);
    GO,gO:=PicardGroup_prod_internal(O,GRH); //C, mC
    F:=Conductor(S);
    FO:=ideal<O|ZBasis(F)>; //Fm
    gens_GO_in_S:=[]; //coprime with FO, in S and then meet S   
    gens_GO_in_O:=[]; //coprime with FO, in O, Cgen
    if #GO gt 1 then
        for i in [1..#Generators(GO)] do
            I:=gO(GO.i);
            //c:=CoprimeRepresentative(I,FO);
            c:=CoprimeRepresentative(I,MinimalInteger(FO)*O);
            cI:=c*I;
            cISmeetS:=ideal<S|ZBasis(cI)> meet S;
            Append(~gens_GO_in_S,cISmeetS);
            Append(~gens_GO_in_O,cI);//used in building relDglue
        end for;

        mGO_to_S:=function(rep)  
            coeff:=Eltseq(rep);
            idS:=&*[(gens_GO_in_S[i])^coeff[i] : i in [1..#coeff] ];
            return idS;
        end function;
        mGO_to_O:=function(rep)  
            coeff:=Eltseq(rep);
            assert #coeff eq #gens_GO_in_O;
            idO:=&*[(gens_GO_in_O[i])^coeff[i] : i in [1..#coeff] ];
            return idO;
        end function;
    else
        GO:=FreeAbelianGroup(0);
        mGO_to_S:=function(rep)
            idS:=OneIdeal(S);
            return idS;
        end function;
        mGO_to_O:=function(rep)
            idO:=OneIdeal(O);
            return idO;
        end function;
    end if;

    R,r:=ResidueRingUnits(O,FO); // G, mG
    Sgens:=residue_class_ring_unit_subgroup_generators(S,F); // ogens //generators in S of (S/F)*
    UO,uO:=UnitGroup2(O : GRH:=GRH ); // Um, mUm 
    H:=FreeAbelianGroup(#Generators(GO));
    D, mRD, mHD, mDR, mDH := DirectSum(R,H); // D, mGD, mHD, mDG, mDH
    relDresidue:=[mRD(x@@r) : x in Sgens];
    relDunits:=[mRD(uO(x)@@r)  : x in Generators(UO)];
    // glue R and GO
    relDglue := [];   
    assert #gens_GO_in_S eq #InvariantFactors(GO);
    for i in [1..#gens_GO_in_S] do
        is_princ, gen := IsPrincipal_prod_internal(gens_GO_in_O[i]^InvariantFactors(GO)[i],GRH);
        assert is_princ;
        Append(~relDglue,-mRD(gen@@r)+mHD(H.i*InvariantFactors(GO)[i]));
    end for;

    P, mDP := quo<D|relDresidue cat relDunits cat relDglue>;
    gens_P_in_D:=[P.i@@mDP : i in [1..#Generators(P)]];
    if #P gt 1 then
        generators_ideals:=[];
        for gen in gens_P_in_D do
            id1:=ideal<S|ZBasis(ideal<O|r(mDR(gen))>)> meet S;
            id2:=mGO_to_S(mDH(gen));
            gen_inS:=id1*id2;
            Append(~generators_ideals,gen_inS);
        end for;
    else
        return P,map<P->Parent(OneIdeal(S)) | rep:->OneIdeal(S),
                                         id:->Zero(P)>;
    end if;

    representative_picard_group := function(rep)
        repseq := Eltseq(rep);
        return &*[generators_ideals[i]^repseq[i]:i in [1..#generators_ideals]];
    end function;


    disc_log_picard_group:=function(id)
    // (crep*id)^-1 is coprime with F
        crep:=1/(CoprimeRepresentative(id^-1,F));
        idO:=O!(crep*id); //idO is coprime with FO
        GOrep:=idO@@gO;
        J:=mGO_to_O((H!Eltseq(GOrep))); //no minus signs, so J is coprime with FO
        assert2 IsCoprime(J,FO);
        prod:=(idO^-1)*J; //prod is corpime with FO...
        isprinc,elt:=IsPrincipal_prod_internal(prod,GRH);
        assert2 IsCoprime(elt*O,FO); //..hence elt is in the image r:R->Pic(S)
        Rrep:=elt@@r;
        rep_P:=mDP(-mRD(Rrep)+mHD(H!Eltseq(GOrep)));//[I]=-[xO meet S]+GOrep
        return rep_P;        
    end function;

    cod:=Parent(representative_picard_group(Zero(P)));
    p:=map<P -> cod | rep:->representative_picard_group(rep),
                       id:->disc_log_picard_group(id) >;
    S`PicardGroup:=<P,p>;
    return P,p;
end intrinsic;

UnitGroup2_prod_internal:=function(O, GRH)
	//returns the UnitGroup of a order which is a produc of orders
	if assigned O`UnitGroup then return O`UnitGroup[1],O`UnitGroup[2]; end if;
	assert IsMaximal(O); //this function should be used only for maximal orders
	test,O_asProd:=IsProductOfOrders(O);
	assert test; //the order must be a product
	A:=Algebra(O);
	idemA:=OrthogonalIdempotents(A);
	U_asProd:=[];
	u_asProd:=[**];
	for OL in O_asProd do
		U,u:=UnitGroup(OL : GRH:=GRH );
		Append(~U_asProd,U);
		Append(~u_asProd,u);
	end for;
	Udp,udp,proj_Udp:=DirectSum(U_asProd);
	gensinA:=[&+[A`NumberFields[j,2](u_asProd[j](proj_Udp[j](Udp.i))) : j in [1..#U_asProd]] : i in [1..#Generators(Udp)] ];
  
    rep_inA:=function(rep)
        coeff:=Eltseq(rep);
        return &*[gensinA[i]^coeff[i] : i in [1..#coeff]];
    end function;

    disc_log:=function(x)
        comp_x:=Components(A ! x);
        x_in_Udp:=&*[ udp[i](comp_x[i]@@u_asProd[i]) : i in [1..#comp_x] ];
        return x_in_Udp;
    end function;

    maptoA:=map<Udp -> O | rep :-> rep_inA(rep) , y :-> disc_log(y) >;
    O`UnitGroup:=<Udp,maptoA>;
    return Udp,maptoA;
end function;

intrinsic UnitGroup2(S::AlgAssVOrd : GRH:=false ) -> GrpAb, Map
{   
    Return the unit group of a order in a etale algebra
    The optional argument "GRH" decides the bound for the computation of the unit group of the maximal order. The default value is "false".
}
    if assigned S`UnitGroup then return S`UnitGroup[1],S`UnitGroup[2]; end if;
    if IsMaximal(S) then return UnitGroup2_prod_internal(S,GRH); end if;
    require IsFiniteEtale(Algebra(S)): "the algebra of definition must be finite and etale over Q";
    A:=Algebra(S);
    require assigned A`NumberFields: "the order must lie in a product of number fields";
    O:=MaximalOrder(Algebra(S));
    UO,uO:=UnitGroup2_prod_internal(O, GRH);
    F:=Conductor(S);
    FO:=ideal<O|ZBasis(F)>;

    //Let's build B=(O/FO)^*/(S/F)^*
    R,r:=ResidueRingUnits(O,FO);
    gens_SF:=residue_class_ring_unit_subgroup_generators(S,F);
    B,b:=quo<R| [ a@@r : a in gens_SF ]>;

    img_gensUO_in_B:=[ b(uO(UO.i)@@r) : i in [1..#Generators(UO)] ];
    m:=hom<UO -> B | img_gensUO_in_B >;
    P:=Kernel(m);
    gens_P_in_A:=[uO(UO ! P.i) : i in [1..#Generators(P)] ];
    p_codomain:=Parent(gens_P_in_A[1]);

    map_P_to_S:=function(rep)
        coeff:=Eltseq(rep);
        assert #coeff eq #gens_P_in_A;
        elt:=&*[gens_P_in_A[i]^coeff[i] : i in [1..#coeff]];
        return elt;
    end function;

    map_S_to_P:=function(y)
        elt := P ! (y@@uO);
        return elt;
    end function;
    p:=map<P -> p_codomain | x:->map_P_to_S(x), y:->map_S_to_P(y)  >;
    S`UnitGroup:=<P,p>;
    return P,p;
end intrinsic;


intrinsic IsIsomorphic2(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl : GRH:=false ) -> BoolElt, AlgAssElt
{
    Checks if I=x*J, for some x. If so, also x is returned
    The optional argument "GRH" decides wheter the bound for the IsPrincipal test should be conditional. The default value is "false"
}
    require IsFiniteEtale(Algebra(I)): "the algebra of definition must be finite and etale over Q";
    test:=IsWeakEquivalent(I,J); //if so I=(I:J)*J and (I:J) is invertible in its MultiplicatorRing
    if test then
        S:=MultiplicatorRing(I);
        IS:=S!I;
        JS:=S!J;
        CIJ:=ColonIdeal(IS,JS);
        test2,x:= IsPrincipal(CIJ : GRH:=GRH );
        if test2 then
            return test2,x;
        assert2 I eq x*J;
        else
            return false, _ ;
        end if;
    else
        return false , _ ;
    end if;
end intrinsic;
