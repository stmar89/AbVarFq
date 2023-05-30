/*
To compute:
* av_fq_pol: label, isog_label, endomorphism_ring, isom_label, degree, kernel, aut_group, geom_aut_group (can say that it is equal to aut_group when End^0(Fqbar) is commutative; can check this from av_fq_endalg_data->divalg_dim for each factor in av_fq_endalg_factors), is_jacobian (say false if a product at all, none otherwise)
* av_fq_weak_equivalences: label (for matching), pic_invs, pic_basis, is_product, product_partition, is_conjugate_stable, generator_over_ZFV, is_Zconductor_sum
* av_fq_isog: pic_prime_gens

*/
SetColumns(0);
//SetDebugOnError(true);
issue_file := Sprintf("%oavdata/issues", fld);
av_fq_pol_output := Sprintf("%oavdata/av_fq_pol_output/%o", fld, label);
av_fq_pol_columns := ["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "aut_group", "geom_aut_group", "is_jacobian", "representative"];
av_fq_we_output := Sprintf("%oavdata/av_fq_we_output/%o", fld, label);
av_fq_we_columns := ["label", "pic_invs", "pic_basis", "is_product", "product_partition", "is_conjugate_stable", "generator_over_ZFV", "is_Zconductor_sum", "is_ZFVconductor_sum"];
av_fq_isog_output := Sprintf("%oavdata/av_fq_isog_output/%o", fld, label);
av_fq_isog_columns := ["pic_prime_gens"];
allproduct_output := Sprintf("%oavdata/allproduct_output/%o", fld, label);
cmfile := Sprintf("%opAdicPos/output_parallel1/%o_pAdicPos.txt", fld, label);
AttachSpec(fld * "AlgEt/spec");
AttachSpec(fld * "AbVarFq/LMFDB/spec");
SetClassGroupBounds("GRH");
function print_ivec(v : json:=false)
    base := json select "[%o]" else "{%o}";
    if Type(v) eq SeqEnum or Type(v) eq Tup then
        return Sprintf(base, Join([$$(c : json:=json) : c in v], ","));
    end if;
    return Sprint(v);
end function;
try
    allproduct := true;
    g, q, poly := Explode(Split(label, "."));
    commlines := Split(Read(Sprintf("%oavdata/commutative_geom_endalg/%o.%o", fld, g, q)), "\n");
    geom_endalg_is_comm := 0;
    for line in commlines do
        llabel, iscomm := Explode(Split(line, " "));
        if label eq llabel then
            geom_endalg_is_comm := (iscomm[1] eq "t");
            break;
        end if;
    end for;
    assert geom_endalg_is_comm cmpne 0;
    ZFV := LoadSchemaWKClasses(Read(Sprintf("%oavdata/wk_classes/%o_schema.txt", fld, label)));
    A := Algebra(ZFV);
    if OpenTest(cmfile, "r") then
        cmdata := Split(Read(cmfile), ":")[2];
        print label, cmdata;
        PHI := LoadpAdicPosCMType(ZFVBasis(A), cmdata);
        assert assigned A`pAdicPosCMType;
        print "CM type loaded";
    end if;
    av_fq_pol := [];
    av_fq_we := [];
    av_fq_isog := AssociativeArray();
    _, cangens := CanonicalPicGenerators(ZFV);
    _ := CanonicalPicBases(ZFV); // sets CanonicalPicBasis for each S
    av_fq_isog["pic_prime_gens"] := print_ivec(cangens);
    for S in OverOrders(ZFV) do
        Pbasis, construction := CanonicalPicBasis(S);
        invs, construction := Explode(construction);
        Sdata := AssociativeArray();
        Sdata["label"] := WELabel(S);
        Sdata["pic_invs"] := print_ivec(invs);
        Sdata["pic_basis"] := print_ivec(construction);
        product, _, partition := IsProduct(S);
        allproduct := allproduct and product;
        Sdata["is_product"] := product select "t" else "f";
        Sdata["product_partition"] := print_ivec(partition: json:=true);
        Sdata["is_conjugate_stable"] := IsConjugateStable(S) select "t" else "f";
        _, dens, nums := SmallestMonogenicGeneratorOverZFV(S, ZFV);
        if #dens eq 0 then
            Sdata["generator_over_ZFV"] := "\\N";
        else
            Sdata["generator_over_ZFV"] := Sprintf("[%o,%o]", dens[1], print_ivec(nums[1] : json:=true));
        end if;
        Sdata["is_Zconductor_sum"] := (S eq Order(ZBasis(Conductor(S)))) select "t" else "f";
        Sdata["is_ZFVconductor_sum"] := (S eq Order(ZBasis(Conductor(S)) cat ZBasis(ZFV))) select "t" else "f";
        Append(~av_fq_we, Sdata);
    end for;
    h := ChangeRing(DefiningPolynomial(Algebra(ZFV)), Integers());
    _,p:=IsPrimePower(ConstantCoefficient(h));
    if IsCoprime(Coefficients(h)[(Degree(h) div 2)+1], p) then
        for ppol in PPolIteration(ZFV) do
            poldata := AssociativeArray();
            we, pic_ctr, I, den, nums := Explode(ppol);
            S := MultiplicatorRing(I);
            pieces := Split(we, ".");
            poldata["label"] := Sprintf("%o.%o.%o", label, we, pic_ctr);
            poldata["isog_label"] := label;
            poldata["endomorphism_ring"] := Join(pieces[1..2], ".");
            poldata["isom_label"] := Sprintf("%o.%o", pieces[3], pic_ctr);
            poldata["degree"] := "1";
            poldata["kernel"] := "{}";
            aut_grp := IdentifyGroup(TorsionSubgroup(UnitGroup(S)));
            aut_grp := Sprintf("%o.%o", aut_grp[1], aut_grp[2]);
            poldata["aut_group"] := aut_grp;
            if geom_endalg_is_comm then
                poldata["geom_aut_group"] := aut_grp;
            else
                poldata["geom_aut_group"] := "\\N";
            end if;
            poldata["is_jacobian"] := IsProduct(S) select "f" else "\\N";
            poldata["representative"] := Sprintf("[%o,%o]", den, print_ivec(nums: json:=true));
            Append(~av_fq_pol, poldata);
        end for;
    end if;
    for pol_line in av_fq_pol do
        fprintf av_fq_pol_output, "%o\n", Join([pol_line[col] : col in av_fq_pol_columns], ":");
    end for;
    for we_line in av_fq_we do
        fprintf av_fq_we_output, "%o\n", Join([we_line[col] : col in av_fq_we_columns], ":");
    end for;
    fprintf av_fq_isog_output, "%o\n", Join([av_fq_isog[col] : col in av_fq_isog_columns], ":");
    if allproduct then
        fprintf allproduct_output, "%o\n", #av_fq_pol;
    end if;
catch e;
    fprintf issue_file, "*********************************************\n%o\n", label;
    fprintf issue_file, "%o\n", e;
end try;
quit;
