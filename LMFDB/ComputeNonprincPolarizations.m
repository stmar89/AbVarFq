

SetColumns(0);
if assigned degree_bounds then
    degree_bounds := [StringToInteger(d) : d in Split(degree_bounds, ",")];
else
    degree_bounds := [4,9,25];
end if;
//SetDebugOnError(true);
issue_file := Sprintf("%onpoldata/issues", fld);
av_fq_pol_output := Sprintf("%oavdata/av_fq_pol_output/%o", fld, label);
av_fq_pol_columns := ["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "degree_rr", "kernel_rr", "degree_rl", "kernel_rl", "degree_lr", "kernel_lr", "degree_ll", "kernel_ll", "aut_group", "geom_aut_group", "is_jacobian", "representative"];
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
        PHI := LoadpAdicPosCMType(ZFVBasis(A), cmdata);
        assert assigned A`pAdicPosCMType;
    end if;
    av_fq_pol := [];
    h := ChangeRing(DefiningPolynomial(A), Integers());
    _,p:=IsPrimePower(ConstantCoefficient(h));
    if IsCoprime(Coefficients(h)[(Degree(h) div 2)+1], p) then
        for I->Ipols in AllPolarizations(ZFV, PHI, degree_bounds) do
            S := MultiplicatorRing(I);
            aut_grp := IdentifyGroup(TorsionSubgroup(UnitGroup(S)));
            aut_grp := Sprintf("%o.%o", aut_grp[1], aut_grp[2]);
            for d->Idpols in Ipols do
                for data in Idpols do
                    den, nums, kerinfo := Explode(data);
                    poldata := AssociativeArray();

                    //we, pic_ctr, I, den, nums := Explode(nppol);
                    pieces := Split(I`IsomLabel, ".");
                    poldata["label"] := Sprintf("%o.%o", label, I`IsomLabel);
                    poldata["isog_label"] := label;
                    poldata["endomorphism_ring"] := Join(pieces[1..2], ".");
                    poldata["isom_label"] := I`IsomLabel;
                    poldata["degree"] := Sprint(d);
                    FillKernelInfo(~poldata, kerinfo);
                    poldata["aut_group"] := aut_grp;
                    if geom_endalg_is_comm then
                        poldata["geom_aut_group"] := aut_grp;
                    else
                        poldata["geom_aut_group"] := "\\N";
                    end if;
                    poldata["is_jacobian"] := "f";
                    poldata["representative"] := Sprintf("[%o,%o]", den, print_ivec(nums: json:=true));
                    Append(~av_fq_pol, poldata);
                end for;
            end for;
        end for;
    end if;
    for pol_line in av_fq_pol do
        fprintf av_fq_pol_output, "%o\n", Join([pol_line[col] : col in av_fq_pol_columns], ":");
    end for;
catch e;
    fprintf issue_file, "*********************************************\n%o\n", label;
    fprintf issue_file, "%o\n", e;
end try;
quit;
