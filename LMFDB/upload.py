# Attach this to a running copy of Sage

opj = os.path.join
from collections import Counter

def create_upload_files(basefolders, exclude_gq=[]):
    isodata = []
    poldata = []
    wedata = []
    polcnts = Counter()
    for base in basefolders:
        for label in os.listdir(opj(base, "av_fq_pol_output")):
            if exclude_gq:
                g, q, isocls = label.split(".")
                if (g,q) in exclude_gq:
                    continue
            with open(opj(base, "av_fq_pol_output", label)) as F:
                for line in F:
                    polcnts[label] += 1
                    poldata.append(line)
        for label in os.listdir(opj(base, "av_fq_we_output")):
            if exclude_gq:
                g, q, isocls = label.split(".")
                if (g,q) in exclude_gq:
                    continue
            with open(opj(base, "av_fq_we_output", label)) as F:
                for line in F:
                    wedata.append(line)
        for label in os.listdir(opj(base, "av_fq_isog_output")):
            if exclude_gq:
                g, q, isocls = label.split(".")
                if (g,q) in exclude_gq:
                    continue
            with open(opj(base, "av_fq_isog_output", label)) as F:
                pic_prime_gens = F.read().strip()
                isodata.append(f"{label}:{polcnts[label]}:{pic_prime_gens}\n")
    with open("av_fq_isog.update", "w") as F:
        _ = F.write(":".join(["label", "principal_polarization_count", "pic_prime_gens"]) + "\n")
        _ = F.write(":".join(["text", "integer", "integer[]"]) + "\n\n")
        _ = F.write("".join(isodata))
    with open("av_fq_weak_equivalences.update", "w") as F:
        _ = F.write(":".join(["label", "pic_invs", "pic_basis", "is_product", "product_partition", "is_conjugate_stable", "generator_over_ZFV", "is_Zconductor_sum", "is_ZFVconductor_sum"]) + "\n")
        _ = F.write(":".join(["text", "integer[]", "integer[]", "boolean", "jsonb", "boolean", "jsonb", "boolean", "boolean"]) + "\n\n")
        _ = F.write("".join(wedata))
    with open("av_fq_pol.update", "w") as F:
        _ = F.write(":".join(["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "aut_group", "geom_aut_group", "is_jacobian", "representative"]) + "\n")
        _ = F.write(":".join(["text", "text", "text", "text", "smallint", "smallint[]", "text", "text", "boolean", "jsonb"]) + "\n\n")
        _ = F.write("".join(poldata))
