# Attach this to a running copy of Sage

opj = os.path.join
from collections import Counter, defaultdict
from sage.all import ZZ


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
                    # Some representatives surpass the limit of 131072 digits for a numeric type.  So we make them strings instead, since we're using jsonb.
                    if len(line) > 131072:
                        pieces = line.split(":")
                        rep = pieces[-1]
                        den, num = rep[1:-2].split(",[")
                        if len(den) > 131072 or any(len(n) > 131072 for n in num):
                            num = ",".join(f'"{n}"' for n in num)
                            pieces[-1] = f'["{den}",[{num}]]\n'
                            line = ":".join(pieces)
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

def load

def compute_diagramx(basefolder, outfile="av_fq_diagramx.update", parallelopts="-j32 --timeout 60"):
    # Given a folder containing weak equivalence data (in the form read by LoadSchemaWKClasses), uses graphviz to find a layout for the endomorphism rings in each weak equivalence class.
    diagramx = {}
    os.makedirs("/tmp/abvar_diagramx_in")
    os.makedirs("/tmp/abvar_diagramx_out")
    for label in os.listdir(basefolder):
        nodes = []
        edges = []
        ranks = defaultdict(list)
        mlabels = []
        with open(opj(basefolder, label)) as F:
            for line in F:
                pieces = line.strip().split(":")
                invertible, mring, min_over = pieces[7], pieces[3], pieces[10]
                if invertible == "t":
                    mlabels.append(mring)
                    if len(min_over) == 2: # [] or {}
                        min_over = ""
                    else:
                        min_over = '","'.join(min_over[1:-1].split(","))
                    N = ZZ(mring.split(".")[0])
                    nodes.append(f'"{mring}" [label="{tex}"],shape=plaintext]')
                    if min_over:
                        edges.append(f'"{mring}" -> {{"{min_over}"}} [dir=none]')
                    ranks[sum(e for (p,e) in N.factor())].append(mring)
        if len(nodes) <= 3:
            # early exits, since we don't need to do anything in these cases
            # We write 
            for mring in mlabels:
                diagramx[f"{label}.{mring}.1"] = 5000
        else:
            nodes = ";\n".join(nodes)
            edges = ";\n".join(edges)
            if edges:
                edges += ";" # deal with no edges by moving semicolon here.
            ranks = ";\n".join('{rank=same; "%s"}' % ('" "'.join(labs)) for labs in ranks.values())
            graph = f"""strict digraph "{label}" {{
rankdir=TB;
splines=line;
{edges}
{nodes};
{ranks};
}}
"""
            infile = opj("/tmp", "abvar_diagramx_in", label)
            with open(infile, "w") as F:
                _ = F.write(graph)
    subprocess.run('ls /tmp/abvar_diagramx_in | parallel %s "dot -Tplain -o /tmp/abvar_diagramx_out/{1} /tmp/abvar_diagramx_in/{1}"' % parallelopts, shell=True, check=True)
    for label in os.listdir("/tmp/abvar_diagramx_out")
