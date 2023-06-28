# Attach this to a running copy of Sage

import os
opj, ope = os.path.join, os.path.exists
from collections import Counter, defaultdict
from sage.all import ZZ
import subprocess


def create_upload_files(ppolfolder, npolfolder, exclude_gq=[]):
    isodata = []
    poldata = []
    wedata = []
    polcnts = Counter()
    poldegs = defaultdict(set)
    by_isodeg = defaultdict(lambda: defaultdict(list))
    for base in [ppolfolder, npolfolder]:
        for label in os.listdir(opj(base, "av_fq_pol_output")):
            if exclude_gq:
                g, q, isocls = label.split(".")
                if (g,q) in exclude_gq:
                    continue
            with open(opj(base, "av_fq_pol_output", label)) as F:
                for line in F:
                    pieces = line.split(":")
                    if base == ppolfolder:
                        polcnts[label] += 1
                        # Need to insert rr, rl, lr, ll degrees and kernels
                        pieces[6:6] = ["1:{}:1:{}:1:{}:1:{}"]
                    else:
                        # In the nonprincipal case, we included the endomorphism ring label in the isom_label, while in the principal case we didn't.  We trim it out here
                        assert pieces[3].count(".") == 3
                        pieces[3] = ".".join(pieces[3].split(".")[2:])
                    # Some representatives surpass the limit of 131072 digits for a numeric type.  So we make them strings instead, since we're using jsonb.
                    rep = pieces[-1]
                    den, num = rep[1:-2].split(",[")
                    num = num.split(",")
                    key = tuple(ZZ(n)/ZZ(den) for n in num)
                    if len(rep) > 131072:
                        if len(den) > 131072 or any(len(n) > 131072 for n in num):
                            num = ",".join(f'"{n}"' for n in num)
                            pieces[-1] = f'["{den}",[{num}]]\n'
                    by_isodeg[pieces[0]][int(pieces[4])].append((key, pieces))
    # Now that we have polarized abvars sorted by their unpolarized isomorphism class and degree,
    # we throw out those that aren't minimal for degree (under the divisibility order),
    # sort and add pol_ctr to the data line, and add degree and pol_ctr to the label
    for ulabel, by_deg in by_isodeg.items():
        keep = [d for d in by_deg if len([e for e in by_deg if d % e == 0]) == 1]
        for d in keep:
            for i, (key, pieces) in enumerate(sorted(by_deg[d])):
                pieces[0] += f".{d}.{i+1}"
                pieces[4:4] = [str(i+1)]
                poldata.append(":".join(pieces))
    for label in os.listdir(opj(ppolfolder, "av_fq_we_output")):
        if exclude_gq:
            g, q, isocls = label.split(".")
            if (g,q) in exclude_gq:
                continue
        with open(opj(ppolfolder, "av_fq_we_output", label)) as F:
            for line in F:
                # The isogeny label was left off of the label; fortunately it came first
                wedata.append(f"{label}.line")
    for label in os.listdir(opj(ppolfolder, "av_fq_isog_output")):
        if exclude_gq:
            g, q, isocls = label.split(".")
            if (g,q) in exclude_gq:
                continue
        with open(opj(ppolfolder, "av_fq_isog_output", label)) as F:
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
        _ = F.write(":".join(["label", "isog_label", "endomorphism_ring", "isom_label", "pol_ctr", "degree", "kernel", "degree_rr", "kernel_rr", "degree_rl", "kernel_rl", "degree_lr", "kernel_lr", "degree_ll", "kernel_ll", "aut_group", "geom_aut_group", "is_jacobian", "representative"]) + "\n")
        _ = F.write(":".join(["text", "text", "text", "text", "integer", "smallint", "smallint[]", "smallint", "smallint[]", "smallint", "smallint[]", "smallint", "smallint[]", "smallint", "smallint[]", "text", "text", "boolean", "jsonb"]) + "\n\n")
        _ = F.write("".join(poldata))

def compute_diagramx(basefolder, outfile="av_fq_diagramx.update", parallelopts="-j32 --timeout 60"):
    # Given a folder containing weak equivalence data (in the form read by LoadSchemaWKClasses), uses graphviz to find a layout for the endomorphism rings in each weak equivalence class.
    diagramx = {}
    todofile = "/tmp/abvar_diagramx.todo"
    indir = "/tmp/abvar_diagramx_in"
    outdir = "/tmp/abvar_diagramx_out"
    os.makedirs(indir, exist_ok=True)
    os.makedirs(outdir, exist_ok=True)
    todo = []
    for label in os.listdir(basefolder):
        if ope(opj(outdir, label)): # diagramx already computed for this isogeny class
            continue
        todo.append(label)
        if ope(opj(indir, label)): # input file already exists for this isogeny class
            continue
        nodes = []
        edges = []
        ranks = defaultdict(list)
        mlabels = []
        with open(opj(basefolder, label)) as F:
            for line in F:
                pieces = line.strip().split(":")
                invertible, mring, min_over, pic_size = pieces[7], pieces[3], pieces[10], pieces[2]
                if invertible == "t":
                    mlabels.append(mring)
                    if len(min_over) == 2: # [] or {}
                        min_over = ""
                    else:
                        min_over = '","'.join(min_over[1:-1].split(","))
                    N = ZZ(mring.split(".")[0])
                    # We get an approximation to the latex used (we don't omit .1 when there's only one mring of a given index; it won't matter since in that case horizontal space isn't a big deal; and we omit the number of weak equivalence classes with a given mring)
                    if N == 1:
                        factored_index = "1"
                    else:
                        factored_index = r"\cdot".join((f"{p}^{{{e}}}" if e > 1 else f"{p}") for (p, e) in N.factor())
                    istr = f"_{{{i}}}"
                    tex = "[%s]%s%s" % (factored_index, pic_size, istr)
                    nodes.append(f'"{mring}" [label="{tex}",shape=plaintext]')
                    if min_over:
                        edges.append(f'"{mring}" -> {{"{min_over}"}} [dir=none]')
                    ranks[sum(e for (p,e) in N.factor())].append(mring)
        if len(nodes) <= 3:
            # early exits, since we don't need to do anything in these cases
            with open(opj(outdir, label), "w") as F:
                _ = F.write("graph 1.0\n")
                for mring in mlabels:
                    _ = F.write(f'node "{mring}" 0.5\n')
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
            with open(opj(indir, label), "w") as F:
                _ = F.write(graph)
    if todo:
        with open(todofile, "w") as Ftodo:
            _ = Ftodo.write("\n".join(todo) + "\n")
        subprocess.run('parallel %s -a %s "dot -Tplain -o %s/{1} %s/{1}"' % (parallelopts, todofile, outdir, indir), shell=True, check=True)
    with open(outfile, "w") as Fout:
        _ = Fout.write("label|diagramx\ntext|smallint\n\n")
        for label in os.listdir(outdir):
            with open(opj(outdir, label)) as F:
                # When there are long output lines, dot uses a backslash at the end of the line to indicate a line continuation.
                maxx = 0
                minx = 10000
                lines = []
                continuing = False
                for line in F:
                    line = line.strip()
                    if continuing:
                        lines[-1] += line
                    else:
                        lines.append(line)
                    continuing = line[-1] == "\\"
                    if continuing:
                        lines[-1] = lines[-1][:-1]
                for line in lines:
                    if line == "graph 1.0":
                        scale = 1.0
                    elif line.startswith("graph"):
                        scale = float(line.split()[2])
                    elif line.startswith("node"):
                        pieces = line.split()
                        mring = pieces[1].replace('"', '')
                        diagram_x = int(round(10000 * float(pieces[2]) / scale))
                        _ = Fout.write(f"{label}.{mring}.1|{diagram_x}\n")
