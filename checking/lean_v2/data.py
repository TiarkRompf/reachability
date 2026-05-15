#!/usr/bin/env python3
# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "matplotlib",
#     "numpy",
# ]
# ///
import subprocess
import json
import argparse
import matplotlib.pyplot as plt
import numpy as np

import matplotlib
matplotlib.rcParams['pdf.fonttype'] = 42   # TrueType (Type 42) fonts
matplotlib.rcParams['ps.fonttype'] = 42

parser = argparse.ArgumentParser()
parser.add_argument("--no-exec", action="store_true")
parser.add_argument("--log-file", default="data.log")
parser.add_argument("--fig-file", default="data-{}.pdf")
args = parser.parse_args()

if args.no_exec:
    with open(args.log_file) as f:
        output0 = f.read()
else:
    print(r"%running")
    output0 = subprocess.getoutput("lake lean Lean4/ChkExamples.lean")
    with open(args.log_file, "w") as f:
        f.write(output0)

output = output0.replace("(42)", "\"42\"") \
    .replace("(\"", "[\"") \
    .replace("})", "}],") \
    .replace(" :=", "\":") \
    .replace("{ ", "{ \"") \
    .replace(", ", ", \"")
output = "[" + output[:-1] + "]"
data = []
for name, time, cnt_ast, cnt_alg in json.loads(output):
    res = dict(name=name, time=time)
    res.update(cnt_ast)
    res.update(cnt_alg)
    res.pop("world")
    data.append(res)

# group examples: pair up encoded/native by name, separate benchnat
examples = []  # list of (name, encoded, native_or_None)
benchnat = []
seen = {}
for res in data:
    if res["name"].startswith("benchnat-"):
        benchnat.append(res)
    elif res["name"] in seen:
        seen[res["name"]].append(res)
    else:
        entry = [res]
        seen[res["name"]] = entry
        examples.append(entry)
# each entry in examples is [encoded] or [encoded, native]

def sz(r): return r["terms"] + r["types"] + r["quals"]
def qratio(r): return "%.2f" % (r["quals"] / (r["terms"] + r["types"])) if r["terms"] + r["types"] else "---"

def qpct(r): return "%.0f" % (100 * r["quals"] / (r["terms"] + r["types"])) if r["terms"] + r["types"] else "---"

config = [
    ("testcase", lambda enc, nat: r"\textsc{" + enc["name"] + "}"),
    # encoded mega-column
    ("size", lambda enc, nat: sz(enc)),
    ("time (ms)", lambda enc, nat: "%.2f" % enc["time"]),
    # native mega-column
    ("size", lambda enc, nat: sz(nat) if nat else "---"),
    (r"qual.~(\%)", lambda enc, nat: qpct(nat) if nat else "---"),
    ("time (ms)", lambda enc, nat: "%.2f" % nat["time"] if nat else "---"),
]
n_enc = 2  # number of sub-columns under encoded
n_nat = 3  # number of sub-columns under native
alignstr = "l" + (n_enc + n_nat) * "r"
print(r"\begin{tabular}{", alignstr, r"} \toprule", sep="")
print(r"& \multicolumn{", n_enc, r"}{c}{\textsc{encoded}}", sep="", end="\t")
print(r"& \multicolumn{", n_nat, r"}{c}{\textsc{native}}", sep="", end="\t")
print(r"\\ \cmidrule(lr){2-3} \cmidrule(lr){4-6}")
for idx, (col, _) in enumerate(config):
    print("&\t" * bool(idx), r"\textsc{", col, "}", sep="", end="\t")
print(r"\\", r"\midrule")
for entry in examples:
    enc = entry[0]
    nat = entry[1] if len(entry) > 1 else None
    for idx, (_, col) in enumerate(config):
        print("&\t" * bool(idx), col(enc, nat), sep="", end="\t")
    print(r"\\")
print(r"\bottomrule \end{tabular}")

# three families
encoded = [entry[0] for entry in examples]
native = [entry[1] for entry in examples if len(entry) > 1]

families = [
    ("encoded", encoded, "x", "tab:blue"),
    ("native", native, "+", "tab:green"),
    ("benchnat", benchnat, "o", "tab:orange"),
]

# single quadratic fit (through origin) over all data
all_data = encoded + native + benchnat
all_sizes = np.array([r["terms"] + r["types"] + r["quals"] for r in all_data])
all_times = np.array([r["time"] for r in all_data])
A = np.column_stack([all_sizes**2, all_sizes])
coeff, _, _, _ = np.linalg.lstsq(A, all_times, rcond=None)
print('%', coeff)
model = lambda x: coeff[0]*x**2 + coeff[1]*x

# zoom levels: full range, examples range
zooms = [
    (1, all_sizes.max()),
    (2, max(r["terms"] + r["types"] + r["quals"] for r in encoded + native)),
]

for fig_id, xmax in zooms:
    x = np.arange(0, xmax + 10, 10)
    y = model(x)

    fig, ax = plt.subplots()
    ax.plot(x, y, c="tab:orange", linewidth=1)
    for label, fam, marker, color in families:
        s = np.array([r["terms"] + r["types"] + r["quals"] for r in fam])
        t = np.array([r["time"] for r in fam])
        mask = s <= xmax
        if mask.any():
            ax.scatter(s[mask], t[mask], marker=marker, c=color,
                       s=20, label=label, zorder=3)
    ax.set_xlim(0, xmax)
    ax.set_xlabel("ast size")
    ax.set_ylim(0, max(model(xmax), max(
        r["time"] for r in all_data
        if r["terms"] + r["types"] + r["quals"] <= xmax)))
    ax.set_ylabel("time (ms)")
    ax.legend()
    fig.set_size_inches(3.2, 4.8)
    fig.tight_layout()
    fig.savefig(args.fig_file.format(fig_id), bbox_inches="tight")
