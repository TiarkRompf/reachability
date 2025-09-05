#!/usr/bin/env python3
import subprocess
import json
import argparse
import matplotlib.pyplot as plt
import numpy as np

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

config = [
    ("testcase", lambda x: r"\textsc{" + x["name"] + "}"),
    ("ast size", lambda x: x["terms"] + x["types"] + x["types"]),
    ("\\#qual", lambda x: x["types"]),
    ("time (ms)", lambda x: "%.2f" % x["time"]),
    ("\\#unif.", lambda x: x["cnt_unify"]),
    ("\\#infer", lambda x: x["cnt_growth"] + x["cnt_avoid"] + x["cnt_inferqf"]),
]
alignstr = "l" + (len(config) - 1) * "r"
print(r"\begin{tabular}{", alignstr, r"} \toprule", sep="")
for idx, (col, _) in enumerate(config):
    print("&\t" * bool(idx), r"\textsc{", col, "}", sep="", end="\t")
print(r"\\", r"\midrule")
for res in data:
    if res["name"].startswith("benchnat"): continue
    for idx, (_, col) in enumerate(config):
        print("&\t" * bool(idx), col(res), sep="", end="\t")
    print(r"\\")
print(r"\bottomrule \end{tabular}")

datalist = [[], []]
for i in data:
    data2 = datalist[1] if i["name"].startswith("benchnat-") else datalist[0]
    data2.append(i)

for idx, data2 in enumerate(datalist, 1):
    nterms = np.array([i["terms"] for i in data2])
    ntypes = np.array([i["types"] for i in data2])
    sizes = nterms + ntypes
    times = np.array([i["time"] for i in data2])
    coeff = np.polyfit(sizes, times, idx)
    print('%', coeff)
    model = np.poly1d(coeff)
    x = np.arange(0, sizes.max() + 50, 50)
    y = model(x)

    fig, ax = plt.subplots()
    ax.plot(x, y, c="tab:orange")
    ax.scatter(sizes, times, marker="x")
    ax.set_xlim(0, sizes.max())
    ax.set_xlabel("ast size")
    ax.set_ylim(0, max(times.max(), y.max()))
    ax.set_ylabel('time (ms)')
    fig.set_size_inches(3.2, 4.8)
    fig.tight_layout()
    fig.savefig(args.fig_file.format(idx))
