#!/usr/bin/env python3
"""Tabulate Vivado results as Markdown.

    report.py SVDIR RUNDIR...

For each implemented design found in the run directories, print its cells,
slices used, bounding box (from SVDIR/designs.tsv), worst setup slack, the
clock frequency that slack implies, and whether the placement honours the
generated layout (vivado/check_placement.py).
"""
import os
import subprocess
import sys

here = os.path.dirname(os.path.abspath(__file__))
svdir, rundirs = sys.argv[1], sys.argv[2:]
boxes = {}
with open(os.path.join(svdir, "designs.tsv")) as f:
    next(f)
    for line in f:
        name, words, bits, latency, cols, rows = line.split()
        boxes[name] = (int(words), int(bits), int(latency), int(cols), int(rows))

results = {}
for rundir in rundirs:
    for name in os.listdir(rundir):
        summary = os.path.join(rundir, name, f"{name}_summary.txt")
        if not os.path.isfile(summary):
            continue
        fields = dict(line.split(None, 1) for line in open(summary) if " " in line)
        check = subprocess.run(
            [sys.executable, os.path.join(here, "check_placement.py"),
             os.path.join(svdir, f"{name}.sv"), os.path.join(rundir, name, f"{name}_placement.tsv")],
            capture_output=True, text=True)
        cells = check.stdout.split()[0]
        results[name] = (cells, int(fields["slices"]), float(fields["period_ns"]),
                         float(fields["wns_ns"]), check.returncode == 0)

order = {"bitonic": 0, "oddeven": 1, "balanced": 2, "periodic": 3}
def key(name):
    family = name.rstrip("0123456789x")
    words, bits = boxes[name][0], boxes[name][1]
    return (bits, words, order.get(family, 9))

print("| design | words × bits | latency | cells | slices used | bounding box | worst slack | f<sub>max</sub> | layout |")
print("|---|---|---:|---:|---:|---:|---:|---:|---|")
for name in sorted(results, key=key):
    words, bits, latency, cols, rows = boxes[name]
    cells, slices, period, wns, ok = results[name]
    fmax = 1000.0 / (period - wns)
    dense = " (full)" if slices == cols * rows else ""
    print(f"| {name} | {words} × {bits} | {latency} | {cells} | {slices}{dense} | {cols} × {rows} | "
          f"{wns:+.3f} ns | {fmax:.0f} MHz | {'honoured' if ok else 'NOT honoured'} |")
