#!/usr/bin/env python3
"""Find a slice where a relatively placed macro fits without holes.

    find_origin.py PART COLUMNS ROWS

Dumps the slice sites of PART with Vivado (cached in build/slices_PART.txt) and
prints the first origin XxYy such that every slice of a COLUMNS x ROWS
rectangle from it exists. Use it as ORIGIN for vivado/implement_all.sh when
targeting another part. COLUMNS and ROWS are the slice dimensions printed in
the header of each generated module and listed in designs.tsv.
"""
import os
import subprocess
import sys

part, cols, rows = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
cache = os.path.join("build", f"slices_{part}.txt")
if not os.path.exists(cache):
    os.makedirs("build", exist_ok=True)
    tcl = os.path.join("build", f"slices_{part}.tcl")
    with open(tcl, "w") as f:
        f.write(f"link_design -part {part} -quiet\n"
                f"set f [open {cache} w]\n"
                "foreach s [get_sites SLICE_*] { regexp {SLICE_X(\\d+)Y(\\d+)} $s -> x y; puts $f \"$x $y\" }\n"
                "close $f\n")
    subprocess.run(["vivado", "-mode", "batch", "-nojournal", "-nolog", "-source", tcl],
                   check=True, stdout=subprocess.DEVNULL)

sites = {tuple(map(int, line.split())) for line in open(cache)}
xs = sorted({x for x, _ in sites})
ys = sorted({y for _, y in sites})
for y0 in ys:
    for x0 in xs:
        if all((x0 + dx, y0 + dy) in sites for dx in range(cols) for dy in range(rows)):
            print(f"X{x0}Y{y0}")
            sys.exit(0)
sys.exit(f"no hole-free {cols} x {rows} region on {part}")
