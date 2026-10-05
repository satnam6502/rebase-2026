#!/usr/bin/env python3
"""Check that Vivado placed every cell where the Lean layout semantics put it.

    check_placement.py DESIGN.sv DESIGN_placement.tsv

The generated SystemVerilog gives each instance an RLOC (slice relative to the
macro origin), or an absolute LOC, and a BEL. The placement report gives the
site and BEL Vivado chose. The layout is honoured when every cell sits at the
same offset from its RLOC (offset 0 for LOCs) and on its requested BEL.
"""
import re
import sys

# RLOC = "XnYm" (relative to the macro origin) or LOC = "SLICE_XnYm" (absolute).
attr = re.compile(r'R?LOC = "(?:SLICE_)?X(\d+)Y(\d+)", BEL = "(\w+)"')
inst = re.compile(r'^\s*\w+\s*(?:#\(.*?\))?\s+(\w+)\s*\(')

expected = {}
pending = None
with open(sys.argv[1]) as f:
    for line in f:
        m = attr.search(line)
        if m:
            pending = (int(m.group(1)), int(m.group(2)), m.group(3))
            continue
        if pending:
            m = inst.match(line)
            if m:
                expected[m.group(1)] = pending
            pending = None

offsets = set()
bad_bel = []
placed = 0
with open(sys.argv[2]) as f:
    for line in f:
        name, rloc, loc, bel = line.rstrip("\n").split("\t")
        placed += 1
        rx, ry, want = expected[name]
        sx, sy = map(int, re.match(r"SLICE_X(\d+)Y(\d+)", loc).groups())
        offsets.add((sx - rx, sy - ry))
        if bel.split(".")[-1] != want:
            bad_bel.append((name, want, bel))

ok = len(offsets) == 1 and not bad_bel and placed == len(expected)
print(f"{placed} of {len(expected)} cells placed; origin offsets {sorted(offsets)[:4]}; "
      f"{len(bad_bel)} BEL mismatches -> {'LAYOUT HONOURED' if ok else 'LAYOUT NOT HONOURED'}")
for b in bad_bel[:10]:
    print("  BEL mismatch:", b)
sys.exit(0 if ok else 1)
