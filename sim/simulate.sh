#!/bin/bash
# Simulate generated sorters against the Xilinx UNISIM models with xsim.
#
#   sim/simulate.sh SVDIR WORKDIR DESIGN...
set -u
svdir=$(cd "$1" && pwd); shift
mkdir -p "$1"; cd "$1"; shift
glbl="$(dirname "$(dirname "$(command -v vivado)")")/data/verilog/src/glbl.v"
xvlog "$glbl" > glbl.log 2>&1 || { echo "cannot compile $glbl"; exit 1; }
status=0
for d in "$@"; do
  if xvlog -sv "$svdir/$d.sv" "$svdir/${d}_tb.sv" > "xvlog_$d.log" 2>&1 &&
     xelab -L unisims_ver "${d}_tb" glbl -s "${d}_sim" > "xelab_$d.log" 2>&1; then
    result=$(xsim "${d}_sim" -R 2>&1 | grep -E "^(PASS|FAIL)")
    echo "$result"
    case "$result" in PASS*) ;; *) status=1 ;; esac
  else
    echo "FAIL $d: does not compile (see xvlog_$d.log, xelab_$d.log)"; status=1
  fi
done
exit $status
