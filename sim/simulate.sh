#!/bin/bash
# Simulate generated sorters against the Xilinx UNISIM models with xsim.
#
#   sim/simulate.sh SVDIR WORKDIR DESIGN...
set -uo pipefail
svdir=$(cd "$1" && pwd); shift
mkdir -p "$1"; cd "$1"; shift
glbl="$(dirname "$(dirname "$(command -v vivado)")")/data/verilog/src/glbl.v"
xvlog "$glbl" > glbl.log 2>&1 || { echo "cannot compile $glbl"; exit 1; }
status=0
for d in "$@"; do
  if xvlog -sv "$svdir/$d.sv" "$svdir/${d}_tb.sv" > "xvlog_$d.log" 2>&1 &&
     xelab -L unisims_ver "${d}_tb" glbl -s "${d}_sim" > "xelab_$d.log" 2>&1; then
    result=$(xsim "${d}_sim" -R > "xsim_$d.log" 2>&1; grep -E "^(PASS|FAIL)" "xsim_$d.log")
    if [ -z "$result" ]; then
      echo "FAIL $d: no result from xsim (see xsim_$d.log)"; status=1
    else
      echo "$result"
      case "$result" in PASS*) ;; *) status=1 ;; esac
    fi
  else
    echo "FAIL $d: does not compile (see xvlog_$d.log, xelab_$d.log)"; status=1
  fi
done
exit $status
