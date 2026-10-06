#!/bin/bash
# Simulate generated sorters with Verilator against the behavioural UNISIM
# models in sim/unisim_models.sv: a check that needs no Vivado, run in CI.
#
#   [SEED=n] sim/verilate.sh SVDIR WORKDIR DESIGN...
#
# SEED seeds each testbench's random words (default 1, set by the testbench).
set -uo pipefail
models="$(cd "$(dirname "$0")" && pwd)/unisim_models.sv"
svdir=$(cd "$1" && pwd); shift
mkdir -p "$1"; cd "$1"; shift
bad="^%Warning-(WIDTH[A-Z]*|UNDRIVEN|MULTIDRIVEN|IMPLICIT|PINMISSING):"
status=0
for d in "$@"; do
  # Warnings vary between Verilator versions, so only those that point to real
  # bugs (width mismatches, undriven or multiply driven nets, implicit nets,
  # missing pins) fail the build. The rest are left in the log.
  if verilator --binary --timing -Wall -Wno-fatal --top-module "${d}_tb" \
       -Mdir "obj_$d" "$models" "$svdir/$d.sv" "$svdir/${d}_tb.sv" > "verilator_$d.log" 2>&1; then
    if grep -qE "$bad" "verilator_$d.log"; then
      echo "FAIL $d: Verilator warnings (see verilator_$d.log)"; status=1
      grep -m 5 -E "$bad" "verilator_$d.log"
      continue
    fi
    result=$("./obj_$d/V${d}_tb" ${SEED:+"+seed=$SEED"} > "run_$d.log" 2>&1; grep -E "^(PASS|FAIL)" "run_$d.log")
    if [ -z "$result" ]; then
      echo "FAIL $d: no result from simulation (see run_$d.log)"; status=1
    else
      echo "$result"
      case "$result" in PASS*) ;; *) status=1 ;; esac
    fi
  else
    echo "FAIL $d: does not compile (see verilator_$d.log)"; status=1
    grep -m 5 -E "^%(Error|Warning)" "verilator_$d.log"
  fi
done
exit $status
