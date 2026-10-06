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
status=0
for d in "$@"; do
  # Any warning fails, except these known ones: unused CARRY4 outputs, a timescale
  # only in the testbench, the testbench's initialised clock and reset, and
  # several modules in unisim_models.sv.
  if verilator --binary --timing -Wall -Wno-UNUSEDSIGNAL -Wno-TIMESCALEMOD -Wno-PROCASSINIT \
       -Wno-DECLFILENAME --top-module "${d}_tb" \
       -Mdir "obj_$d" "$models" "$svdir/$d.sv" "$svdir/${d}_tb.sv" > "verilator_$d.log" 2>&1; then
    result=$("./obj_$d/V${d}_tb" ${SEED:+"+seed=$SEED"} > "run_$d.log" 2>&1; grep -E "^(PASS|FAIL)" "run_$d.log")
    if [ -z "$result" ]; then
      echo "FAIL $d: no result from simulation (see run_$d.log)"; status=1
    else
      echo "$result"
      case "$result" in PASS*) ;; *) status=1 ;; esac
    fi
  else
    echo "FAIL $d: does not compile (see verilator_$d.log)"; status=1
  fi
done
exit $status
