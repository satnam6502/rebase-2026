#!/bin/bash
# Implement each design named on the command line with Vivado, JOBS at a time,
# and check that the placement honours the generated layout.
#
#   vivado/implement_all.sh SVDIR OUTDIR DESIGN...
#
# Environment: PART (xc7a200tsbg484-1), PERIOD in ns (4.0), JOBS (6) and ORIGIN
# (X36Y50), the slice that anchors each relatively placed macro. Without an
# anchor Vivado searches for a legal origin, which is slow for large macros. On
# the xc7a200t the slices from X36Y50 to X133Y177 contain no holes, room for
# every sorter up to 128 words of 4 bits.
set -u
here=$(cd "$(dirname "$0")" && pwd)
svdir=$(cd "$1" && pwd); shift
mkdir -p "$1"; outdir=$(cd "$1" && pwd); shift
jobs=${JOBS:-6}

run_one() {
  d=$1
  cd "$outdir"
  vivado -mode batch -nojournal -nolog -source "$here/implement.tcl" \
    -tclargs "$d" "$svdir" "$outdir/$d" ${PART:-xc7a200tsbg484-1} ${PERIOD:-4.0} ${ORIGIN:-X36Y50} > "$d.log" 2>&1
  if [ -f "$d/${d}_placement.tsv" ]; then
    echo "$d: $(grep wns "$d/${d}_summary.txt") $(grep slices "$d/${d}_summary.txt") | $(python3 "$here/check_placement.py" "$svdir/$d.sv" "$d/${d}_placement.tsv")"
  else
    echo "$d: FAILED ($(grep -m1 ERROR "$d.log"))"
  fi
}
export -f run_one
export here svdir outdir
printf "%s\n" "$@" | xargs -P "$jobs" -I{} bash -c 'run_one {}'
