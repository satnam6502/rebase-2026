#!/bin/bash
# Check that the testbenches catch a wrong sorter and that their seeds are
# reproducible, using sim/verilate.sh on a copy of bitonic4x4 whose smallest
# output word has its low bit stuck at 1.
#
#   sim/selftest.sh SVDIR WORKDIR
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
svdir=$(cd "$1" && pwd)
mkdir -p "$2/sv"; cd "$2"
grep -q "assign b\[0\]\[0\] = " "$svdir/bitonic4x4.sv"
sed "s/assign b\[0\]\[0\] = .*;/assign b[0][0] = 1'b1;/" "$svdir/bitonic4x4.sv" > sv/bitonic4x4.sv
cp "$svdir/bitonic4x4_tb.sv" sv/

# Each run must fail, and report its seed.
run() {
  local out status=0
  out=$(SEED=$1 "$here/verilate.sh" sv "work" bitonic4x4) || status=$?
  [ "$status" -eq 1 ] || { echo "selftest: broken sorter did not fail (seed $1)" >&2; exit 1; }
  echo "$out" | grep -q "^FAIL bitonic4x4: .* vectors wrong (seed $1)$" ||
    { echo "selftest: unexpected result for seed $1: $out" >&2; exit 1; }
  grep MISMATCH work/run_bitonic4x4.log
}
a=$(run 1); b=$(run 1); c=$(run 2)
[ "$a" = "$b" ] || { echo "selftest: seed 1 is not reproducible"; exit 1; }
[ "$a" != "$c" ] || { echo "selftest: seeds 1 and 2 give the same stimulus"; exit 1; }
echo "selftest: a broken sorter fails, and seeds are reproducible"
