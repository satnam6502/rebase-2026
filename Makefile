# ruby-lean: verified Batcher sorters for Xilinx FPGAs, from a Ruby DSL in Lean.

LAKE   ?= lake
SV     := build/sv
SVLOC  := build/sv_loc
SIMDIR := build/sim
IMPL   := build/vivado
IMPLOC := build/vivado_loc
ORIGIN ?= X36Y50

# Designs simulated by `make sim` (all four sorter families, several sizes and widths).
SIM_DESIGNS ?= \
  bitonic2x4 bitonic4x4 oddeven4x4 balanced4x4 periodic4x4 \
  bitonic8x4 oddeven8x4 balanced8x4 periodic8x4 \
  bitonic16x4 oddeven16x4 balanced16x4 periodic16x4 \
  bitonic32x4 oddeven32x4 balanced32x4 periodic32x4 \
  bitonic8x8 oddeven8x8 balanced8x8 periodic8x8 \
  bitonic4x16 oddeven4x16 balanced4x16 periodic4x16

# Designs implemented by `make impl`, out of context on an xc7a200t. These are
# relocatable RLOC macros, each anchored at slice ORIGIN.
IMPL_DESIGNS ?= \
  bitonic4x4 bitonic8x4 bitonic16x4 oddeven16x4 balanced16x4 periodic16x4 \
  bitonic32x4 oddeven32x4 balanced32x4 periodic32x4 \
  bitonic64x4 oddeven64x4 bitonic8x8

# The largest designs, placed with absolute LOCs at ORIGIN: Vivado's macro
# shape builder is very slow on RLOC macros this big.
IMPL_LOC_DESIGNS ?= \
  balanced64x4 periodic64x4 bitonic128x4 oddeven128x4 balanced128x4 periodic128x4

.PHONY: all lean sv sim impl clean

all: lean sv sim

## Check every definition and proof.
lean:
	$(LAKE) build

## Emit SystemVerilog modules, testbenches and designs.tsv: relocatable macros
## in build/sv, and the same layouts at ORIGIN with absolute LOCs in build/sv_loc.
sv:
	$(LAKE) exe ruby-sv $(SV)
	$(LAKE) exe ruby-sv $(SVLOC) --loc $(ORIGIN)

## Simulate against the Xilinx UNISIM models with Vivado's xsim.
sim: sv
	sim/simulate.sh $(SV) $(SIMDIR) $(SIM_DESIGNS)

## Place and route with Vivado, check the placement against the Lean layout,
## and tabulate the results.
impl: sv
	ORIGIN=$(ORIGIN) vivado/implement_all.sh $(SV) $(IMPL) $(IMPL_DESIGNS)
	vivado/implement_all.sh $(SVLOC) $(IMPLOC) $(IMPL_LOC_DESIGNS)
	vivado/report.py $(SV) $(IMPL) $(IMPLOC)

clean:
	rm -rf build
