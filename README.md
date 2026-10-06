# ruby-lean

A Ruby-style hardware description language embedded in Lean 4, with
Batcher's sorters as the case study. The same circuit description yields:

1. **an implementation**: flat SystemVerilog of Xilinx 7-series primitives
   (`LUT`, `CARRY4`, `FDCE`) for Vivado;
2. **proofs**: the circuits' behaviour is a structural semantics of their
   terms. The sorters are proved to sort for **every** degree and word width,
   as combinational functions and as pipelines;
3. **a layout**: relative placement (`RLOC`/`BEL`) derived from the
   combinators. It is proved compact, free of overlaps and dense for every
   degree, and Vivado honours it exactly.

The sorters are ports of the Batcher sorters and FPGA layouts of
[`xilinx-lava`](../xilinx-lava). There are four cores: bitonic, odd–even
merge, and the two periodic sorters of Claessen, Sheeran and Singh's sorter
core paper. They are related to one another by Bird–Meertens calculation, in
the style of `rtl/experiments/bird-meertens/BirdMeertens/Sorters.lean`.

Lean `v4.34.1` with Mathlib `v4.34.1`. The project has no other
dependencies; it does not use `../lhdl`.

## Contents

- [Design of the DSL](#design-of-the-dsl)
- [Lessons from earlier experiments](#lessons-from-earlier-experiments)
- [The sorters](#the-sorters)
- [What is proved](#what-is-proved)
- [Layout](#layout)
- [Building, simulating and implementing](#building-simulating-and-implementing)
- [Results](#results)
- [Limitations](#limitations)

## Design of the DSL

A circuit is a **term**, `Circuit a b`, relating bundles of wires of shape `a`
to bundles of shape `b`
([Ruby/Core.lean](Ruby/Core.lean)). Shapes are bits, pairs and vectors
([Ruby/Shape.lean](Ruby/Shape.lean)). The constructors are the Ruby
combinators, and each has a geometric reading:

| constructor | Ruby | behaviour | layout |
|---|---|---|---|
| `prim p` | primitive | Xilinx `LUTk`, `CARRY4`, `FDCE` | one LUT row, or a whole slice for `CARRY4` |
| `wire w` | wiring | routes, copies, drops, ties off wires | no area |
| `r >-> s` | `r ; s` | serial composition | `s` to the right of `r` |
| `r >^> s` | `r ; s` | serial composition | `s` above `r` (carry chains) |
| `r >\|> s` | `r ; s` | serial composition | `s` on top of `r` (a LUT and its flip-flop) |
| `r ‖ s` | `[r, s]` | parallel composition on pairs | `r` below `s` |
| `map n r` | `map_n r` | `r` on each element of a vector | stacked, element `0` at the bottom |

Everything else is derived ([Ruby/Combinators.lean](Ruby/Combinators.lean)):
`fst`, `snd`, `two`, `parl`, `ilv`, `evens`, `riffle`, `unriffle`, `alt`,
`vee`, `que`, `hrep`, Ruby's `col`, the butterfly mergers and the sorters.

Because circuits are data, every interpretation is a structural recursion
over the term:

| interpretation | definition | used for |
|---|---|---|
| combinational behaviour | `Circuit.eval` (wires carry `Bool`) | functional correctness |
| synchronous behaviour | `Circuit.evalS` (wires carry `Nat → Bool`) | pipelines |
| latency | `Circuit.latency` | registers on every path |
| layout | `Circuit.size`, `Circuit.sites` | relative placement |
| netlist | `Circuit.gen` (wires carry `Net`) | SystemVerilog |

**Wiring is polymorphic in the wire type.** A `Wiring a b` is a function
`∀ β, (Bool → β) → a.Val β → b.Val β`. It cannot inspect wires; it can only
route, copy, drop or tie them off. Its single obligation is that it commutes
with a change of wire type (`natural`), discharged by `rfl` or a case split.
This is what lets one description serve all interpretations: wiring builds no
hardware in the netlist, takes no area in the layout, and is pure reindexing
in the semantics. It also gives the retiming theorem `Circuit.evalS_sample`
in one structural induction: a circuit whose paths all carry `k` registers
outputs, at cycle `t + k`, its combinational function of the inputs at cycle
`t`.

**Primitives follow the UNISIM simulation models.** For example, `CARRY4` is
`CO[i] = S[i] ? c_i : DI[i]` and `O[i] = S[i] ^ c_i` with
`c_0 = CI | CYINIT`, as in Vivado's `CARRY4.v`.

## Lessons from earlier experiments

| experiment | what worked | what this design changes |
|---|---|---|
| `xilinx-lava` (Haskell, tagless final) | Combinator-based layout (`>->`, `>\|>`, `vpar2`, `vmap`) produced placed sorters up to 128 inputs. | Lava rebuilt the layout tree by popping blocks off a stack whenever the netlist grew, so wiring had no layout meaning and the scheme was fragile. Here layout is a structural interpretation of the term, and theorems about it are possible. Lava's correctness evidence was simulation and EQY at fixed sizes; here it is proofs at every size. |
| `lhdl` / `alt-lhdl` (Lean, monadic typeclass) | One description, several semantics (relational, functional, netlist). | The Batcher proofs were fixed-size (4 and 8 inputs) and found by heavy unfolding and search. The general merger theorem in `rtl/docs/v2l_backends/Ruby.lean` stayed `sorry`. The "pipeline latency" theorems evaluated a separately defined number, not a property of the circuit. Here latency is computed from the circuit and connected to its stream semantics. Vectors are `Fin n → α` rather than `List.Vector`, and lengths are written `m * 2` so `2 ^ (n + 1)` is *definitionally* `2 ^ n * 2`: the recursive networks need no `▸` casts. |
| Bird–Meertens `Sorters.lean` (lists) | The four cores related by wiring laws, one `fly` schema. | Its correctness checks were for 4 and 8 inputs only. Here the same laws are proved over `Fin` vectors, and the sorters are proved to sort at every degree. |

## The sorters

[Ruby/Sorting/Networks.lean](Ruby/Sorting/Networks.lean) defines the networks
over any two-input cell `f`, on `2 ^ n` wires:

```
bfly f (n+2)   = ilv (bfly f (n+1)) ⨾ evens f          -- Batcher's bitonic merger
mergeOE f (n+2) = ilv (mergeOE f (n+1)) ⨾ midEvens f   -- Batcher's odd–even merger
vfly f (n+2)   = vee (vfly f (n+1)) ⨾ evens f          -- Dowd et al.'s balanced merger
qfly f (n+2)   = que (qfly f (n+1)) ⨾ midEvens f       -- Canfield–Williamson merger

sortB f (n+1)  = parl (sortB f n) (sortB f n ⨾ rev) ⨾ bfly f (n+1)
sortOE f (n+1) = two (sortOE f n) ⨾ mergeOE f (n+1)
sortV f n      = hrep n (vfly f n)
sortQ f n      = hrep n (qfly f n)
```

The hardware sorters ([Ruby/Sorter/Cell.lean](Ruby/Sorter/Cell.lean)) use the
same patterns as circuits, with `xilinx-lava`'s pipelined two-sorter as the
cell. Each output word has its own half of the cell:

```
          X0 (comparator)                       X1 (selection)
  max:    CARRY4 chain computing b ≥ a          LUT3 muxes (8'hE4) + FDCEs
  min:    CARRY4 chain computing a ≥ b          LUT3 muxes (8'hE4) + FDCEs
```

In each comparator slice, LUTs A–D compute `S = a XNOR b` (`LUT2`, `4'h9`)
and the `CARRY4` takes `DI = a`. For `4k`-bit words the comparator is Ruby's
`col` of `k` `CARRY4` slices, with the carry on the dedicated chain. The
odd–even and Canfield–Williamson patterns pass two wires around their middle
column. Those wires go through a register word (`delayW`), so every path has
the same latency.

## What is proved

Every statement below is proved with no `sorry`, `admit`, `native_decide` or
extra axioms. Each is universally quantified over the degree `n` (`2 ^ n`
inputs) and, for hardware, over the word width `4k`.
[Ruby/Summary.lean](Ruby/Summary.lean) restates the headline theorems
together.

**The networks sort**, over any linear order
([Ruby/Sorting](Ruby/Sorting)):

- `sortB_sorts`, `sortOE_sorts`, `sortV_sorts`, `sortQ_sorts`: the output is
  `mergeSort` of the input.
- The proof route:
  - `zero_one` is the zero–one principle, via commutation with monotone maps.
  - `IsPerm.*` shows a network of compare–exchange cells permutes its input.
  - `bfly_ind` shows the butterfly sorts any bit vector whose ones form one
    segment.
  - `mergeB_ind` and `mergeOE_ind` show both mergers merge sorted halves.
  - `mergeB_ksorted` and `mergeOE_ksorted` show both mergers preserve
    `2^j`-sortedness of their halves. Hence each `unriffle ⨾ merge` pass halves
    the period, and `n` passes sort.

**Bird–Meertens refinement**: each core is derived from the previous one
([Ruby/Sorting/Derivation.lean](Ruby/Sorting/Derivation.lean)). Every line
below is a network and every step names its law:

```
sortB (n+1)
  = two (sortB n) ⨾ mergeB n                 -- the reversal belongs to the merger (sortB_succ)
  = two (sortB n) ⨾ mergeOE (n+1)            -- merger exchange on sorted halves (merge_exchange)
  = two (sortOE n) ⨾ mergeOE (n+1)           -- induction
  = sortOE (n+1)

sortOE (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))    -- the periodic law (periodicOE_sorts)
  = hrep (n+1) (qfly (n+1))                  -- qfly_eq
  = sortQ (n+1)

sortQ (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))    -- qfly_eq
  = hrep (n+1) (unriffle ⨾ mergeB n)         -- merger exchange in periodic passes
  = sortV (n+1)                              -- vfly_eq
```

- `sortB_succ`, `qfly_eq` and `vfly_eq` are wiring laws: they hold for *any*
  symmetric cell.
  - `qfly_eq` and `vfly_eq` are themselves `calc` derivations (`que_step`,
    `vee_step`) using the wiring laws W3, W4, W5 and "a butterfly ignores a
    reversal" ([Ruby/Sorting/Laws.lean](Ruby/Sorting/Laws.lean)).
  - All four mergers are instances of one schema, `fly P L`
    ([Ruby/Sorting/Refinement.lean](Ruby/Sorting/Refinement.lean)).
- The merging laws hold for the comparator:
  - `merge_exchange`: the two mergers agree on inputs whose halves are sorted.
  - `periodicOE_sorts`, `periodicB_sorts`: `n + 1` passes of
    `unriffle ⨾ merge` sort with either merger, since each pass halves the
    period of a `k`-sorted vector.
- `sorter_refinement` assembles the three steps. `four_sorters_sort` carries
  `sortB_sorts` along the chain to all four cores.
- `que_ilv` proves the paper's own lemma, `que (ilv f) = ilv (ilv f)`, by the
  same wiring laws. `bfly_hrep_counterexample` is the paper's counterexample:
  without the `unriffle`, two bitonic mergers in series leave
  `[0, 1, 0, 1]` unsorted.

**The hardware sorts** ([Ruby/Sorter](Ruby/Sorter)):

- `eval_geC`: the `CARRY4` chain computes `a ≥ b` on `4k`-bit words.
  `twoSorter_commutes`: decoded, the cell is the comparator.
- `bitonicSorter_sorts` and the other three: the circuits of Xilinx
  primitives sort.
- `bitonicSorter_latency`, …: every path carries `n(n+1)/2` registers
  (recursive sorters) or `n²` (periodic sorters).
- `bitonicSorter_pipelined`, …: as synchronous circuits, the words leaving at
  cycle `t + latency` are the words that entered at cycle `t`, sorted.

**The layout** ([Ruby/Layout.lean](Ruby/Layout.lean),
[Ruby/Sorter/Layout.lean](Ruby/Sorter/Layout.lean),
[Ruby/NetlistLayout.lean](Ruby/NetlistLayout.lean)):

- `sites_inBox`, `nodup_sites`: for every circuit, each occupied site lies in
  the bounding box. No site is used twice if overlaid parts use different
  kinds of resource.
- `size_bitonicSorter`, `size_oddEvenSorter`, `size_balancedSorter`,
  `size_periodicSorter`: each sorter is a rectangle of cells.
- `nodup_*Sorter`: no resource of any sorter is used twice.
- `bitonicSorter_dense`, `balancedSorter_dense`: every LUT site in the
  bounding box is occupied.
- `Circuit.gen_sites`: the netlist instances, and so the emitted `RLOC`/`BEL`
  attributes, occupy exactly the sites of the layout semantics.

**The netlist computes the verified function**
([Ruby/NetlistSemantics.lean](Ruby/NetlistSemantics.lean)):

- The instance list has an execution semantics. A LUT applies its function, a
  `CARRY4` follows the UNISIM equations, and a register passes its input, as
  in one cycle of `Circuit.eval`.
- `Circuit.gen_eval` and `Circuit.netlist_correct`: executing the emitted
  instances in order gives every output net the value that `Circuit.eval`
  gives. The wiring cases follow from the naturality of wiring.

## Layout

Coordinates count slice columns (`x`) and LUT rows (`y`), four rows to a
slice. A LUT or flip-flop at row `y` gets `RLOC` row `y / 4` and BEL letter
`A`–`D` from `y % 4`.

- The cell is 2 slices wide and `2(k+1)` slices high.
- A butterfly of degree `n` is `n` columns of `2^(n-1)` cells: the FFT
  butterfly layout. The `riffle`/`unriffle` wiring between columns takes no
  area.
- A recursive sorter of `2^n` words is `tri(n) = n(n+1)/2` such columns side
  by side. A periodic sorter is `n²` columns.

Sizes for 4-bit words, in slices (columns × rows):

| words | bitonic / odd–even | balanced / periodic | latency (recursive / periodic) |
|---:|---:|---:|---:|
| 4 | 6 × 4 | 8 × 4 | 3 / 4 |
| 8 | 12 × 8 | 18 × 8 | 6 / 9 |
| 16 | 20 × 16 | 32 × 16 | 10 / 16 |
| 32 | 30 × 32 | 50 × 32 | 15 / 25 |
| 64 | 42 × 64 | 72 × 64 | 21 / 36 |
| 128 | 56 × 128 | 98 × 128 | 28 / 49 |

## Building, simulating and implementing

```console
$ make lean      # lake build: every definition and proof
$ make test      # lake test: structural checks of the SystemVerilog emitter
$ make sv        # SystemVerilog, testbenches and designs.tsv in build/sv (and LOC variants in build/sv_loc)
$ make sim       # xsim against the Xilinx UNISIM models
$ make verilate  # Verilator against behavioural models of the primitives, no Vivado needed
$ make impl      # Vivado place and route, and a placement check
```

- `make sim` needs Vivado's `xvlog`/`xelab`/`xsim` on the `PATH`. Each
  generated testbench drives random and corner-case words every cycle. It
  checks the outputs `latency` cycles later against a sort written in
  SystemVerilog. The random words are seeded with `+seed=<n>` (default 1, or
  `make sim SEED=<n>`), and a failure reports its seed.
- `make verilate` runs the testbenches of the `SIM_DESIGNS` with Verilator against
  behavioural models of `LUT1`–`LUT6`, `CARRY4` and `FDCE`
  ([sim/unisim_models.sv](sim/unisim_models.sv)). It is quicker and needs no
  Vivado, but `make sim` against the real UNISIM library remains the reference.
- CI ([.github/workflows/lean.yml](.github/workflows/lean.yml)) runs
  `lake build`, `lake test`, `ruby-sv` (all 36 designs, both placements) and
  `make verilate` (the `SIM_DESIGNS`, relatively placed) on every push and pull
  request. [sim/selftest.sh](sim/selftest.sh) also checks that a deliberately
  broken sorter fails its testbench and that seeds are reproducible.
  `make sim` and `make impl` need Vivado and are not run in CI.
- `make impl` implements out of context on an `xc7a200tsbg484-1` at 250 MHz
  ([vivado/implement.tcl](vivado/implement.tcl)). It then compares every
  cell's placed site and BEL with the `RLOC`/`BEL` emitted from the Lean
  layout ([vivado/check_placement.py](vivado/check_placement.py)).
- Each relocatable macro is anchored with `place_cell` at slice `X36Y50`
  (`ORIGIN`). On the xc7a200t the slices from `X36Y50` to `X133Y177` contain
  no holes, which is room for every sorter up to 128 words of 4 bits.
  [vivado/find_origin.py](vivado/find_origin.py) finds such an origin for
  other parts and sizes. Without an anchor, Vivado's search for a legal macro
  origin takes tens of minutes for macros wider than about 40 slices.
- For the largest macros, Vivado's shape builder stalls even with an anchor.
  `ruby-sv OUTDIR --loc X36Y50` emits the same layout with absolute `LOC`s at
  that origin instead of `RLOC`s. `make impl` uses this for the 64-word
  periodic sorters and all 128-word sorters.

## Results

### Simulation

`make sim`: every simulated design sorts with exactly its proved latency. The
designs cover all four families at 2–32 words of 4 bits, 8 words of 8 bits and
4 words of 16 bits, each with 200 vectors.

### Implementation (Vivado 2026.1, xc7a200t-1, 4 ns clock, out of context)

`make impl` reproduces this table (`vivado/report.py`):

| design | words × bits | latency | cells | slices used | bounding box | worst slack | f<sub>max</sub> | layout |
|---|---|---:|---:|---:|---:|---:|---:|---|
| bitonic4x4 | 4 × 4 | 3 | 156 | 24 (full) | 6 × 4 | +0.953 ns | 328 MHz | honoured |
| bitonic8x4 | 8 × 4 | 6 | 624 | 96 (full) | 12 × 8 | +0.809 ns | 313 MHz | honoured |
| bitonic16x4 | 16 × 4 | 10 | 2080 | 320 (full) | 20 × 16 | +0.677 ns | 301 MHz | honoured |
| oddeven16x4 | 16 × 4 | 10 | 1774 | 286 | 20 × 16 | +0.695 ns | 303 MHz | honoured |
| balanced16x4 | 16 × 4 | 16 | 3328 | 512 (full) | 32 × 16 | +0.597 ns | 294 MHz | honoured |
| periodic16x4 | 16 × 4 | 16 | 2824 | 456 | 32 × 16 | +0.646 ns | 298 MHz | honoured |
| bitonic32x4 | 32 × 4 | 15 | 6240 | 960 (full) | 30 × 32 | +0.277 ns | 269 MHz | honoured |
| oddeven32x4 | 32 × 4 | 15 | 5358 | 862 | 30 × 32 | +0.411 ns | 279 MHz | honoured |
| balanced32x4 | 32 × 4 | 25 | 10400 | 1600 (full) | 50 × 32 | +0.243 ns | 266 MHz | honoured |
| periodic32x4 | 32 × 4 | 25 | 9050 | 1450 | 50 × 32 | +0.469 ns | 283 MHz | honoured |
| bitonic64x4 | 64 × 4 | 21 | 17472 | 2688 (full) | 42 × 64 | -0.229 ns | 236 MHz | honoured |
| oddeven64x4 | 64 × 4 | 21 | 15150 | 2430 | 42 × 64 | -0.164 ns | 240 MHz | honoured |
| balanced64x4 | 64 × 4 | 36 | 29952 | 4608 (full) | 72 × 64 | -0.332 ns | 231 MHz | honoured |
| periodic64x4 | 64 × 4 | 36 | 26604 | 4236 | 72 × 64 | -0.100 ns | 244 MHz | honoured |
| bitonic128x4 | 128 × 4 | 28 | 46592 | 7168 (full) | 56 × 128 | -1.478 ns | 183 MHz | honoured |
| oddeven128x4 | 128 × 4 | 28 | 40814 | 6526 | 56 × 128 | -1.307 ns | 188 MHz | honoured |
| balanced128x4 | 128 × 4 | 49 | 81536 | 12544 (full) | 98 × 128 | -1.594 ns | 179 MHz | honoured |
| periodic128x4 | 128 × 4 | 49 | 73598 | 11662 | 98 × 128 | -1.273 ns | 190 MHz | honoured |
| bitonic8x8 | 8 × 8 | 6 | 1248 | 192 (full) | 12 × 16 | +0.483 ns | 284 MHz | honoured |

- **Layout.** "Honoured" means every cell sits at one common offset from its
  `RLOC` (or exactly on its `LOC`) and on its requested BEL. "(full)" marks
  designs that use every slice of their bounding box. These are the bitonic
  and balanced sorters, as the density theorems predict. The odd–even and
  Canfield–Williamson sorters leave the second column empty beside the
  one-slice delay words.
- **Timing.** Up to 32 words, every sorter meets 250 MHz. Beyond that the
  critical path is the longest butterfly wire. Some merger stage must bring
  together words `N/2` apart, a route across about `N/4` cells of a column.
  This is inherent to the butterfly in a one-dimensional column of cells; at
  64 words it costs about 0.2 ns, at 128 words about 1.4 ns.
- **Runtime.** With the anchor (or absolute `LOC`s), each design takes
  minutes: under five minutes for the largest (81,536 primitives).

## Limitations

- **Unverified text emission.** The netlist is connected to the behaviour
  (`Circuit.netlist_correct`) and to the layout (`Circuit.gen_sites`). The
  final rendering of instances as SystemVerilog text (`Inst.toSV`) is not
  verified; simulation of the generated code against the UNISIM models checks
  it.
- **Timed netlist semantics.** `Circuit.netlist_correct` reads registers as
  transparent, which is one cycle of `Circuit.eval`. The timed behaviour is
  proved for the circuit term (`Circuit.evalS_sample`) and checked for the
  netlist by simulation.
- **Reset.** The stream semantics gives every register the value `0` at cycle
  `0` and has no reset input. This matches the circuits after their
  asynchronous clear. The pipeline theorems only concern cycles from `latency`
  on, so they do not depend on initial values.
- **256 words.** A 256-word bitonic sorter of 4-bit words is a 72 × 256 slice
  rectangle. That is taller than the 250 slice rows of an xc7a200t (or an
  xc7k160t). Folded into two side-by-side halves it would be 144 × 128, wider
  than the largest hole-free region of 128 rows on the xc7a200t (98 × 128). It
  needs a taller part, or a layout split into several macros around the
  device's hard blocks. A fold would need a side-by-side variant of `‖`;
  `eval` ignores geometry, so the proofs of behaviour would not change.
