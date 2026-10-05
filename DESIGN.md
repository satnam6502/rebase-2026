# How ruby-lean was produced

[README.md](README.md) describes what this repository contains. This document
covers how and why it came to be that way:

- the brief, and how it changed;
- the prior work consulted;
- the order of the work;
- the design decisions and the alternatives rejected;
- the problems met along the way and how they were fixed;
- how the result was checked.

## Contents

1. [Provenance](#1-provenance)
2. [The brief and how it evolved](#2-the-brief-and-how-it-evolved)
3. [Prior work and what was taken from it](#3-prior-work-and-what-was-taken-from-it)
4. [Design decisions](#4-design-decisions)
5. [Order of the work](#5-order-of-the-work)
6. [Proof strategy](#6-proof-strategy)
7. [The Bird–Meertens refinement, in two iterations](#7-the-birdmeertens-refinement-in-two-iterations)
8. [Problems met and how they were fixed](#8-problems-met-and-how-they-were-fixed)
9. [How the result was checked](#9-how-the-result-was-checked)
10. [Trust base](#10-trust-base)
11. [Module map](#11-module-map)
12. [Open directions](#12-open-directions)

## 1. Provenance

- **Author.** The code, proofs, scripts and documentation were written by
  Claude Code, Anthropic's coding agent, running a Claude Opus model. The work
  was one long interactive session, carried across several context
  compactions.
- **Direction.** The project owner set the brief and changed direction at
  several points (section 2). Nothing was copied from the earlier projects;
  they were read for ideas and lessons only.
- **Tools.** Lean `v4.34.1`, Mathlib `v4.34.1`, and Vivado 2026.1 (`xsim` and
  out-of-context implementation) on an `xc7a200tsbg484-1`.
- **Version control.** Nothing was committed during the session. The files are
  staged for the owner to review. One commit was made without being asked for;
  it was undone at once (`git update-ref -d HEAD`), leaving the files staged.

Size of the result:

- about 5,400 lines across 25 Lean files (including the executable) and the build, simulation and Vivado scripts;
- about 360 theorems;
- 36 generated designs;
- 25 designs simulated and 19 implemented in Vivado.

## 2. The brief and how it evolved

| # | Request (paraphrased) | Effect on the work |
|---|---|---|
| 1 | Port the Batcher sorter designs and FPGA layouts of `../xilinx-lava` to a Ruby-style hardware DSL in Lean, in the style of `../lhdl`. The DSL must (1) emit SystemVerilog for Vivado, (2) support formal theorems via a semantic interpretation of the circuits, and (3) produce good layouts as well as correct behaviour. Learn from earlier experiments. Re-implement the sorters with compact FFT-style butterfly layouts, and prove they sort for every degree. | Set the overall architecture (section 4): one circuit term, with behaviour, latency, layout and netlist as interpretations of it, and degree-generic proofs from the start. |
| 2 | Use Mathlib and the latest Lean, with no dependency on `../lhdl`. | Pinned the newest stable Lean tag and the matching Mathlib tag. The project imports nothing from `lhdl`. |
| 3 | Also take inspiration from the Batcher sorter and proofs in `../alt-lhdl`. | Its fixed-size proofs, typeclass DSL and latency theorems were studied. The lessons are recorded in the README table and in section 3. |
| 4 | Use `~/rtl/experiments/bird-meertens/BirdMeertens/Sorters.lean` as inspiration for four sorter types, each related to the next by Bird–Meertens stepwise refinement. | Added the balanced and periodic sorters, the wiring laws, and the shared `fly` schema. The first version of the refinement went through a common specification. The request was then sent again, and that version was replaced by a genuine stepwise chain (section 7). |

Two standing constraints applied throughout:

- commit only when asked;
- prefer proofs quantified over every size to checks at fixed sizes.

## 3. Prior work and what was taken from it

**`../xilinx-lava` (Haskell Lava, tagless final)**
- *Taken:*
  - the four sorter families, as Lava descriptions of Batcher's networks;
  - the pipelined two-sorter cell: a `CARRY4` comparator column (`X0`) next to a column of `LUT3` muxes with `FDCE`s (`X1`);
  - the layout combinators `>->` (beside) and `>|>` (overlay).
- *Changed:* Lava rebuilt the layout tree by popping blocks off a stack as the
  netlist grew. Wiring therefore had no layout meaning, and the layout could
  not be reasoned about. Here layout is a structural interpretation of the
  circuit term.

**`../lhdl` and `../alt-lhdl` (Lean, monadic typeclass DSL)**
- *Taken:* the principle that one description should have several semantics.
- *Changed:*
  - The Batcher proofs there were for 4 and 8 inputs, found by unfolding and
    search. Here every proof is by induction on the degree.
  - Their latency theorems evaluated a separately defined number. Here latency
    is computed from the circuit and connected to its stream semantics.
  - `List.Vector` with `▸` casts became `Fin n → α`, with lengths written `m * 2`.

**`rtl/docs/v2l_backends/Ruby.lean`**
- Its general merger theorem was left as `sorry`. This confirmed that the
  degree-generic proof needs a different route: the zero–one principle plus
  `k`-sortedness, not unfolding.

**Bird–Meertens `Sorters.lean` (lists)**
- *Taken:*
  - the four cores: bitonic, odd–even, balanced (Dowd et al.) and periodic
    (Canfield–Williamson);
  - the wiring laws relating them, and the single `fly` schema for their mergers;
  - the lemma `que (ilv f) = ilv (ilv f)`;
  - the counterexample showing why the `unriffle` is needed.
- *Changed:* its checks were at 4 and 8 inputs. Here the laws are proved over
  `Fin` vectors at every size, and the derivation is a chain of `calc` steps.

## 4. Design decisions

### 4.1 A deep embedding

**Choice.** `inductive Circuit : Shape → Shape → Type 1` has constructors
`prim`, `wire`, `seq (d : Dir)`, `par` and `map` ([Ruby/Core.lean](Ruby/Core.lean)).
Every interpretation is a structural recursion over the term.

**Alternatives rejected:**
- Lava's tagless-final style.
- `lhdl`'s monadic typeclass.

Both make it easy to add interpretations, but hard to prove theorems that
relate two of them.

With a deep embedding, the relations between interpretations are theorems by
induction on the term:
- `evalS_sample`: stream behaviour against combinational behaviour;
- `gen_eval`: the netlist against behaviour;
- `gen_sites`: the netlist against the layout.

**Cost.** `Circuit` lives in `Type 1`, and the recursive definitions must bind
their shape indices after the colon (section 8).

### 4.2 Shapes and vectors

- `Shape` is `bit | pair | vec n`. `Shape.Val β` interprets a shape with wires
  of type `β`: `Bool` for behaviour, `Nat → Bool` for streams, `Net` for netlists.
- Vectors are functions `Fin n → α`. Indexing reduces by computation, and
  `funext` gives equality of vectors.
- Every recursive network has length `m * 2`. Then `2 ^ (n + 1)` is
  *definitionally* `2 ^ n * 2`, and the recursive definitions need no casts.

### 4.3 Wiring is polymorphic in the wire type

- `Wiring a b` contains `run : {β} → (Bool → β) → a.Val β → b.Val β`. The
  argument `Bool → β` lets wiring tie a wire to a constant.
- Wiring also carries a proof `natural`: it commutes with every change of wire
  type. For all wiring in the library this is discharged by `rfl`, or by a case
  split.
- Since it cannot inspect wires, wiring can only route, copy, drop or tie off.

One definition therefore serves every interpretation:
- no instances in the netlist;
- no area in the layout;
- reindexing in the semantics.

Naturality is also the key lemma in two places:
- the retiming theorem;
- the netlist proof (`allBelow_wire`).

### 4.4 Layout direction on serial composition

- `seq` takes a direction:
  - `>->` places `s` beside `r`;
  - `>^>` places `s` above `r`;
  - `>|>` places `s` on top of `r`.
- `>->` and `>|>` come from Lava. `>^>` was added for carry chains.
- `par r s` places `r` below `s`, and `map n r` stacks `n` copies bottom to top.

The butterfly's geometry then falls out of the combinators:
- a column of cells per merger stage;
- `riffle`/`unriffle` wiring between columns, taking no area;
- stages side by side.

### 4.5 Primitives follow the UNISIM models

There are three primitives:
- `lut k f`;
- `carry4`, defined by `carryChain` from the equations in Vivado's `CARRY4.v`;
- `fdce`.

Because the proofs use the same equations as the simulation models, simulating
the emitted SystemVerilog against UNISIM checks the one unverified step: the
text rendering.

### 4.6 Two levels: networks and circuits

Sorting is proved on *function-level networks* over any linear order
(`Ruby.Vec`, [Ruby/Sorting](Ruby/Sorting)). The hardware is connected to them
in two steps:

1. The circuit combinators evaluate to the networks (`eval_sortB`, …).
2. The decoded hardware cell equals the comparator `cmp` (`twoSorter_commutes`).

The sorting proofs never see bits, and the cell proofs never see networks.

### 4.7 Layout semantics

- **Coordinates.** `x` counts slice columns and `y` counts LUT rows, four rows
  to a slice. A row maps to an `RLOC` row (`y / 4`) and a BEL letter (`y % 4`).
- **Interpretations.** `size`, `sites` and `kinds` compute the bounding box,
  the occupied sites and the kind of resource used at each site.
- **`NoOverlap`.** Overlap is checked per kind of resource. A LUT overlaid with
  its flip-flop, or with a `CARRY4`, is legal; two LUTs at one site are not.

### 4.8 Netlist generation

- `Circuit.gen` runs in a state monad.
  - It allocates fresh nets.
  - It emits LUT, `CARRY4` and `FDCE` instances in topological order.
  - It attaches `RLOC`, `BEL` and `DONT_TOUCH` attributes taken from the layout.
- Absolute `LOC` placement (`Placement.absolute`) was added later, for the
  macros that Vivado's shape builder could not handle (section 8).

## 5. Order of the work

Roughly in this order:

1. **Survey.** Read the earlier projects listed in section 3, and recorded what
   to keep and what to change.
2. **DSL core.** Wrote `Shape`, `Wiring`, `Prim`, `Circuit` and `eval`. Fixed
   the `m * 2` length convention early, because every later proof depends on it.
3. **Network combinators** ([Ruby/Vec.lean](Ruby/Vec.lean)). Wrote `riffle`,
   `unriffle`, `two`, `parl`, `ilv`, `evens`, `midEvens`, `alt`, `rev`, `vee`,
   `que` and `hrep`, with `⨾` for composition. Added the naturality lemmas
   (`Commutes`) for every combinator.
4. **Sorting networks and their proofs.**
   - The bitonic and odd–even sorters, via the zero–one principle.
   - The periodic sorters, via `k`-sortedness.
5. **Circuit combinators** ([Ruby/Combinators.lean](Ruby/Combinators.lean)).
   Wrote the circuit versions of the networks, parameterised by a cell and a
   delay, and the lemmas that their `eval` is the network.
6. **The hardware cell** ([Ruby/Sorter](Ruby/Sorter)).
   - Wrote `geTile`, `geC = col k geTile`, `muxReg`, `halfMin`, `halfMax`,
     `twoSorter` and `delayW`.
   - Proved the carry-chain comparator correct for every width.
7. **Latency and streams.**
   - Wrote `latency` and `evalS`.
   - Proved the retiming theorem `evalS_sample`.
   - Derived the pipeline theorems `*Sorter_pipelined`.
8. **Layout** ([Ruby/Layout.lean](Ruby/Layout.lean),
   [Ruby/Sorter/Layout.lean](Ruby/Sorter/Layout.lean)). Proved containment,
   absence of overlaps, the exact size of each sorter and density.
9. **Netlist and SystemVerilog.**
   - Wrote `gen`, `toSystemVerilog` and the self-checking testbench generator.
   - Wrote the `ruby-sv` executable and the `Makefile`.
10. **Simulation.** Ran `xsim` against UNISIM, using the scripts in [sim](sim).
11. **Implementation.** Ran Vivado place and route and checked every placed
    cell against the Lean layout (scripts in [vivado](vivado)).
12. **Closing the gaps between interpretations.**
    - [Ruby/NetlistLayout.lean](Ruby/NetlistLayout.lean): the emitted
      instances occupy exactly the layout's sites.
    - [Ruby/NetlistSemantics.lean](Ruby/NetlistSemantics.lean): executing the
      emitted instances computes `eval`.
13. **Bird–Meertens refinement.** Two iterations, described in section 7.
14. **Tidying.**
    - Removed every lint warning.
    - Wrote [Ruby/Summary.lean](Ruby/Summary.lean), which restates the headline
      theorems as checked `example`s.
    - Wrote the README.

## 6. Proof strategy

### 6.1 The networks sort, at every degree

- **Zero–one principle** (`zero_one`).
  - A network that commutes with every monotone map (`Commutes g F F'`) and
    sorts every bit vector sorts every vector.
  - Commutation is proved once per combinator. Commutation for each network
    then follows by composition.
- **Permutation** (`IsPerm`).
  - A network of compare–exchange cells permutes its input. This is proved via
    `List.Perm` and involutive conditional swaps.
  - "Sorts" means the output is `mergeSort` of the input (`Sorts`, `sorts_of`).
- **Bitonic merger.**
  - The butterfly sorts every bit vector whose ones form a single segment
    (`ind p q`, `bfly_ind`).
  - With sorted halves, the reversal in `sortB` makes the input such a segment.
    `sortB_sorts` follows by induction.
- **Odd–even merger.** `mergeOE_ind`: the merger merges two sorted halves of
  bits. `sortOE_sorts` follows by induction.
- **Periodic sorters.**
  - `KSorted k v` means `v i ≤ v (i + k)` for every `i`.
  - One pass of `unriffle ⨾ merge` takes a `2k`-sorted vector to a `k`-sorted
    one (`unriffle_mergeB_pass`, `unriffle_mergeOE_pass`).
  - So `n + 1` passes sort `2 ^ (n + 1)` wires (`periodicB_sorts`,
    `periodicOE_sorts`).
- **Wiring laws** (W3, W4 and W5 in [Ruby/Sorting/Laws.lean](Ruby/Sorting/Laws.lean)).
  - Each law is proved by splitting a vector into four quarters (`quad P Q R S`)
    and computing both sides.
  - These laws hold for any cell, and give the merger identities `qfly_eq` and
    `vfly_eq`.

### 6.2 The hardware sorts

- **The comparator.** `carryChain_ge` shows that the `CARRY4` chain, with
  `S = a XNOR b` and `DI = a`, computes `a ≥ b`. Induction over the chain
  (`carry_step`, `carryChain_shift`) extends this to `k` slices (`col_geTile`,
  `eval_geC`).
- **The muxes.** `eval_muxReg` shows that the mux column selects the minimum or
  maximum word.
- **The cell.** `twoSorter_commutes`: decoded, the cell is `cmp`.
- **The whole sorter.** `*Sorter_sorts` combines the cell with `eval_sortB` and
  the network theorems.
- **Latency.** `*Sorter_latency`: every path carries `tri n` or `n²` registers.
  The middle wires of the odd–even and periodic patterns pass through `delayW`,
  which keeps every path the same length.
- **Pipelining.** `*Sorter_pipelined` follows from the latency theorem and
  `evalS_sample`.

### 6.3 Layout and netlist

**Layout.**
- `sites_inBox` and `nodup_sites` hold for every circuit, by induction on the
  term.
- `size_*` and `noOverlap_*` compute each sorter's rectangle and rule out
  overlaps.
- The density theorems count LUT sites (`lut_sites_fill`).

**Netlist.**
- `gen_sites` shows that the instances' footprints are the layout's sites.
- `gen_eval` and `netlist_correct` are proved with two invariants:
  - `GenOK`: the generator's state agrees with `eval`;
  - `AllBelow`: every instance reads only nets created before it, so executing
    the instance list in order is well defined.

## 7. The Bird–Meertens refinement, in two iterations

**First iteration.**
- Proved all four cores sort, each independently.
- Proved the wiring laws and the `fly` schema.
- Stated `sorter_refinement` as pairwise equalities, each proved by
  `eq_of_sorts`: two permuting networks that both sort are equal.

The theorem was correct. But it related each core to the specification rather
than to the previous core, so it was not a refinement.

**Second iteration** ([Ruby/Sorting/Derivation.lean](Ruby/Sorting/Derivation.lean)).
Each core is derived from the one before by a `calc` chain whose every step
names its law:

```
sortB (n+1)
  = two (sortB n) ⨾ mergeB n                 -- sortB_succ: the reversal belongs to the merger
  = two (sortB n) ⨾ mergeOE (n+1)            -- merge_exchange on sorted halves
  = two (sortOE n) ⨾ mergeOE (n+1)           -- induction
  = sortOE (n+1)

sortOE (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))    -- the periodic law
  = hrep (n+1) (qfly (n+1))                  -- qfly_eq
  = sortQ (n+1)

sortQ (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))    -- qfly_eq
  = hrep (n+1) (unriffle ⨾ mergeB n)         -- merger exchange in periodic passes
  = sortV (n+1)                              -- vfly_eq
```

Other changes in the same iteration:
- `vee_step` and `que_step` (the inductive steps of `vfly_eq` and `qfly_eq`)
  became `calc` chains, so each wiring law shows by name.
- The periodic laws became the primary results. `sortV_sorts` and
  `sortQ_sorts` are now derived from them.
- `que_ilv` and `bfly_hrep_counterexample` were added from the reference.

**Why two steps still use `eq_of_sorts`.** The two mergers agree only on inputs
whose halves are sorted (`merge_exchange`). Inside a periodic pass the halves
are not sorted, so single passes of the two mergers really differ. The
exchange is valid only for all `n + 1` passes together. That step therefore
rests on both periodic laws: both versions sort, so they are equal. The chain
keeps the two kinds of law apart:
- wiring laws, which hold for any symmetric cell;
- merging laws, which hold for the comparator.

## 8. Problems met and how they were fixed

### 8.1 Lean and Mathlib

| Problem | Fix |
|---|---|
| Recursive definitions over `Circuit` failed with the shape indices bound by `variable {a b}`. | Bind them after the colon: `def eval : {a b : Shape} → Circuit a b → …`. |
| `latency`, written with `do` over `Option`, resisted `simp`. | Rewrite it with an explicit `match`. |
| `2 ^ (n + 1)` and `2 ^ n * 2` are defeq but not syntactically equal, which broke `rw`, `simpa` and `calc`. | Several fixes, depending on the case: `exact` or `Eq.trans` instead of `rw`; `erw`; generic-size lemmas (`vee_step`, `que_step` and `mergeB_split` take any `k * 2`); explicit implicit arguments; type ascriptions on each `calc` line, closed by `rfl` or `exact`. |
| After `split_ifs`, `omega` dropped hypotheses of the form `False ∨ …`. | Add a `fin_omega` macro that simplifies `false_or` and then calls `omega`. |
| `min` was displayed as `⊓`, which `omega` cannot use. | Clamp indices with an explicit `if`. |
| A non-dependent `if` lost the hypothesis needed to prove an index in bounds. | Use `if h : …`. |
| `congr 1` sometimes closed goals itself, leaving later tactics with nothing to do. | Add an `idx_eq` macro for index equalities. |
| Mathlib names had moved. | Use `List.SortedLE`, `sortedLE_ofFn_iff`, `Perm.eq_of_sortedLE` and `List.map_coe_finRange_eq_range` (Batteries). Note that `getElem_finRange` now returns a `Fin.cast`. |
| `geC 0` (a comparator for 0-bit words) outputs `false`, so "the cell compares" fails at width zero. | Assume `0 < k` in the theorems and add `col_geTile_cyinit`. The emitted designs all have `k ≥ 1`. |
| `A \|\| B = C` parsed as `A \|\| (B = C)`. | Parenthesise. |
| In the netlist proofs, projections of structure literals and `StateT.run` did not reduce. | Use `show` with the reduced form, add `setBlock` lemmas, and use `of_decide_eq_true` for the custom decidable instances. |
| Deprecated names (`if_pos`, `dif_neg`), unused `simp` arguments, and `<;>` where `;` was meant. | Fix them all; the build is free of warnings. |

### 8.2 Simulation and Vivado

| Problem | Fix |
|---|---|
| In `xsim`, the first vectors read `0000`: the global set/reset holds the UNISIM registers for 100 ns. | The testbench waits 12 clock edges before checking. |
| `RLOC_ORIGIN` cannot be set after synthesis. A log line from synthesis was at first mistaken for placer progress. | Anchor each macro by `place_cell`-ing one LUT at `SLICE_X36Y50/A6LUT`. `find_origin.py` finds a hole-free origin for other parts. |
| The shape builder stalled on `RLOC` macros of about 56 columns or 128 rows and more (`CRITICAL WARNING [Shape Builder 18-119]`). | Add absolute placement: `ruby-sv OUTDIR --loc X36Y50` emits the same layout as `LOC`s. It is used for the 64-word balanced and periodic sorters and for every 128-word sorter. |
| In `LOC` mode, the placement dump included a reset inverter that synthesis had inserted. | Select only cells with `IS_PRIMITIVE && DONT_TOUCH`, which marks the cells emitted from Lean. |
| `pkill -f` and `pgrep -f` matched the shell running them. | Use bracketed patterns such as `"[t]clargs …"`. |

## 9. How the result was checked

- **Lean.**
  - `lake build` succeeds with no errors and no warnings.
  - A search finds no `sorry` or `admit`, and no `native_decide` is used.
  - `#print axioms` on the headline theorems lists only `propext`,
    `Classical.choice` and `Quot.sound`. These include `sorter_refinement`,
    `bitonicSorter_pipelined` and `periodicSorter_pipelined`.
- **Summary.** [Ruby/Summary.lean](Ruby/Summary.lean) restates the main
  results as `example`s. A reader can check the statements without following
  the proofs.
- **Generation.** `make sv` emits 36 designs: four families at 2 to 128 words
  of 4 bits, 8 words of 8 bits, and 4 words of 16 bits.
- **Simulation.** `make sim` runs 25 designs, each with 200 random and
  corner-case vectors. The designs cover all four families, several widths,
  and the 2-word bitonic sorter. Every design sorts, with exactly its proved
  latency.
- **Implementation.** `make impl` runs Vivado on 19 designs, from 4 to 128
  words.
  - Every cell lies at one common offset from its `RLOC`, or exactly on its
    `LOC`, and on its requested BEL.
  - The bitonic and balanced sorters fill every slice of their bounding box, as
    the density theorems predict.
  - Every design up to 32 words meets 250 MHz.
  - The 64-word designs reach 231–244 MHz and the 128-word designs 179–190 MHz.
    At those sizes the longest butterfly wire limits the clock.
  - The full table is in the README.

## 10. Trust base

**Trusted without proof:**
- the Lean kernel, Mathlib, and the compiler that runs `ruby-sv`;
- the transcription of the UNISIM equations into `Prim.eval`. Simulation
  against the UNISIM models cross-checks it.
- the rendering of instances as SystemVerilog text (`Inst.toSV`). Simulation
  and the placement check cover it.
- Vivado's synthesis, placement and routing.

**Proved:**
- that the instance list computes the verified function (`netlist_correct`);
- that it occupies the proved layout (`gen_sites`).

The step from instance list to text is the remaining gap.

## 11. Module map

In dependency order:

| Module | Contents |
|---|---|
| [Ruby/Shape.lean](Ruby/Shape.lean) | shapes, values, streams |
| [Ruby/Core.lean](Ruby/Core.lean) | `Wiring`, `Prim`, `Circuit`, `eval`, `evalS`, `latency`, `evalS_sample` |
| [Ruby/Vec.lean](Ruby/Vec.lean) | network combinators, `Commutes`, tactic macros |
| [Ruby/Combinators.lean](Ruby/Combinators.lean) | circuit combinators and their `eval` lemmas |
| [Ruby/Latency.lean](Ruby/Latency.lean) | latency of the combinators and sorters |
| [Ruby/Layout.lean](Ruby/Layout.lean) | layout semantics and its general theorems |
| [Ruby/Netlist.lean](Ruby/Netlist.lean), [Ruby/SystemVerilog.lean](Ruby/SystemVerilog.lean) | netlist generation, SystemVerilog, testbenches |
| [Ruby/NetlistLayout.lean](Ruby/NetlistLayout.lean), [Ruby/NetlistSemantics.lean](Ruby/NetlistSemantics.lean) | netlist ↔ layout, netlist ↔ behaviour |
| [Ruby/Sorting/Networks.lean](Ruby/Sorting/Networks.lean) | the four sorting networks and their mergers |
| [Ruby/Sorting/ZeroOne.lean](Ruby/Sorting/ZeroOne.lean) | zero–one principle, permutations, `Sorts` |
| [Ruby/Sorting/Merge.lean](Ruby/Sorting/Merge.lean) | bitonic and odd–even merging |
| [Ruby/Sorting/Laws.lean](Ruby/Sorting/Laws.lean) | wiring laws W3–W5 |
| [Ruby/Sorting/Refinement.lean](Ruby/Sorting/Refinement.lean) | `fly` schema, `vfly_eq`, `qfly_eq` |
| [Ruby/Sorting/Periodic.lean](Ruby/Sorting/Periodic.lean) | `k`-sortedness and the periodic laws |
| [Ruby/Sorting/Derivation.lean](Ruby/Sorting/Derivation.lean) | merging laws and the refinement chain |
| [Ruby/Sorting.lean](Ruby/Sorting.lean) | `sorter_refinement`, `four_sorters_sort` |
| [Ruby/Sorter/Cell.lean](Ruby/Sorter/Cell.lean) | the hardware cell and the four sorter circuits |
| [Ruby/Sorter/CellProof.lean](Ruby/Sorter/CellProof.lean) | the carry-chain comparator and cell |
| [Ruby/Sorter/Correctness.lean](Ruby/Sorter/Correctness.lean) | sorting, latency and pipeline theorems for the hardware |
| [Ruby/Sorter/Layout.lean](Ruby/Sorter/Layout.lean) | size, overlap and density of the sorters |
| [Ruby/Summary.lean](Ruby/Summary.lean) | the headline theorems, restated |
| [Main.lean](Main.lean) | the `ruby-sv` generator |

## 12. Open directions

- **Verified text emission.** Prove `Inst.toSV` correct against a model of the
  relevant SystemVerilog subset.
- **Timed netlist semantics.** Extend `netlist_correct` from one combinational
  cycle to streams, matching `evalS`.
- **Larger sorters.** A 256-word sorter needs a folded layout: a side-by-side
  variant of `‖`, or several macros placed around the device's hard blocks.
  `eval` ignores geometry, so the behavioural proofs would carry over
  unchanged.
- **Timing at 64 words and above.** Lay out the long butterfly stages in two
  dimensions to shorten the longest wire.
