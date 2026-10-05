import Ruby.Shape
import Ruby.Core
import Ruby.Vec
import Ruby.Combinators
import Ruby.Latency
import Ruby.Layout
import Ruby.Netlist
import Ruby.SystemVerilog
import Ruby.NetlistLayout
import Ruby.NetlistSemantics
import Ruby.Sorting
import Ruby.Sorter.Cell
import Ruby.Sorter.CellProof
import Ruby.Sorter.Correctness
import Ruby.Sorter.Layout
import Ruby.Summary

/-!
# ruby-lean

A Ruby-style hardware description language embedded in Lean 4.

Circuits are terms of `Ruby.Circuit`, built from Xilinx 7-series primitives
with the Ruby combinators. Each term has several interpretations, all by
structural recursion:

* behaviour: `Circuit.eval` (one clock cycle) and `Circuit.evalS` (streams),
  related by `Circuit.evalS_sample` through `Circuit.latency`;
* layout: `Circuit.size` and `Circuit.sites`, the relative placement;
* netlists: `Circuit.gen`, emitted as SystemVerilog with `RLOC`/`BEL`
  attributes by `Circuit.toSystemVerilog`.

The case study is Batcher's sorters (`Ruby.Sorter`), proved to sort at every
degree, and four sorter cores related by Bird–Meertens calculation
(`Ruby.Vec.sorter_refinement`).
-/
