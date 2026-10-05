import Ruby

/-!
Checks of the SystemVerilog emitter, which the Lean proofs do not cover. Every
`#guard` is checked when this library is built, by `lake test`.
-/

open Ruby Ruby.Sorter Ruby.Circuit

/-- The number of occurrences of `pat` in `s`. -/
def occurrences (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- `bitonic4x4`: a 4-word, 4-bit bitonic sorter of latency 3. -/
def bitonic4x4 : SVModule := (bitonicSorter 1 2).svModule "bitonic4x4"

#guard bitonic4x4.sequential
#guard occurrences bitonic4x4.text "module bitonic4x4 (" == 1
#guard occurrences bitonic4x4.text "input  logic clk" == 1
#guard occurrences bitonic4x4.text "input  logic [3:0] [3:0] a" == 1
#guard occurrences bitonic4x4.text "output logic [3:0] [3:0] b" == 1
#guard occurrences bitonic4x4.text "endmodule : bitonic4x4" == 1
#guard occurrences bitonic4x4.text "156 primitives" == 1
#guard occurrences bitonic4x4.text "RLOC = " == 156
#guard occurrences bitonic4x4.text "LOC = \"SLICE_" == 0

/-- Each word is registered once per cycle of latency, so a sorter of `words`
words of `bits` bits has `latency * words * bits` flip-flops. -/
def registersOk {s : Shape} (c : Circuit s s) (latency words bits : Nat) : Bool :=
  occurrences (c.toSystemVerilog "m") "  FDCE " == latency * words * bits

#guard registersOk (bitonicSorter 1 2) (tri 2) 4 4
#guard registersOk (oddEvenSorter 1 3) (tri 3) 8 4
#guard registersOk (balancedSorter 1 3) (3 * 3) 8 4
#guard registersOk (periodicSorter 2 2) (2 * 2) 4 8

/-- Absolute placement pins every primitive with a `LOC` and no `RLOC`. -/
def bitonic4x4Loc : String := (bitonicSorter 1 2).toSystemVerilog "bitonic4x4" (.absolute 36 50)

#guard occurrences bitonic4x4Loc "LOC = \"SLICE_" == 156
#guard occurrences bitonic4x4Loc "RLOC = " == 0
#guard occurrences bitonic4x4Loc "LOC = \"SLICE_X36Y50\"" > 0

/-- A circuit with no registers has no clock or reset ports, and its testbench
does not connect them. -/
def wires : SVModule := (idC : Circuit (.vec 4 (.vec 4 .bit)) (.vec 4 (.vec 4 .bit))).svModule "wires"

#guard !wires.sequential
#guard occurrences wires.text "clk" == 0
#guard occurrences (sorterTestbench "wires" 4 4 0 200 false) "wires dut (.a(a), .b(b));" == 1
#guard occurrences (sorterTestbench "bitonic4x4" 4 4 3 200)
  "bitonic4x4 dut (.clk(clk), .rstN(rstN), .a(a), .b(b));" == 1
