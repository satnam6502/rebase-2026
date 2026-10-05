import Ruby

/-!
Write the SystemVerilog of the sorter cores and their testbenches.

`lake exe ruby-sv [OUTDIR] [--loc XnYm]` writes, for each sorter family and
size, the module `<family><words>x<bits>.sv`, a self-checking testbench
`<name>_tb.sv`, and a manifest `designs.tsv` listing each design's words, bits,
latency and size in slices. Placement is a relocatable `RLOC` macro, or with
`--loc XnYm` absolute `LOC`s with the macro origin at slice `XnYm`.
-/

open Ruby Ruby.Sorter Ruby.Circuit

structure Design where
  name : String
  words : Nat
  bits : Nat
  latency : Nat
  sv : SVModule
  slices : Nat × Nat

/-- A design of latency `latency`, which must be the proved latency of `c`, so the
testbench and manifest cannot drift from the circuit. -/
def mkDesign {s : Shape} (p : Placement) (family : String) (k n latency : Nat) (c : Circuit s s)
    (_ : c.latency = some latency) : Design :=
  let name := s!"{family}{2 ^ n}x{k * 4}"
  { name, words := 2 ^ n, bits := k * 4, latency, sv := c.svModule name p,
    slices := (c.size.1, (c.size.2 + 3) / 4) }

def designsFor (p : Placement) (k n : Nat) : List Design :=
  [ mkDesign p "bitonic" k n (tri n) (bitonicSorter k n) (bitonicSorter_latency k n),
    mkDesign p "oddeven" k n (tri n) (oddEvenSorter k n) (oddEvenSorter_latency k n),
    mkDesign p "balanced" k n (n * n) (balancedSorter k n) (balancedSorter_latency k n),
    mkDesign p "periodic" k n (n * n) (periodicSorter k n) (periodicSorter_latency k n) ]

def allDesigns (p : Placement) : List Design :=
  ((List.range 7).map (· + 1)).flatMap (designsFor p 1) ++ designsFor p 2 3 ++ designsFor p 4 2

/-- Parse a slice coordinate `XnYm`. -/
def parseSlice (s : String) : Option (Nat × Nat) := do
  let s ← s.dropPrefix? "X"
  match s.toString.splitOn "Y" with
  | [x, y] => pure (← x.toNat?, ← y.toNat?)
  | _ => none

#guard parseSlice "X36Y50" = some (36, 50)
#guard parseSlice "X0Y0" = some (0, 0)
#guard parseSlice "x36y50" = none
#guard parseSlice "X36" = none
#guard parseSlice "X36Y50Y1" = none
#guard parseSlice "XY50" = none

/-- Parse the command line `[OUTDIR] [--loc XnYm]` into a placement and output
directory, or explain what is wrong with it. -/
def parseArgs : List String → Except String (Placement × System.FilePath)
  | [] => pure (.relative, "build/sv")
  | [dir] =>
      if dir.startsWith "-" then throw s!"unknown option {dir}" else pure (.relative, dir)
  | [dir, "--loc", origin] =>
      if dir.startsWith "-" then throw "OUTDIR is required with --loc"
      else match parseSlice origin with
        | some (x, y) => pure (.absolute x y, dir)
        | none => throw s!"bad slice {origin}: expected XnYm, for example X36Y50"
  | ["--loc", _] => throw "OUTDIR is required with --loc"
  | _ => throw "too many or misplaced arguments"

#guard (parseArgs []).toOption.map (·.2) = some "build/sv"
#guard (parseArgs ["out"]).toOption.map (·.2) = some "out"
#guard (parseArgs ["out", "--loc", "X36Y50"]).toOption.map (·.2) = some "out"
#guard (parseArgs ["out", "--loc", "x36y50"]).toOption.isNone
#guard (parseArgs ["--loc", "X36Y50"]).toOption.isNone
#guard (parseArgs ["--loc"]).toOption.isNone
#guard (parseArgs ["out", "--loc"]).toOption.isNone
#guard (parseArgs ["out", "extra"]).toOption.isNone
#guard (parseArgs ["out", "--loc", "X36Y50", "extra"]).toOption.isNone

def main (args : List String) : IO UInt32 := do
  let (placement, dir) ← match parseArgs args with
    | .ok r => pure r
    | .error e =>
        IO.eprintln s!"ruby-sv: {e}\nusage: ruby-sv [OUTDIR] [--loc XnYm]"
        return 1
  IO.FS.createDirAll dir
  let designs := allDesigns placement
  let mut manifest := "name\twords\tbits\tlatency\tcolumns\trows\n"
  for d in designs do
    IO.FS.writeFile (dir / s!"{d.name}.sv") d.sv.text
    IO.FS.writeFile (dir / s!"{d.name}_tb.sv")
      (sorterTestbench d.name d.words d.bits d.latency 200 d.sv.sequential)
    manifest := manifest ++ s!"{d.name}\t{d.words}\t{d.bits}\t{d.latency}\t{d.slices.1}\t{d.slices.2}\n"
  IO.FS.writeFile (dir / "designs.tsv") manifest
  IO.println s!"wrote {designs.length} designs to {dir}"
  return 0
