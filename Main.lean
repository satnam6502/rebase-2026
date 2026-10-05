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
  sv : String
  slices : Nat × Nat

def mkDesign {s : Shape} (p : Placement) (family : String) (k n latency : Nat) (c : Circuit s s) :
    Design :=
  let name := s!"{family}{2 ^ n}x{k * 4}"
  { name, words := 2 ^ n, bits := k * 4, latency, sv := c.toSystemVerilog name p,
    slices := (c.size.1, (c.size.2 + 3) / 4) }

def designsFor (p : Placement) (k n : Nat) : List Design :=
  [ mkDesign p "bitonic" k n (tri n) (bitonicSorter k n),
    mkDesign p "oddeven" k n (tri n) (oddEvenSorter k n),
    mkDesign p "balanced" k n (n * n) (balancedSorter k n),
    mkDesign p "periodic" k n (n * n) (periodicSorter k n) ]

def allDesigns (p : Placement) : List Design :=
  ((List.range 7).map (· + 1)).flatMap (designsFor p 1) ++ designsFor p 2 3 ++ designsFor p 4 2

/-- Parse a slice coordinate `XnYm`. -/
def parseSlice (s : String) : Option (Nat × Nat) := do
  let s ← s.dropPrefix? "X"
  match s.toString.splitOn "Y" with
  | [x, y] => pure (← x.toNat?, ← y.toNat?)
  | _ => none

def main (args : List String) : IO Unit := do
  let (placement, args) : Placement × List String :=
    match args with
    | dir :: "--loc" :: origin :: _ =>
        match parseSlice origin with
        | some (x, y) => (.absolute x y, [dir])
        | none => (.relative, [dir])
    | _ => (.relative, args)
  let dir : System.FilePath := args.headD "build/sv"
  IO.FS.createDirAll dir
  let mut manifest := "name\twords\tbits\tlatency\tcolumns\trows\n"
  for d in allDesigns placement do
    IO.FS.writeFile (dir / s!"{d.name}.sv") d.sv
    IO.FS.writeFile (dir / s!"{d.name}_tb.sv") (sorterTestbench d.name d.words d.bits d.latency 200)
    manifest := manifest ++ s!"{d.name}\t{d.words}\t{d.bits}\t{d.latency}\t{d.slices.1}\t{d.slices.2}\n"
  IO.FS.writeFile (dir / "designs.tsv") manifest
  IO.println s!"wrote {(allDesigns placement).length} designs to {dir}"
