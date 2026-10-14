# Bird–Meertens derivations in Lean 4

Each file here starts from an obvious specification. It ends at an efficient
program. Every step in between is a proved law, cited in a `calc` block.

| File | Specification | Result | Needs |
|---|---|---|---|
| [`BirdMeertens/Kadane.lean`](BirdMeertens/Kadane.lean) | `maxL ∘ map sum ∘ segs`, O(n³) | Kadane's `foldl`, O(n) | core Lean |
| [`BirdMeertens/CRC.lean`](BirdMeertens/CRC.lean) | remainder of `M·Xᵏ` by `g` | LFSR, then a table | Mathlib |
| [`BirdMeertens/Adder.lean`](BirdMeertens/Adder.lean) | a carry is the overflow of the columns below | Sklansky carry-lookahead adder, log depth | core Lean |
| [`BirdMeertens/Sorters.lean`](BirdMeertens/Sorters.lean) | four sorter cores from one paper | the four, related by equations | core Lean |

## Kadane's algorithm

This follows Bird's maximum segment sum derivation. Wikipedia shows it in its
[Bird–Meertens formalism](https://en.wikipedia.org/wiki/Bird%E2%80%93Meertens_formalism)
article. The source is Bird, *Algebraic Identities for Program Calculation*, 1989, §8.

`mss_eq_kadane` is one `calc` block. Every line is a runnable program. Every
step cites one law.

```
  maxL ∘ map sum ∘ segs                                 O(n³)
= maxL ∘ map sum ∘ concat ∘ map tails ∘ inits           definition of segs
= maxL ∘ concat ∘ map (map sum) ∘ map tails ∘ inits     map promotion
= maxL ∘ map maxL ∘ map (map sum) ∘ map tails ∘ inits   fold promotion
= maxL ∘ map (maxL ∘ map sum ∘ tails) ∘ inits           map distributivity
= maxL ∘ map (foldl (⊙) 0) ∘ inits                      Horner's rule     O(n²)
= maxL ∘ scanl (⊙) 0                                    scan lemma        O(n)
= fst ∘ foldl (⊗) (0, 0)                                fold–scan fusion  O(n)
```

Here `a ⊙ b = max (a + b) 0`. The pair operator is
`(u, v) ⊗ x = (max u w, w)`, where `w = v ⊙ x`.

- Lists hold `Int`. The empty segment counts, so the answer is never negative.
- `maxL` folds `max` from `0`. That makes `0` its unit.
- Laws used mid-pipeline carry a trailing `∘ g`. Then `rw` can find them.

### Each step, on an example

The Wikipedia article draws an example instance of each law. The diagrams
below do the same for every step of `mss_eq_kadane`, on the list `[3, −4, 2]`.
Each applies its law where the derivation applies it. The left path is the
line before the step, and the right path is the line after it. Both end at the
same value. Steps are numbered as in the table of running times, where step 1
is the specification.

Bracket colour shows depth. Blue brackets hold numbers, orange brackets hold
lists of numbers, and green brackets hold lists of those.

[`diagrams/KadaneDiagrams.lean`](diagrams/KadaneDiagrams.lean) draws them. It
computes every value with the definitions in `Kadane.lean`. It fails if the
two paths of a diagram end at different values, or if two pieces of text
overlap. CI redraws the diagrams and checks that they match the committed
files.

```bash
lake exe kadane_diagrams     # redraws the Kadane SVGs in bird-meertens/diagrams
```

#### 2. Definition of `segs`

A segment is a suffix of a prefix. The empty segment is a suffix of every
prefix, so it appears four times.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/segs_dark.svg">
  <img alt="Commuting diagram. From [3, −4, 2], segs gives the ten segments in one step. inits, map tails and concat give the same list in three." src="diagrams/segs_light.svg">
</picture>

#### 3. Map promotion

`map sum` moves inside `concat`. Each prefix's suffixes are summed as a group.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/map_promotion_dark.svg">
  <img alt="Commuting diagram. From the suffixes of each prefix, concat then map sum, and map (map sum) then concat, both give [0, 3, 0, −1, −4, 0, 1, −2, 2, 0]." src="diagrams/map_promotion_light.svg">
</picture>

#### 4. Fold promotion

The largest of all the sums is the largest of each group's largest.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/fold_promotion_dark.svg">
  <img alt="Commuting diagram. From [[0], [3, 0], [−1, −4, 0], [1, −2, 2, 0]], concat then maxL, and map maxL then maxL, both give 3." src="diagrams/fold_promotion_light.svg">
</picture>

#### 5. Map distributivity

Three passes over the prefixes become one. `[0, 3, 0, 2]` holds the largest
suffix sum of each prefix. It comes back in steps 7 and 8.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/map_distrib_dark.svg">
  <img alt="Commuting diagram. From the prefixes of [3, −4, 2], map tails, map (map sum) and map maxL give [0, 3, 0, 2]. One map of the composite gives the same list." src="diagrams/map_distrib_light.svg">
</picture>

#### 6. Horner's rule

The largest suffix sum is a fold from the left. `⊙` drops `3 + −4` to `0`,
and the suffix starts again. The rule takes its name from polynomials: `+`
distributes over `max` as `·` distributes over `+`. The diagram shows the last
prefix. The derivation applies the rule to every prefix, under `map`. The cost
drops from O(n³) to O(n²).

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/horner_dark.svg">
  <img alt="Commuting diagram. From [3, −4, 2], tails, map sum and maxL give 2. foldl (⊙) 0 gives ((0 ⊙ 3) ⊙ −4) ⊙ 2, which is also 2." src="diagrams/horner_light.svg">
</picture>

#### 7. Scan lemma

The left path folds each prefix from scratch. The right path shares the work:
each element is one `⊙` on from the one before. Both paths write out the same
terms, so the lemma holds for any operator. The cost drops from O(n²) to O(n).

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/scan_lemma_dark.svg">
  <img alt="Commuting diagram. From [3, −4, 2], inits then map (foldl (⊙) 0), and scanl (⊙) 0, both give [0, 0 ⊙ 3, (0 ⊙ 3) ⊙ −4, ((0 ⊙ 3) ⊙ −4) ⊙ 2], which is [0, 3, 0, 2]." src="diagrams/scan_lemma_light.svg">
</picture>

#### 8. Fold–scan fusion

The fold carries a pair. Its second component follows the scan, and its first
keeps the largest so far: `(0, 0)`, `(3, 3)`, `(3, 0)`, `(3, 2)`. So `fst`
gives what `maxL` gives, and no list is built.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/fold_scan_fusion_dark.svg">
  <img alt="Commuting diagram. From [3, −4, 2], scanl (⊙) 0 then maxL gives 3. foldl (⊗) (0, 0) gives (3, 2), and fst gives 3." src="diagrams/fold_scan_fusion_light.svg">
</picture>

### Running times

[`bench/KadaneBench.lean`](bench/KadaneBench.lean) runs every line of the
`calc` block. It times each line on random lists of growing length.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="bench/kadane_timings_dark.svg">
  <img alt="Log–log plot of running time against list length for the eight lines of the Kadane derivation. Steps 1 to 5 rise with slope 3, Horner's rule with slope 2, and the last two lines with slope 1." src="bench/kadane_timings_light.svg">
</picture>

Both axes are logarithmic. A program that costs `c·nᵏ` is then a straight line
of slope `k`. The derivation's three complexity classes show up as three slopes.

- Steps 1–5 lie on top of each other. Their four laws leave the cost unchanged.
- Horner's rule drops a factor of `n`. The scan lemma drops another.
- Fold–scan fusion stays O(n) but runs about 7 times faster. It builds no intermediate list.
- At n = 512 the specification takes 271 ms. The last line takes 2.4 µs, about 110,000 times faster.

| Step | Law | Bird's cost | Measured slope | n = 512 | Largest n | Time there |
|---|---|---|---|---|---|---|
| 1 | specification | O(n³) | 3.10 | 271 ms | 724 | 807 ms |
| 2 | definition of segs | O(n³) | 3.10 | 270 ms | 724 | 807 ms |
| 3 | map promotion | O(n³) | 3.09 | 268 ms | 724 | 803 ms |
| 4 | fold promotion | O(n³) | 3.12 | 266 ms | 724 | 799 ms |
| 5 | map distributivity | O(n³) | 3.13 | 265 ms | 724 | 796 ms |
| 6 | Horner's rule | O(n²) | 2.10 | 3.39 ms | 5,793 | 611 ms |
| 7 | scan lemma | O(n) | 0.99 | 16.5 µs | 131,072 | 4.39 ms |
| 8 | fold–scan fusion | O(n) | 1.02 | 2.42 µs | 131,072 | 661 µs |

The slopes of the first six lines sit a little above 3 and 2. `inits` keeps
all `n²/2` prefix cells alive. Memory traffic then likely grows faster than the
operation count.

`lines_eq_mss` proves that every timed program equals `mss`. Its proof replays
the laws, so the benchmark cannot time a mistyped line. Each run also checks
that all eight lines agree on every input.

Each point is the fastest of three batches. A batch repeats the call until it
lasts at least 20 ms. A line stops after its first call over 500 ms. A slope is
a least-squares fit of `log t` on `log n`, over calls of 100 µs or more.

These numbers come from one run on an Intel Xeon at 2.60 GHz, a GCP VM, with
Lean 4.28.0, before these examples moved to Lean 4.34.1. Absolute times vary
by machine. The slopes should change little.

```bash
lake exe kadane_bench        # about 40 seconds
lake exe kadane_bench 50     # stop each line at 50 ms instead
```

Run it from the repository root. It writes every measurement to
[`bench/kadane_timings.csv`](bench/kadane_timings.csv), then redraws both SVGs.

## A CRC

The textbook CRC is algebra. Read the message bits as a polynomial `M` over
GF(2). The CRC is the remainder of `M·Xᵏ` divided by a generator `g`.
Hardware never divides. It clocks bits through a `k`-bit shift register.

`crc_eq_lfsr` derives that register, for every generator. The right column is
the state each line keeps while it streams the message.

```
  (· %ₘ g) ∘ (· * Xᵏ) ∘ msgPoly                                    whole message
= (· %ₘ g) ∘ (· * Xᵏ) ∘ foldl horner 0   Horner's rule             n coefficients
= (· %ₘ g) ∘ foldl hornerShift 0         fold fusion: shift        n + k
= foldl hornerMod 0                      fold fusion: reduction    k
= toPoly ∘ foldl lfsrStep 0              fold fusion: refinement   k bits
```

`crcBytes_eq_table` goes on to Sarwate's table, one lookup per byte, for any
width `k ≥ 8`.

```
  crc ∘ flatten ∘ map bitsOf
= toPoly ∘ foldl lfsrStep 0 ∘ flatten ∘ map bitsOf    the derivation above
= toPoly ∘ foldl (foldl lfsrStep) 0 ∘ map bitsOf      fold over concatenation
= toPoly ∘ foldl byteStep 0                           fold–map fusion
= toPoly ∘ foldl tableStep 0                          Sarwate's table
```

The table step holds because reduction modulo `g` is linear. Its proof is a
short `calc` in `byteStep_eq_tableStep`.

The file also connects the derivation to this repo and to the CRC catalogue.

| Theorem | Says | Proved by |
|---|---|---|
| `crc8Next_eq_lfsrStep` | [`crc8.sv`](crc8.sv) is the derived LFSR | `bv_decide` |
| `crc8_rtl_correct` | after reset to `0xFF`, `crc8.sv` holds `(0xFF·Xⁿ + M·X⁸) mod (X⁸ + X² + X + 1)` | the laws |
| `xmodem_check` | the spec gives CRC-16/XMODEM's `0x31C3` on `"123456789"` | kernel `decide` |
| `smbus_check` | the spec gives CRC-8/SMBUS's `0xF4` | kernel `decide` |

The check values are theorems about the specification. No polynomial division
ever runs. The kernel runs the derived table loop instead.

### Each step, as a law and a circuit

The diagrams below follow both `calc` blocks one step at a time. Each step has
a law diagram, like the Kadane ones, and a schematic of the program after it.

- **Bit by bit.** The steps of `crc_eq_lfsr` use CRC-8/SMBUS, whose generator
  `g = X⁸ + X² + X + 1` is the one in [`crc8.sv`](crc8.sv), on the message
  `1011`.
- **A byte at a time.** The steps of `crcBytes_eq_table` use CRC-16/XMODEM on
  the two bytes of `"12"`. At width 8 the shift in Sarwate's step is always
  zero, so width 16 shows the whole step.
- **Schematics.** The programs before the LFSR are loops over the message. Each
  is drawn as a machine: a step, a register that keeps its result, and the
  stages that read the register after the last bit. The register's label is
  the state the `calc` block's right-hand column counts.

[`diagrams/CrcDiagrams.lean`](diagrams/CrcDiagrams.lean) draws them. Mathlib's
polynomials over GF(2) do not compute, so it models them as bit masks. A
`#guard` checks the model against `lfsrStep` on every message of up to 8 bits.
Registers, bytes and the table come from `CRC.lean` itself. The LFSR is found
by running `lfsrStep` on each unit input: the step is linear, as a `#guard`
checks, so its taps are the bits each input flips.

```bash
lake exe crc_diagrams        # redraws the CRC SVGs in bird-meertens/diagrams
```

#### The specification

The CRC is defined on the whole message. Nothing can be computed until the last
bit has arrived.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_spec_dark.svg">
  <img alt="Schematic of the specification as a pipeline: the message M, n bits, goes through msgPoly to n coefficients, through · * X⁸ to n + 8, and through · mod g to the 8-coefficient CRC." src="diagrams/crc_circuit_spec_light.svg">
</picture>

#### 1. Horner's rule

One multiply-add per bit builds the message polynomial, so the definition
becomes a loop. Its state is the whole polynomial so far, which grows with the
message.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_horner_dark.svg">
  <img alt="Commuting diagram. From [1, 0, 1, 1], msgPoly gives X³ + X + 1. foldl horner 0 gives (((0·X + 1)·X + 0)·X + 1)·X + 1, which is also X³ + X + 1." src="diagrams/crc_horner_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_horner_dark.svg">
  <img alt="Schematic of a loop: each bit b enters the step p·X + b, and a register of n coefficients keeps the result. After the last bit, · * X⁸ and · mod g give the CRC." src="diagrams/crc_circuit_horner_light.svg">
</picture>

#### 2. Shift fusion

Multiplying by `X⁸` commutes with Horner's step, so it moves into the loop:
each bit now enters at `X⁸`. The state grows to `n + 8` coefficients.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_shift_fusion_dark.svg">
  <img alt="Commuting diagram. From [1, 0, 1, 1], foldl horner 0 then · * X⁸ gives X¹¹ + X⁹ + X⁸. foldl (hornerShift 8) 0 gives the same polynomial, written out as a fold." src="diagrams/crc_shift_fusion_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_shift_dark.svg">
  <img alt="Schematic of a loop with the step p·X + b·X⁸ and a register of n + 8 coefficients, followed by · mod g after the last bit." src="diagrams/crc_circuit_shift_light.svg">
</picture>

#### 3. Reduction fusion

Reducing modulo `g` commutes with the step too, so it also moves into the loop.
Now the state stays below degree 8, however long the message.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_mod_fusion_dark.svg">
  <img alt="Commuting diagram. From [1, 0, 1, 1], foldl (hornerShift 8) 0 gives X¹¹ + X⁹ + X⁸, and reducing modulo g gives X⁵ + X⁴ + 1. foldl (hornerMod g 8) 0 gives X⁵ + X⁴ + 1 directly." src="diagrams/crc_mod_fusion_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_mod_dark.svg">
  <img alt="Schematic of a loop with the step (p·X + b·X⁸) mod g and a register of 8 coefficients, which is the CRC after the last bit." src="diagrams/crc_circuit_mod_light.svg">
</picture>

#### 4. Data refinement

A register of 8 bits holds the 8 coefficients, and one clock of the LFSR is one
reduced Horner step. The LFSR is `crc8.sv`, gate for gate.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_refine_fusion_dark.svg">
  <img alt="Commuting diagram. From [1, 0, 1, 1], foldl (hornerMod g 8) 0 gives X⁵ + X⁴ + 1. foldl (lfsrStep 0x07) 0 gives the register 00110001, and toPoly reads it as X⁵ + X⁴ + 1." src="diagrams/crc_refine_fusion_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_lfsr_dark.svg">
  <img alt="Schematic of an 8-bit LFSR: register bits r₀ to r₇ in a row, the feedback r₇ ⊕ b returning along the bottom into r₀, and XORs before r₁ and r₂, the taps of 0x07." src="diagrams/crc_circuit_lfsr_light.svg">
</picture>

#### A byte at a time

Software reads bytes. The bit-level derivation applies to a byte string once
`bitsOf` has turned each byte into eight bits, so the LFSR clocks eight times a
byte.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_serial_dark.svg">
  <img alt="Schematic of a byte x going through bitsOf, one bit at a time, into lfsrStep 0x1021 and a 16-bit register, read by toPoly after the last byte." src="diagrams/crc_circuit_serial_light.svg">
</picture>

#### 5. Fold over concatenation

Folding over the flattened bits is folding over each byte's bits in turn. No
gate changes: the schematic above is the circuit of this line too.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_fold_concat_dark.svg">
  <img alt="Commuting diagram. From the bits of the two bytes, flatten then foldl (lfsrStep 0x1021) 0 gives 0x20B5. foldl (foldl (lfsrStep 0x1021)) 0 gives 0x20B5 too." src="diagrams/crc_fold_concat_light.svg">
</picture>

#### 6. Fold–map fusion

`bitsOf` joins the fold's step. Eight clocks become one `byteStep`, so the
register changes once a byte.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_fold_map_dark.svg">
  <img alt="Commuting diagram. From the bytes [0x31, 0x32], map bitsOf then foldl (foldl (lfsrStep 0x1021)) 0 gives 0x20B5. foldl (byteStep 0x1021) 0 gives 0x20B5 too." src="diagrams/crc_fold_map_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_bytestep_dark.svg">
  <img alt="Schematic of the 16-bit register feeding eight lfsrStep stages in a row, each taking one bit of the byte, most significant first, with the last stage feeding the register." src="diagrams/crc_circuit_bytestep_light.svg">
</picture>

#### 7. Sarwate's table

Reduction modulo `g` is linear, so eight clocks are one table lookup. The top
byte of the register meets the input byte, and the rest of the register shifts
up a byte.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_table_dark.svg">
  <img alt="Commuting diagram. From the register 0x2672 and the byte 0x32, byteStep 0x1021 gives 0x20B5. tableStep gives 0x7200 ⊕ table (0x26 ⊕ 0x32) = 0x7200 ⊕ 0x52B5 = 0x20B5." src="diagrams/crc_table_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/crc_circuit_table_dark.svg">
  <img alt="Schematic of Sarwate's step: the register's top byte XOR the input byte indexes a 256-entry table, whose entry is XORed with the register shifted up a byte." src="diagrams/crc_circuit_table_light.svg">
</picture>

### Related work on CRCs

- W. W. Peterson and D. T. Brown,
  [Cyclic codes for error detection](https://doi.org/10.1109/JRPROC.1961.287814),
  Proceedings of the IRE 49(1), 1961. It introduced the CRC, defined through
  polynomials, and the shift-register circuits that compute it.
- D. V. Sarwate,
  [Computation of cyclic redundancy checks via table look-up](https://doi.org/10.1145/63030.63037),
  Communications of the ACM 31(8), 1988. The table that `crcBytes_eq_table`
  ends at.
- T. V. Ramabadran and S. S. Gaitonde,
  [A tutorial on CRC computations](https://doi.org/10.1109/40.7773), IEEE Micro
  8(4), 1988 ([free copy](https://www.ee.bilkent.edu.tr/~ee538/crc.pdf)). The
  theory, then four software algorithms compared, among them table lookup.
- R. N. Williams,
  [A painless guide to CRC error detection algorithms](https://zlib.net/crc_v3.txt),
  1993. It goes from long division to table-driven code, and gives the
  parametrised model the catalogues use.
- G. Cook, [Catalogue of parametrised CRC algorithms](https://reveng.sourceforge.io/crc-catalogue/).
  The source of the check values in `xmodem_check` and `smbus_check`.
- G. Albertengo and R. Sisto,
  [Parallel CRC generation](https://doi.org/10.1109/40.60527), IEEE Micro
  10(5), 1990, and G. Campobello, G. Patanè and M. Russo,
  [Parallel CRC realization](https://doi.org/10.1109/TC.2003.1234528), IEEE
  Transactions on Computers 52(10), 2003. Both derive circuits that take
  several bits a clock from the serial LFSR, as `byteStep` takes eight.
- E. Kmett, [Parallel and incremental CRCs](https://www.schoolofhaskell.com/user/edwardk/parallel-crc),
  2013. In Haskell, the CRC as a fold, then as a monoid, so that it can be
  computed in parallel and updated after small edits.
- P. Koopman and T. Chakravarty,
  [Cyclic redundancy code (CRC) polynomial selection for embedded networks](https://doi.org/10.1109/DSN.2004.1311885),
  DSN 2004 ([free copy](https://users.ece.cmu.edu/~koopman/roses/dsn04/koopman04_crc_poly_embedded.pdf)).
  How to choose the generator `g`, which this derivation takes as given.
- The [hex-gf2](https://github.com/leanprover/hex-gf2) library implements
  polynomials over GF(2) in Lean, packed into machine words and without
  Mathlib, with proofs about division. It is the computable counterpart of the
  Mathlib polynomials used here.
- Wikipedia's [Computation of cyclic redundancy checks](https://en.wikipedia.org/wiki/Computation_of_cyclic_redundancy_checks)
  gives a series of equivalent algorithms, from code close to the mathematics
  to bytewise tables.

## Why the CRC suits a talk

- Every hardware engineer knows the spec. It fits on one line.
- One law, fold fusion, does three jobs: a shift, a reduction, a change of representation.
- Bits meet polynomials in one lemma, `toPoly_lfsrStep`. It covers one clock. Fusion does the induction.
- The derivation ends at RTL in this repo, and at published check values.
- It is small. `CRC.lean` is about 400 lines, with 38 theorems.

A possible running order for slides:

1. The spec: `(M·Xᵏ) mod g`.
2. Horner's rule. Now a loop, but its state grows with the message.
3. Two fusions. The state is now bounded by `k`, but still a polynomial.
4. Data refinement to a `k`-bit register. The one-clock lemma.
5. Bytes. Two list laws, then Sarwate's table from linearity.
6. The payoff. `crc8.sv` is that LFSR, and the check values are theorems.

## A carry-lookahead adder

The carry into column `i` of a binary addition is set when the low `i` columns,
plus the carry in, overflow `i` bits. That is the whole specification. A
ripple-carry adder computes the carries one column at a time. A carry-lookahead
adder computes them with a parallel prefix network.

`carries_eq_prefixNet` derives the second from the first. Columns run least
significant first. The right column is the depth of the carry chain for `n`
columns.

```
  map (carryOut c) ∘ inits                                  the specification
= map (foldl carry c) ∘ inits                               full-adder law
= scanl carry c                                             scan lemma          n
= scanl ev c ∘ map gp                                       carry = g ∨ (p ∧ c)
= map fst ∘ scanl (⊛) (c, false) ∘ map gp                   scan fusion
= map fst ∘ scan1 (⊛) ∘ ((c, false) :: ·) ∘ map gp          definition of scan1
= map fst ∘ prefixNet (⊛) ∘ ((c, false) :: ·) ∘ map gp      parallel prefix     ⌈log₂ (n + 1)⌉
```

Here `gp (a, b) = (a ∧ b, a ⊕ b)` gives a column's generate and propagate bits.
The carry operator is `(g₁, p₁) ⊛ (g₂, p₂) = (g₂ ∨ (p₂ ∧ g₁), p₁ ∧ p₂)`. It is
associative, and that is all the last step needs. The carry in enters as an
extra column that generates `c`.

The scan lemma is the one from the Kadane derivation. Scan fusion does the job
that fold fusion did for the CRC.

`prefixNet` is Sklansky's network. It scans both halves at once. Then it
combines the left half's total into every result of the right half. It takes
its operator as an argument, so the same code has three readings.

| Run it on | It computes | Theorem |
|---|---|---|
| bits, with `⊛` | the carries | `cla_correct`: the output, read as a number, is the sum |
| arrival times, with `later t u = max t u + 1` | each output's depth | `prefixNet_depth`: at most `⌈log₂ n⌉` levels; `serial_depth`: the serial scan needs `n - 1` |
| symbolic gates | a netlist | `claNet_correct`: the netlist adds |

`lake exe adder_netlist` prints the netlist as Verilog. Each distinct gate
becomes one wire. The 32-bit adder is
[`netlist/sklansky_adder_32.v`](netlist/sklansky_adder_32.v).

| Width | Ripple gates | Ripple depth | Sklansky gates | Sklansky depth |
|---|---|---|---|---|
| 8 | 48 | 17 | 55 | 9 |
| 16 | 96 | 33 | 131 | 11 |
| 32 | 192 | 65 | 307 | 13 |
| 64 | 384 | 129 | 707 | 15 |

Depth counts two-input gates on the longest path. Sklansky buys logarithmic
depth with more gates: 1.6 times as many at 32 bits, 1.8 at 64. Both netlists come from lines of the
derivation: `rippleNet` from the third, `claNet` from the last.

Only the Verilog printer is unverified. Two outside tools check what it prints.

```bash
make -C bird-meertens/netlist lint     # Verilator with every warning on: clean
make -C bird-meertens/netlist equiv    # Yosys SAT: the adder equals + for every input
```

The SAT proof passes at widths 8, 32 and 64. A netlist with one gate flipped
fails it.

### From ripple-carry to carry-lookahead, directly

`refine_cla_from_ripple_carry` relates the two adders themselves. It starts
from the ripple-carry adder as Lava builds it: `row fullAdd`, a chain of full
adders. It ends at `cla`. Neither end mentions the specification.

```
  snoc ∘ row fullAdd c                                             a row of full adders   n
= adder (scanl carry c)                                            row law
= adder (scanl ev c ∘ map gp)                                      carry = g ∨ (p ∧ c)
= adder (map fst ∘ scanl (⊛) (c, false) ∘ map gp)                  scan fusion
= adder (map fst ∘ scan1 (⊛) ∘ ((c, false) :: ·) ∘ map gp)         definition of scan1
= adder (map fst ∘ prefixNet (⊛) ∘ ((c, false) :: ·) ∘ map gp)     parallel prefix        ⌈log₂ (n + 1)⌉
= cla c                                                            definition of cla
```

`adder net xs = sumBits xs (net xs)` wraps a carry network `net`. It adds one
XOR per column, then the carry out. `snoc` puts the row's last carry on top of
its sum bits.

The row law is the one new step. A row's carries are a scan, and each output
reads its column and the carry into it. After it come the steps above, under
`adder`. The netlist section's `rippleNet` is the second line, `adder (scanl
carry c)`, built from gates.

### Each step of the refinement, as a law and a circuit

The diagrams below follow `refine_cla_from_ripple_carry` one step at a time.
Each step has a law diagram, like the Kadane ones above, and a schematic of
the circuit after the step.

- **Law diagrams.** They add `5 + 4` with a carry in of 1, in three columns.
  Bits are written 1 and 0, least significant first. The first column
  propagates the carry in, the second kills it, and the third generates the
  carry out.
- **Schematics.** They show seven columns, with column 0, on the left,
  carrying the carry in. Time runs down the page: each cell sits one level
  below the latest of its inputs, so a schematic's height is its depth. The
  bracket on the right spans the carry chain.

[`diagrams/AdderDiagrams.lean`](diagrams/AdderDiagrams.lean) draws them. Each
schematic comes from running its line's own `row`, `scanl`, `scan1` or
`prefixNet` on symbolic wires. Before it is drawn, it is evaluated cell by
cell with the functions in `Adder.lean`, and it must add correctly on all 2¹⁵
inputs.

```bash
lake exe adder_diagrams      # redraws the adder SVGs in bird-meertens/diagrams
```

#### The ripple-carry adder

The derivation starts from Lava's ripple-carry adder: a row of full adders,
each passing its carry to the right. The carry chain is as long as the adder.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_circuit_ripple_dark.svg">
  <img alt="Schematic of a row of seven full adders. The carry in enters the first; each passes its carry to the next, one level lower, so the carry chain is seven levels deep." src="diagrams/adder_circuit_ripple_light.svg">
</picture>

#### 1. The row law

A row's carries are a scan, and each output reads its column and the carry
into it. So the row splits into a chain of `carry` cells and a row of sum
cells. The chain is as deep as before.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_row_law_dark.svg">
  <img alt="Commuting diagram. From the columns [(1, 0), (0, 0), (1, 1)], row fullAdd c then snoc, and scanl carry c then sumBits, both give [0, 1, 0, 1]." src="diagrams/adder_row_law_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_circuit_carry_chain_dark.svg">
  <img alt="Schematic of a chain of seven carry cells, then a row of sum cells. Each sum cell reads its column and the carry from the column to its left." src="diagrams/adder_circuit_carry_chain_light.svg">
</picture>

#### 2. carry = g ∨ (p ∧ c)

Each `carry` cell splits into a `gp` cell, which reads only its own column,
and an `ev` cell on the chain. Scan–map fusion moves the `gp` cells out of the
scan, so they all work at once, on the first level.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_carry_ev_dark.svg">
  <img alt="Commuting diagram. From the columns, scanl carry c gives the carries [1, 1, 0, 1]. map gp gives [(0, 1), (0, 0), (1, 0)], and scanl ev c gives the same carries." src="diagrams/adder_carry_ev_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_circuit_gp_dark.svg">
  <img alt="Schematic with a row of seven gp cells on the first level, then a chain of seven ev cells, then the sum cells." src="diagrams/adder_circuit_gp_light.svg">
</picture>

#### 3. Scan fusion

The chain now carries `(g, p)` pairs, combined by `⊛`, and each carry is the
`g` of a pair. This works because `fst` takes each `⊛` step to an `ev` step.
A pair costs more than a bit, but `⊛`, unlike `ev`, is associative.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_scan_fusion_dark.svg">
  <img alt="Commuting diagram. From [(0, 1), (0, 0), (1, 0)], scanl ev c gives [1, 1, 0, 1]. scanl (⊛) (c, false) gives [(1, 0), (1, 0), (0, 0), (1, 0)], and map fst gives the same carries." src="diagrams/adder_scan_fusion_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_circuit_scan_dark.svg">
  <img alt="Schematic with the gp cells, then a chain of seven ⊛ cells seeded with (c, false), then the sum cells." src="diagrams/adder_circuit_scan_light.svg">
</picture>

#### 4. Definition of `scan1`

The carry in was the scan's seed. Now it is the first element of the list the
scan runs over, as the pair `(c, false)`: a column that generates `c` and
propagates nothing. No cell changes. A `#guard` checks that lines 4 and 5
build the same circuit, so the schematic above is the circuit of both.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_scan1_dark.svg">
  <img alt="Commuting diagram. From [(0, 1), (0, 0), (1, 0)], scanl (⊛) (c, false) gives [(1, 0), (1, 0), (0, 0), (1, 0)]. Putting (c, false) in front and taking scan1 (⊛) gives the same list." src="diagrams/adder_scan1_light.svg">
</picture>

#### 5. Parallel prefix

`⊛` is associative, so the scan's terms can be bracketed in any way. `scan1`
brackets them to the left, one after another. Sklansky's `prefixNet` brackets
them as balanced trees, so the last result waits 2 levels on four inputs,
not 3. At seven columns, eight inputs with the carry in, the carry chain drops
from 7 levels to 3.

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_parallel_prefix_dark.svg">
  <img alt="Commuting diagram on the inputs q₀ to q₃. scan1 (⊛) gives ((q₀ ⊛ q₁) ⊛ q₂) ⊛ q₃ as its last term, and prefixNet (⊛) gives (q₀ ⊛ q₁) ⊛ (q₂ ⊛ q₃). Both lists of terms evaluate to [(1, 0), (1, 0), (0, 0), (1, 0)]." src="diagrams/adder_parallel_prefix_light.svg">
</picture>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="diagrams/adder_circuit_sklansky_dark.svg">
  <img alt="Schematic with the gp cells, then Sklansky's network of twelve ⊛ cells in three levels, then the sum cells. The carry chain is three levels deep." src="diagrams/adder_circuit_sklansky_light.svg">
</picture>

#### 6. Definition of `cla`

`cla c` is the name of the circuit above, so the last step changes nothing.

### Why the adder suits a talk

- The spec is the definition of a carry. It assumes nothing about circuits.
- The derivation reuses two laws from the other examples: the scan lemma and fusion.
- Associativity is the reason the adder can be parallel. The proof makes that visible.
- A second calculation turns the textbook row of full adders into Sklansky's adder.
- One Lean function yields a proof, a depth analysis and a netlist. That is Lava's idea, checked.

### Related work

The closest work is O'Donnell and Rünger's functional pearl. It too turns a
ripple-carry adder into a carry-lookahead adder by calculation, in Haskell, as
a semi-formal correctness proof, and it draws the circuit at its main stages.
It meets the same obstacle: the ripple adder's carry scan uses a function that
is not associative. It finds associativity another way. It partially evaluates
each column's carry function, composes those functions with `∘`, and then
represents them as the symbols `K`, `P` and `G`, for kill, propagate and
generate. A tree-shaped parallel scan finishes the job. The derivation here
introduces the `(g, p)` pairs directly, by scan fusion, and ends at Sklansky's
network. It also starts from Lava's row of full adders, and Lean checks every
step.

- J. T. O'Donnell and G. Rünger,
  [Functional pearl: Derivation of a logarithmic time carry lookahead addition circuit](https://doi.org/10.1017/S0956796804005180),
  Journal of Functional Programming 14(6), 2004. An earlier version is in the
  [2001 Haskell Workshop proceedings](https://www.haskell.org/haskell-symposium/2001/2001-62.pdf).

The step to a parallel prefix network has an algebra of its own:

- R. Hinze, [An algebra of scans](https://www.cs.ox.ac.uk/ralf.hinze/publications/MPC04.pdf),
  Mathematics of Program Construction 2004, LNCS 3125. Two building blocks and
  four combinators describe the standard prefix circuits. The algebra's laws
  prove circuits correct and derive new ones, such as Brent–Kung and
  Ladner–Fischer.
- M. Sheeran,
  [Functional and dynamic programming in the design of parallel prefix networks](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/functional-and-dynamic-programming-in-the-design-of-parallel-prefix-networks/BF6065585BE32438CDF081A44741A5B8),
  Journal of Functional Programming 21(1), 2011. Networks modelled in Haskell,
  with search, come out smaller than Ladner–Fischer's at the same depth.
- M. Sheeran,
  [Hardware design and functional programming: a perfect match](https://www.jucs.org/jucs_11_7/hardware_design_and_functional/jucs_11_7_1135_1158_sheeran.html),
  Journal of Universal Computer Science 11(7), 2005.
- C. Elliott,
  [Generic functional parallel algorithms: scan and FFT](https://doi.org/10.1145/3110251),
  ICFP 2017 ([free copy](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf)).
  Scan algorithms follow from a few functor combinators, with no arrays and no
  indexing.

Circuits have been derived by refinement before, in Ruby, the relational
language that this repository's DSL is named after, and described as
functions in Lava:

- G. Jones and M. Sheeran,
  [Designing arithmetic circuits by refinement in Ruby](https://link.springer.com/chapter/10.1007/3-540-56625-2_15),
  Mathematics of Program Construction 1992, LNCS 669. A well-known arithmetic
  circuit follows from decisions made about the abstract algorithm, so it is
  correct by construction.
- G. Jones and M. Sheeran, Circuit design in Ruby, in J. Staunstrup (ed.),
  Formal Methods for VLSI Design, North-Holland, 1990.
- P. Bjesse, K. Claessen, M. Sheeran and S. Singh,
  [Lava: hardware design in Haskell](https://doi.org/10.1145/289423.289440),
  ICFP 1998. One circuit description, many interpretations: simulation,
  verification and netlists, as `prefixNet` has here.

The carry operator `⊛`, and carries as a scan:

- R. P. Brent and H. T. Kung,
  [A regular layout for parallel adders](https://doi.org/10.1109/TC.1982.1675982),
  IEEE Transactions on Computers C-31(3), 1982
  ([free copy](https://maths-people.anu.edu.au/~brent/pd/rpb060.pdf)). It
  defines the associative operator on `(g, p)` pairs.
- G. E. Blelloch, [Prefix sums and their applications](https://www.cs.cmu.edu/~scandal/papers/CMU-CS-90-190.html),
  CMU-CS-90-190, 1990. Adding numbers is one of its applications of scan.

Machine-checked proofs of prefix adders, which verify them rather than derive
them:

- F. Liu, Q. Tan and G. Chen,
  [Formal proof of prefix adders](https://www.sciencedirect.com/science/article/pii/S0895717710000609),
  Mathematical and Computer Modelling 52(1–2), 2010. Bit pairs with the carry
  operator form a monoid, and that proves the Kogge–Stone adder correct.
- Wang et al.,
  [Functional verification of high performance adders in Coq](https://doi.org/10.1155/2014/197252),
  Journal of Applied Mathematics, 2014. Carry-lookahead, Ling and parallel
  prefix adders, verified in Coq for every width.

Three informal explanations:

- Wikipedia's [Brent–Kung adder](https://en.wikipedia.org/wiki/Brent%E2%80%93Kung_adder)
  sketches the step from ripple carry to the operator on `(g, p)` pairs.
- A. Feldmann, [Carry lookahead adders](https://feldmann.nyc/blog/carry-lookahead-adder).
  The carries come from composing one-bit carry functions with a prefix
  network.
- K. Shirriff,
  [Reverse-engineering a carry-lookahead adder in the Pentium](https://www.righto.com/2025/01/pentium-carry-lookahead-reverse-engineered.html),
  2025. The carry merge is associative, so sub-ranges can be merged in any
  order.

## Four sorter cores, related

Claessen, Sheeran and Singh, *The Design and Verification of a Sorter Core*
(CHARME 2001, LNCS 2144), build four sorters for a Virtex-II from Lava
connection patterns. [`BirdMeertens/Sorters.lean`](BirdMeertens/Sorters.lean)
copies their definitions and relates the four by calculation.

All four mergers fit one schema, `fly P L`. It places a connection pattern `P`
around the merger of half the size, then adds a last column `L`.

| Merger | `P` | `L` |
|---|---|---|
| `bfly`, Batcher's bitonic merger | `ilv` | `evens` |
| `mergeOE`, Batcher's odd–even merger | `ilv` | `mid ∘ evens` |
| `vfly`, the balanced merger of Dowd et al. | `vee` | `evens` |
| `qfly`, the merger of Canfield and Williamson | `que` | `mid ∘ evens` |

The main results hold for any comparator that keeps lengths and is symmetric,
`f [a, b] = f [b, a]`. The equalities are on lists of length `2ⁿ`.

```
sortB  (n + 1) = two (sortB n)  >-> mergeB  (n + 1)    where mergeB n = parl id reverse >-> bfly n
sortOE (n + 1) = two (sortOE n) >-> mergeOE (n + 1)
qfly n  = unriffle >-> mergeOE n
vfly n  = unriffle >-> mergeB n
sortQ n = hrep n (unriffle >-> mergeOE n)
sortV n = hrep n (unriffle >-> mergeB n)
```

So all four cores come from Batcher's two mergers, used in two ways.

| Merger | Recursive: sort both halves, then merge | Periodic: `n` mergers, each behind `unriffle` |
|---|---|---|
| bitonic, `mergeB` | `sortB` | `sortV` |
| odd–even, `mergeOE` | `sortOE` | `sortQ` |

Canfield and Williamson titled their paper "a sequential sorting network
analogous to the Batcher merger". Here the analogy becomes an equation.
`qfly_eq_unriffle_mergeOE` is one `calc` block; `f` is the comparator.

```
  qfly (n + 2)
= que (qfly (n + 1)) >-> mid (evens f)                                      definition
≈ que (unriffle >-> mergeOE (n + 1)) >-> mid (evens f)                      induction
≈ que unriffle >-> que (mergeOE (n + 1)) >-> mid (evens f)                  que is a functor
≈ ilv unriffle >-> two unriffle >-> two (mergeOE (n + 1)) >-> ilv riffle >-> mid (evens f)
                                                                            ilv riffle undoes ilv unriffle
≈ unriffle >-> unriffle >-> two (mergeOE (n + 1)) >-> ilv riffle >-> mid (evens f)   W3
≈ unriffle >-> unriffle >-> two (mergeOE (n + 1)) >-> riffle >-> mid (evens f)       W4, f symmetric
= unriffle >-> mergeOE (n + 2)                                              definition
```

`vfly_eq_unriffle_mergeB` has the same shape. It uses W5, and the fact that a
butterfly of symmetric components ignores a reversal of its input.

Four wiring laws carry the proofs. Each holds on every list of length `4m`.

| Law | Statement |
|---|---|
| W3 | `ilv unriffle >-> two unriffle = unriffle >-> unriffle` |
| W4 | `ilv riffle = riffle >-> mid (altAux true)` |
| W5 | `alt >-> ilv unriffle >-> ilv (parl id reverse) = unriffle >-> parl id reverse >-> oddsRev` |
| W6 | `ilv (two g) = two (ilv g)` |

They are proved by splitting a list into four interleaved quarter-lists. Then
each wiring only rearranges or reverses the quarters. No position arithmetic is
needed.

Symmetry matters twice. The last column absorbs swaps inside its pairs: that is
the step after W4. And `oddsRev` vanishes into a butterfly. With an asymmetric
component, the `qfly` identity already fails at 4 inputs.

The paper's own lemma from §6, `que (ilv f) = ilv (ilv f)`, follows from W3 and
W6 (`que_ilv`). Its §5 checks are repeated. A kernel proof shows that all four
sorters sort every 4-bit input. Evaluation covers every 8-bit input. The
counterexample `[0, 1, 0, 1]` shows that `bflyCompose` is not a sorter.

### How the identities were found

They were found by testing before they were proved. Two comparator networks are
equal exactly when they agree on every 0–1 input. So exhaustive 0–1 testing
compared candidate equations up to 16 inputs. A symbolic symmetric component
extended the tests to 64 inputs. A search over all 8! input wirings
at 8 inputs showed two families: `{bfly, vfly}` and `{mergeOE, qfly}`. Within a
family, one merger is the other behind a wiring. No wiring links the families.

## Trust

| Theorems | Axioms |
|---|---|
| Kadane | `propext`, `Quot.sound` |
| CRC derivation and check values | the above, plus `Classical.choice` from Mathlib |
| `crc8Next_eq_lfsrStep`, `crc8_rtl_correct` | the above, plus `crc8Next_eq_lfsrStep._native.bv_decide.ax_1_7`, the axiom with which `bv_decide` trusts its compiled check |
| Adder: `carries_eq_prefixNet`, `cla_correct`, `claNet_correct` | `propext`, `Classical.choice`, `Quot.sound` |
| Adder: `refine_cla_from_ripple_carry`, `rippleNet_correct`, `prefixNet_depth`, `serial_depth` | `propext`, `Quot.sound` |
| Sorters: `qfly_eq_unriffle_mergeOE`, `vfly_eq_unriffle_mergeB`, `sortQ_eq`, `sortV_eq`, `que_ilv` | `propext`, `Classical.choice`, `Quot.sound` |
| Sorters: `sortB_eq` | `propext`, `Quot.sound` |

`crc8Next` is transcribed from `crc8.sv` by hand. It is not the generated model.
The adder's Verilog printer is unverified. Verilator and Yosys check its output.

## Build

These examples share the repository's one `lakefile.toml`, with Lean and
Mathlib `v4.34.1`. It builds the `BirdMeertens` library with `autoImplicit` on
and a larger `maxRecDepth`, as these files expect. Run every command from the
repository root.

```bash
lake exe cache get
lake build BirdMeertens kadane_bench kadane_diagrams adder_diagrams crc_diagrams adder_netlist   # `lake build` builds them too
lake exe kadane_bench      # the timings and plots; needs only core Lean
lake exe kadane_diagrams   # the diagrams of the Kadane laws; needs only core Lean
lake exe adder_diagrams    # the law diagrams and schematics of the adder refinement
lake exe crc_diagrams      # the law diagrams and schematics of the CRC derivation
lake exe adder_netlist     # the adder as Verilog; then make -C bird-meertens/netlist lint equiv
```
