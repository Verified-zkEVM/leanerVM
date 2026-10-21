/-
  LeanVM.Spec.Ideal.Table

  The BLAKE2S rows an execution performs, the standard BLAKE2s chains among them, and the table
  check of the idealized system: every standard chain of a message ends at the oracle's answer.
-/

module

public import LeanVM.Spec.IsaWith

/-!
# The table of an execution

An execution's `BLAKE2S` instructions read nine cells each (`BlakeRow`): four message cells, the
chaining value and the output as two cells each, and the metadata cell. `Trace.blakeRows S t` lists
the rows the run of `t` performs under the semantics `S`, in order; these are the active rows of
the committed `BLAKE2S` table (the proof system's padding rows are not instructions).

A **standard chain** of a byte string `x` (`StdChain`, `docs/roadmap/e2e-security.md` D4) is the
sequence of rows BLAKE2s-256 performs on `x` (RFC 7693, `blake2sBytes`): `k = (|x| − 1)/64 + 1`
rows (one zero block for the empty string), the first from the parameterised IV, each next one from
its predecessor's output; a non-final row compresses block `i` of `x` at the counter `64(i + 1)`
with no flag; the last compresses the rest of `x`, zero-filled, at the counter `|x|` with the
last-block flag `0xFFFFFFFF` and `f1 = 0`.

**The table check** (`TableOK H rows`): for every byte string `x` and every standard chain of `x`
among `rows`, the hash `H` answers `x` with the chain's output. Rows on no standard chain are
unconstrained. With `H` the deployed BLAKE2s and rows the compression function's, it holds
(every standard chain computes `blake2sBytes x`); with `H` a random oracle answered by a log, it is
what binds the in-circuit hashing of the idealized system to the oracle.
-/

namespace LeanVM.Semantics

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ## Rows -/

/-- The nine cells a `BLAKE2S` instruction reads. -/
structure BlakeRow where
  /-- The four message cells. -/
  m : Fin 4 → E
  /-- The chaining value's first cell. -/
  cv0 : E
  /-- The chaining value's second cell. -/
  cv1 : E
  /-- The output's first cell. -/
  out0 : E
  /-- The output's second cell. -/
  out1 : E
  /-- The metadata cell. -/
  md : E

/-- The relation a row checks under the semantics `S`. -/
def BlakeSem.row (S : BlakeSem) (b : BlakeRow) : Prop :=
  S.check b.m b.cv0 b.cv1 b.out0 b.out1 b.md

/-- The row's chaining value as a digest. -/
def BlakeRow.cv (r : BlakeRow) : Digest := cellWords r.cv0 ++ cellWords r.cv1

/-- The row's output as a digest. -/
def BlakeRow.out (r : BlakeRow) : Digest := cellWords r.out0 ++ cellWords r.out1

/-- The row a `BLAKE2S` instruction reads at the registers `r`, if its reads succeed. -/
def blakeRowAt (read : K → Option E) (r : Regs K) : Instr → Option BlakeRow
  | .blake2s om ocv oout omd => do
    let m0 ← read (r.fp * om 0)
    let m1 ← read (r.fp * om 1)
    let m2 ← read (r.fp * om 2)
    let m3 ← read (r.fp * om 3)
    let cv0 ← read (r.fp * ocv)
    let cv1 ← read (r.fp * (g * ocv))
    let out0 ← read (r.fp * oout)
    let out1 ← read (r.fp * (g * oout))
    let md ← read (r.fp * omd)
    pure ⟨![m0, m1, m2, m3], cv0, cv1, out0, out1, md⟩
  | _ => none

/-- The rows the first `n` steps from `r` perform under the semantics `S`, as `runB` steps. -/
noncomputable def runRows (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ℕ → Regs K → List BlakeRow
  | 0, _ => []
  | n + 1, r =>
    if r.pc = prog.finalPc then [] else
      match prog.fetch r.pc, stepB S prog L r with
      | some i, some r' => (blakeRowAt L.read r i).toList ++ runRows S prog L n r'
      | _, _ => []

/-- **The rows of an execution** under the semantics `S`. -/
noncomputable def Trace.blakeRows (S : BlakeSem) {prog : Program} (t : Trace prog) :
    List BlakeRow :=
  runRows S prog t.image t.steps Regs.initial

/-! ## Standard chains and the table check -/

/-- **`c` is the standard BLAKE2s-256 chain of `x`**: the rows `blake2sBytes x` performs. -/
def StdChain (x : List UInt8) (c : List BlakeRow) : Prop :=
  c.length = (x.length - 1) / 64 + 1 ∧
  (∀ (i : ℕ) (hi : i < c.length),
    c[i].cv = if h : i = 0 then paramIv else (c[i - 1]'(by omega)).out) ∧
  (∀ (i : ℕ) (hi : i + 1 < c.length),
    messageWords c[i].m = blockWords ((x.drop (64 * i)).take 64) ∧
      unpackMetadata c[i].md = ((64 * (i + 1)).toUInt64, 0, 0)) ∧
  ∀ (hc : 0 < c.length),
    messageWords (c[c.length - 1]'(by omega)).m = blockWords (x.drop (64 * (c.length - 1))) ∧
      unpackMetadata (c[c.length - 1]'(by omega)).md = (x.length.toUInt64, lastBlock, 0)

/-- **The table check**: every standard chain of every byte string among the rows ends at the
hash's answer for the string. -/
def TableOK (H : List UInt8 → Option Digest) (rows : List BlakeRow) : Prop :=
  ∀ (x : List UInt8) (c : List BlakeRow) (hc : 0 < c.length), (∀ r ∈ c, r ∈ rows) →
    StdChain x c → H x = some (c[c.length - 1]'(by omega)).out

end
end LeanVM.Semantics
