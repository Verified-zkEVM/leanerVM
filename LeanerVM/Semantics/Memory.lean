/-
  LeanerVM.Semantics.Memory

  Exponent addressing, the committed memory image, and the two-cell public input.
-/

module

public import LeanerVM.Parameters.Generator

/-!
# The memory image and the public input

leanISA roadmap Layer 2 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

**Addressing** (Category B: specification §2, `doc/leanvm/body/02-vm-specification.tex:22` and
`:49-52`). Memory is `2^κ` words of `E`, the word of logical index `i` sits at the address
`g ^ i ∈ K`, and an access at any other address, `0` included, is invalid. `gLog?` is the bounded
discrete logarithm that turns an address back into its index, or `none`; `MemImage.read` is the
only reader. It is `noncomputable`: the index is `Classical.choose` of `∃ i, a = g ^ i`, so the
specification cannot be run, and it is trusted through `gLog?_spec` alone, with its body not
exposed, so a `module` importer can reason about it only through the specification. The cost of
a discrete logarithm never enters the semantics; a computable carrier for running executions, if
one is ever wanted, is separate work bridged to this specification.

**The image** (Category A, roadmap Layer 2, from specification §2 "Write-once memory" and
"Non determinism", `02-vm-specification.tex:37-47`). The memory is committed whole before
execution and every instruction only reads it, so an execution's memory is one total function
`MemImage κ = Fin (2 ^ κ) → E`, and *all* nondeterminism — the log-size `κ` and every
prover-chosen word — is the choice of image. The executor's write-once bookkeeping, zero reads
of unset cells, and on-demand growth (`crates/lean_vm/src/cpu/execute.rs`) are witness
generation producing such an image, not a second memory model (roadmap acceptance test 19).
Rust-informed: the executor's seeding and address decoding (`execute.rs:36-40`, `:173-177`)
were read before this file was written.

**The public input** (Category B: specification §2, `02-vm-specification.tex:16,24`, and §8.2,
`08-end-to-end-protocol.tex:29`; seeded at `execute.rs:173-177`, a third limb rejected at
`cpu/mod.rs:139-143`). The 256-bit input is four `K` lanes fixing the first two words of the
image as `input₀ + input₁·y` and `input₂ + input₃·y`, top limbs zero.

## Wrong readings excluded

* `read L 0 = none` for every image and every size (`MemImage.read_zero`; acceptance test 2).
* `gLog?_spec` requires `κ < 64`: with `2 ^ κ > 2 ^ 64 - 1 = orderOf g` one address would name
  two indices. Every announced size has `κ ≤ maxLogMem = 32`, which Layer 3's
  `HasPublicBoundary` carries; the semantics itself imposes no cap.
* `word0` and `word1` take two lanes each, never three (`PublicInput.words_injective`;
  acceptance test 17).
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

/-! ## Exponent addressing -/

public section

open Classical in
/-- The bounded discrete logarithm: `some i` when `a = g ^ i` with `i < 2 ^ κ`, else `none`.
The index is chosen, not computed, so the specification cannot be run; not exposed, so importers
use it through `gLog?_spec`. -/
noncomputable def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if h : ∃ i : Fin (2 ^ κ), a = gpow i then some (Classical.choose h) else none

end

@[expose] public section

/-! ## The memory image -/

/-- The committed memory: `2 ^ κ` words of `E`, by logical index. -/
abbrev MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E

/-- Read the word at address `a`: `some (L i)` when `a = g ^ i`, `none` otherwise. -/
noncomputable def MemImage.read {κ : ℕ} (L : MemImage κ) (a : K) : Option E :=
  (gLog? κ a).map L

/-! ## The public input -/

/-- The 256-bit public input as four `K` lanes (specification §2). -/
structure PublicInput where
  /-- `input₀, …, input₃`. -/
  lanes : Fin 4 → K
  deriving DecidableEq

/-- The first memory word, `input₀ + input₁·y`. -/
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

/-- The second memory word, `input₂ + input₃·y`. -/
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0

/-! ## Load-bearing lemmas -/

/-- The specification of `gLog?`: on an address space of at most `2 ^ 63` cells, so that
`2 ^ κ ≤ orderOf g`, `gLog? κ a = some i` exactly when `a = g ^ i`. -/
theorem gLog?_spec {κ : ℕ} (hκ : κ < 64) {a : K} {i : Fin (2 ^ κ)} :
    gLog? κ a = some i ↔ a = gpow i := by
  unfold gLog?
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro hi
      obtain rfl := Option.some.inj hi
      exact hc
    · intro hi
      have hbound : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hj : ((Classical.choose h : Fin (2 ^ κ)) : ℕ) < 2 ^ 64 - 1 := by
        have := (Classical.choose h).isLt; omega
      have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
      exact congrArg some (Fin.ext (gpow_injOn hj hi' (hc.symm.trans hi)))
  · exact ⟨fun hi ↦ (nomatch hi), fun hi ↦ absurd ⟨i, hi⟩ h⟩

/-- `gLog?` fails exactly on the addresses that are no power below `2 ^ κ`; no size bound is
needed. -/
theorem gLog?_eq_none_iff {κ : ℕ} {a : K} :
    gLog? κ a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ gpow i := by
  unfold gLog?
  split_ifs with h
  · exact ⟨fun hn ↦ (nomatch hn), fun hn ↦ absurd h (not_exists.mpr hn)⟩
  · exact ⟨fun _ ↦ not_exists.mp h, fun _ ↦ rfl⟩

/-- `0` is never an address, whatever the size. -/
theorem gLog?_zero (κ : ℕ) : gLog? κ 0 = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ gpow_ne_zero i h.symm

/-- A power past the end is no address: `g ^ j` with `2 ^ κ ≤ j < orderOf g` has no index. -/
theorem gLog?_gpow_eq_none {κ j : ℕ} (hj : 2 ^ κ ≤ j) (hj' : j < 2 ^ 64 - 1) :
    gLog? κ (gpow j) = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ by
    have hi : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have := gpow_injOn hj' hi h
    have := i.isLt
    omega

/-- Reading at the address of index `i` gives word `i`. -/
theorem MemImage.read_gpow {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) (i : Fin (2 ^ κ)) :
    L.read (gpow i) = some (L i) := by
  rw [MemImage.read, (gLog?_spec hκ).mpr rfl, Option.map_some]

/-- A successful read is the word of the address's index. -/
theorem MemImage.read_eq_some_iff {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) {a : K} {v : E} :
    L.read a = some v ↔ ∃ i : Fin (2 ^ κ), a = gpow i ∧ L i = v := by
  simp only [MemImage.read, Option.map_eq_some_iff, gLog?_spec hκ]

/-- A read fails exactly at the addresses that are no power below `2 ^ κ`. -/
theorem MemImage.read_eq_none_iff {κ : ℕ} (L : MemImage κ) {a : K} :
    L.read a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ gpow i := by
  rw [MemImage.read, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Address `0` reads nothing (roadmap acceptance test 2). -/
theorem MemImage.read_zero {κ : ℕ} (L : MemImage κ) : L.read 0 = none := by
  rw [MemImage.read, gLog?_zero, Option.map_none]

/-- The two words determine the input: no lane is dropped or shared (acceptance test 17). -/
theorem PublicInput.words_injective :
    Function.Injective fun p : PublicInput ↦ (p.word0, p.word1) := by
  rintro ⟨p⟩ ⟨q⟩ h
  simp only [Prod.mk.injEq, PublicInput.word0, PublicInput.word1] at h
  congr 1
  funext i
  fin_cases i
  · simpa using congrArg (fun z : E ↦ z.limb 0) h.1
  · simpa using congrArg (fun z : E ↦ z.limb 1) h.1
  · simpa using congrArg (fun z : E ↦ z.limb 0) h.2
  · simpa using congrArg (fun z : E ↦ z.limb 1) h.2

end
end LeanerVM.Semantics
