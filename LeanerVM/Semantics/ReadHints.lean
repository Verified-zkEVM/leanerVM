/-
  LeanerVM.Semantics.ReadHints

  Checked address hints with exhaustive fallback.
-/

module

public import LeanerVM.Semantics.FillerRows

/-!
# Address hints that preserve checker coverage

An untrusted list suggests likely memory indices. A hit is verified by comparing its generator
power to the requested address; a miss uses the exhaustive checker. Therefore missing, stale,
out-of-range or incomplete hints never reject an otherwise valid read. This is an optimization
of the Lean reference checker, not an assertion about any foreign producer's hints.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-- Retain only hint indices inside the actual image, without truncation or modular reduction. -/
def hintIndices (κ : ℕ) (hints : List ℕ) : List (Fin (2 ^ κ)) :=
  hints.filterMap fun i ↦ if h : i < 2 ^ κ then some ⟨i, h⟩ else none

/-- Verify suggested indices, falling back to exhaustive search on every miss. -/
def addressIndexWithHints (κ : ℕ) (hints : List (Fin (2 ^ κ))) (a : K) :
    Option (Fin (2 ^ κ)) :=
  match hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | some i => some i
  | none => addressIndex κ a

/-- Hints preserve all successful and failed lookups; no cache-coverage premise is needed. -/
theorem addressIndexWithHints_eq {κ : ℕ} (hκ : κ < 64)
    (hints : List (Fin (2 ^ κ))) (a : K) :
    addressIndexWithHints κ hints a = addressIndex κ a := by
  unfold addressIndexWithHints
  cases hf : hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | none => rfl
  | some i =>
    rw [addressIndex_eq_gLog hκ]
    apply Eq.symm
    apply (gLog?_spec hκ).mpr
    have hgi : decide (gpow (i : ℕ) = a) = true :=
      List.find?_some (p := fun j : Fin (2 ^ κ) ↦ decide (gpow j = a)) hf
    exact (of_decide_eq_true hgi).symm

/-- Read with verified hints; every unsuccessful hint search retains the complete fallback. -/
def readWithHints {κ : ℕ} (image : MemImage κ) (hints : List (Fin (2 ^ κ))) (a : K) :
    Option E := (addressIndexWithHints κ hints a).map image

/-- Hinted reads are exactly the unhinted executable reads. -/
theorem readWithHints_eq {κ : ℕ} (hκ : κ < 64) (image : MemImage κ)
    (hints : List (Fin (2 ^ κ))) (a : K) :
    readWithHints image hints a = readImage image a := by
  rw [readWithHints, readImage, addressIndexWithHints_eq hκ]

/-- Program step with hinted memory reads and instruction fetch. The same suggested indices
are range checked again against the program size before use as fetch hints. -/
def stepWithHints {κ : ℕ} (prog : Program) (image : MemImage κ)
    (hints : List (Fin (2 ^ κ))) (r : Regs K) : Option (Regs K) :=
  let pcHints := hintIndices prog.logSize (hints.map Fin.val)
  (addressIndexWithHints prog.logSize pcHints r.pc).map prog.code >>=
    evaluateInstruction (readWithHints image hints) r

/-- Hinted and exhaustive execution agree for every instruction and every register pair. -/
theorem stepWithHints_eq {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (hints : List (Fin (2 ^ κ))) (r : Regs K) :
    stepWithHints prog image hints r = stepChecked prog image r := by
  unfold stepWithHints stepChecked executeChecked fetchInstruction
  dsimp only
  rw [addressIndexWithHints_eq (lt_of_le_of_lt prog.logSize_le (by decide)),
    show readWithHints image hints = readImage image from funext (readWithHints_eq hκ _ _)]

/-- Filler-row checking using address hints only to accelerate memory reads and fetches. -/
def checkFillerRowsWithHints {κ : ℕ} (prog : Program) (image : MemImage κ)
    (hints : List (Fin (2 ^ κ))) (starts : List (Regs K)) : Bool :=
  decide ((∀ r ∈ starts, r.pc ≠ prog.finalPc) ∧
    (starts.map some).Perm (starts.map (stepWithHints prog image hints)))

/-- The accelerated filler check has exactly the exhaustive check's acceptance domain. -/
theorem checkFillerRowsWithHints_eq {κ : ℕ} (hκ : κ < 64) (prog : Program)
    (image : MemImage κ) (hints : List (Fin (2 ^ κ))) (starts : List (Regs K)) :
    checkFillerRowsWithHints prog image hints starts = checkFillerRows prog image starts := by
  unfold checkFillerRowsWithHints checkFillerRows
  rw [show stepWithHints prog image hints = stepChecked prog image from
    funext (stepWithHints_eq hκ _ _ _)]

end
end LeanerVM.Semantics
