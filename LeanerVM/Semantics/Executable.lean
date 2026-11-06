/-
  LeanerVM.Semantics.Executable

  The computable carrier of the fixed-image leanISA semantics: address search, the checked
  step, and the exact and fuel-bounded checkers, each proved equal to the reference.
-/

module

public import LeanerVM.Semantics.Execution

/-!
# The executable carrier

leanISA roadmap Layer 3 companion, at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`.
The reference semantics (`gLog?`, `MemImage.read`, `Program.fetch`, `execute`, `step`, `run`,
`ValidExecution`) is noncomputable and is what a reader audits. This module is its computable
carrier: one address search, `addressIndex`, replaces the chosen logarithm `gLog?`; the checked
step `stepChecked` is `executeWith` (the reference's six arms, `LeanerVM.Semantics.Step`) at the
carrier's reader; `checkWithinFuel` searches for the halting time within a budget and
`checkTrace` checks an announced one.

**What is trusted here is the statements of the equivalence theorems**, not the bodies:
`addressIndex_eq_gLog`, `readImage_eq_read`, `fetchInstruction_eq_fetch`,
`executeChecked_eq_execute`, `stepChecked_eq_step`, `runToHalt_eq_ok_iff`,
`checkBoundary_eq_true_iff`, `checkWithinFuel_eq_ok_iff`, `checkTrace_eq_true_iff`. Each says
that a carrier function agrees with the reference on every input (within the address bound
`κ < 64`, which every public entry point discharges from the caps `κ ≤ 32` and
`logSize ≤ 32`). The bodies may hold any speedup that keeps those theorems true.

**Hints and tables of powers.** Every carrier function takes an untrusted list of suggested cell
indices. A hint is used only after `gpow i = a` has been checked, and a miss falls back to the
exhaustive scan, so `addressIndex_eq_gLog` holds for every hint list: hints buy speed, never
trust. The scan carries `g ^ i` as a running product, one multiplication per candidate. The run
of `runToHalt` reads through a table of powers (`PowTable`: an array of powers, proved, and an
untrusted index of their words), seeded with the hints and grown along the run to the cells it
reaches (`stepTable`); a guess of the index is checked against the array, else the scan, so
`addressIndexBy_eq_gLog` holds for every table, and a run costs the powers up to the highest cell
it reads once, not a scan per read.

This is fixed-image validation of the reference ISA; it constructs no witness and says
nothing about a Rust executor's success domain.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Address search -/

/-- Retain only hint indices inside the address space, without truncation or modular
reduction. -/
def hintIndices (κ : ℕ) (hints : List ℕ) : List (Fin (2 ^ κ)) :=
  hints.filterMap fun i ↦ if h : i < 2 ^ κ then some ⟨i, h⟩ else none

/-- The exhaustive fallback: from index `i` with `cur = g ^ i`, compare `cur` with `a` and
advance by one multiplication, for at most `fuel` candidates; `none` past the address space. -/
def scan (κ : ℕ) (a : K) : ℕ → ℕ → K → Option (Fin (2 ^ κ))
  | 0, _, _ => none
  | fuel + 1, i, cur =>
    if h : i < 2 ^ κ then
      if cur = a then some ⟨i, h⟩ else scan κ a fuel (i + 1) (g * cur)
    else none

/-- The index of address `a`: the first hint `i` with `g ^ i = a`, else the scan from index
`0` over the whole address space. -/
def addressIndex (κ : ℕ) (hints : List (Fin (2 ^ κ))) (a : K) : Option (Fin (2 ^ κ)) :=
  match hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | some i => some i
  | none => scan κ a (2 ^ κ) 0 1

/-- Read a fixed image through `addressIndex`. -/
def readImage {κ : ℕ} (image : MemImage κ) (hints : List ℕ) (a : K) : Option E :=
  (addressIndex κ (hintIndices κ hints) a).map image

/-- Fetch the typed instruction at a bounded program address; the hints are range-checked
again against the program size. -/
def fetchInstruction (prog : Program) (hints : List ℕ) (pc : K) : Option Instr :=
  (addressIndex prog.logSize (hintIndices prog.logSize hints) pc).map prog.code

/-! ## Checked guesses -/

/-- The machine word of a field element, the key of a guess table. -/
def wordKey (a : K) : UInt64 := UInt64.ofBitVec a.toBitVec

/-- A table of powers of `g`: the powers `g ^ i`, `i < pows.size`, in an array (proved), and an
untrusted index of words. -/
structure PowTable where
  /-- The powers `g ^ 0, g ^ 1, …`. -/
  pows : Array K
  /-- Entry `i` is `g ^ i`. -/
  pows_eq : ∀ i (h : i < pows.size), pows[i] = gpow i
  /-- The guessed index of a word, by its machine word. Untrusted: every guess is checked. -/
  index : Std.HashMap UInt64 ℕ

/-- The power `g ^ i`, from the array when it holds it. -/
def PowTable.pow (P : PowTable) (i : ℕ) : K :=
  if h : i < P.pows.size then P.pows[i] else gpow i

/-- The tabulated power is the power. -/
theorem PowTable.pow_eq (P : PowTable) (i : ℕ) : P.pow i = gpow i := by
  unfold PowTable.pow
  split_ifs with h
  · exact P.pows_eq i h
  · rfl

/-- The guess the table makes for a word. -/
def PowTable.guess (P : PowTable) (a : K) : Option ℕ := P.index[wordKey a]?

/-- The index of address `a` from an untrusted guess: the guessed index `i` when it is inside the
address space and `g ^ i = a` (read from the table), else the scan from index `0`. -/
def addressIndexBy (κ : ℕ) (P : PowTable) (a : K) : Option (Fin (2 ^ κ)) :=
  match P.guess a with
  | some i => if h : i < 2 ^ κ ∧ P.pow i = a then some ⟨i, h.1⟩ else scan κ a (2 ^ κ) 0 1
  | none => scan κ a (2 ^ κ) 0 1

/-- Read a fixed image through `addressIndexBy`. -/
def readBy {κ : ℕ} (image : MemImage κ) (P : PowTable) (a : K) : Option E :=
  (addressIndexBy κ P a).map image

/-- Fetch the typed instruction at a program address through `addressIndexBy`. -/
def fetchBy (prog : Program) (P : PowTable) (pc : K) : Option Instr :=
  (addressIndexBy prog.logSize P pc).map prog.code

/-- The limbs of the word a reader holds at `a`, zero when there is none: `MemImage.limbsAt` at
any reader. -/
def limbsBy (rd : K → Option E) (a : K) : Vector K 3 :=
  match rd a with
  | some v => #v[v.limb 0, v.limb 1, v.limb 2]
  | none => #v[0, 0, 0]

/-- The two limbs of the word a reader holds at `a`, zero when there is none: `MemImage.cellAt` at
any reader. -/
def cellBy (rd : K → Option E) (a : K) : Vector K 2 :=
  match rd a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-- The powers `g ^ i` for `i` from `acc.size` on, `n` of them, appended to `acc` from the running
product `cur`. -/
def powsFrom : ℕ → K → Array K → Array K
  | 0, _, acc => acc
  | n + 1, cur, acc => powsFrom n (g * cur) (acc.push cur)

/-- The index of the powers `pows[i]`, `i ≥ j`, `n` of them, inserted into `m`. -/
def indexFrom (pows : Array K) : ℕ → ℕ → Std.HashMap UInt64 ℕ → Std.HashMap UInt64 ℕ
  | 0, _, m => m
  | n + 1, j, m => indexFrom pows n (j + 1) (m.insert (wordKey (pows.getD j 0)) j)

/-- The running product appends the powers. -/
theorem powsFrom_spec : ∀ (n : ℕ) (cur : K) (acc : Array K), cur = gpow acc.size →
    (∀ i (h : i < acc.size), acc[i] = gpow i) →
    ∀ i (h : i < (powsFrom n cur acc).size), (powsFrom n cur acc)[i] = gpow i := by
  intro n
  induction n with
  | zero => intro cur acc _ hacc; exact hacc
  | succ n ih =>
    intro cur acc hcur hacc
    refine ih (g * cur) (acc.push cur) (by rw [hcur, Array.size_push, gpow_succ]) ?_
    intro i hi
    rw [Array.getElem_push]
    split_ifs with h
    · exact hacc i h
    · rw [hcur]
      congr 1
      rw [Array.size_push] at hi
      omega

/-- The table of the powers `g ^ i`, `i < n`. -/
def powTable (n : ℕ) : PowTable :=
  let pows := powsFrom n 1 (Array.mkEmpty n)
  ⟨pows, powsFrom_spec n 1 _ (by simp) (by simp),
    indexFrom pows n 0 (Std.HashMap.emptyWithCapacity n)⟩

/-- The cells an instruction reads at frame `fp`, in the circuit's order, at a reader: the second
address of a `DEREF` is the word read at the first. -/
def readAddrsBy (rd : K → Option E) (fp : K) : Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (limbsBy rd (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .blake2s om ocv oout omd =>
      [fp * om 0, fp * om 1, fp * om 2, fp * om 3, fp * ocv, fp * (g * ocv), fp * oout,
        fp * (g * oout), fp * omd]

/-- Appending `g ^ pows.size` keeps an array of powers. -/
theorem pows_push_spec {pows : Array K} (hp : ∀ i (h : i < pows.size), pows[i] = gpow i)
    {cur : K} (h : cur = gpow pows.size) :
    ∀ i (hi : i < (pows.push cur).size), (pows.push cur)[i] = gpow i := by
  intro i hi
  rw [Array.getElem_push]
  split_ifs with h'
  · exact hp i h'
  · rw [h]
    congr 1
    rw [Array.size_push] at hi
    omega

/-- The table with the next power `cur = g ^ n` at index `n`, its size. The index is updated
before the array, so that the array is no longer read once pushed and is pushed in place. -/
def PowTable.push : (P : PowTable) → (cur : K) → cur = gpow P.pows.size → PowTable
  | ⟨pows, hp, index⟩, cur, h =>
    let index := index.insert (wordKey cur) pows.size
    ⟨pows.push cur, pows_push_spec hp h, index⟩

/-- Pushing adds one power. -/
theorem PowTable.push_size (P : PowTable) (cur : K) (h : cur = gpow P.pows.size) :
    (P.push cur h).pows.size = P.pows.size + 1 := by
  cases P
  simp [PowTable.push]

/-- Push the powers from `cur = g ^ P.pows.size` on, at most `fuel` of them, stopping after `a`. -/
def PowTable.extendLoop (a : K) :
    ℕ → (P : PowTable) → (cur : K) → cur = gpow P.pows.size → PowTable
  | 0, P, _, _ => P
  | fuel + 1, P, cur, h =>
    if cur = a then P.push cur h
    else PowTable.extendLoop a fuel (P.push cur h) (g * cur)
      (by rw [PowTable.push_size, gpow_succ, h])

/-- Whether the index guesses for `a` a power the array holds. -/
def PowTable.holds (P : PowTable) (a : K) : Bool :=
  match P.guess a with
  | some i => if h : i < P.pows.size then P.pows[i] == a else false
  | none => false

/-- The table extended by powers until it holds `a`, to at most `n` powers; unchanged when its
array already holds `a`, and for `0`, which is no power. -/
def PowTable.extendTo (n : ℕ) (P : PowTable) (a : K) : PowTable :=
  if a = 0 ∨ P.holds a = true then P
  else P.extendLoop a (n - P.pows.size) (P.pow P.pows.size) (P.pow_eq _)

/-- The table extended until it holds each of `as`. -/
def PowTable.extendAll (n : ℕ) (P : PowTable) (as : List K) : PowTable :=
  as.foldl (PowTable.extendTo n) P

/-- The table with no powers whose index guesses the hinted indices. -/
def PowTable.ofHints (hints : List ℕ) : PowTable :=
  ⟨#[], by simp, hints.foldl (fun m i ↦ m.insert (wordKey (gpow i)) i) ∅⟩

/-! ## The checked step -/

/-- One instruction at the carrier's reader: the reference arms `executeWith`, nothing else. -/
def executeChecked {κ : ℕ} (image : MemImage κ) (hints : List ℕ) (r : Regs K) :
    Instr → Option (Regs K) :=
  executeWith (readImage image hints) r

/-- Fetch and check one step. Halting remains the responsibility of the loop. -/
def stepChecked {κ : ℕ} (prog : Program) (image : MemImage κ) (hints : List ℕ) (r : Regs K) :
    Option (Regs K) :=
  fetchInstruction prog hints r.pc >>= executeChecked image hints r

/-- One step through a table of powers of at most `n` entries, the table extended first by the
program counter and the cells the instruction reads, so that each guess is likely a hit; the
extended table and the next state. -/
def stepTable {κ : ℕ} (prog : Program) (image : MemImage κ) (n : ℕ) (P : PowTable)
    (r : Regs K) : PowTable × Option (Regs K) :=
  let P := P.extendTo n r.pc
  match fetchBy prog P r.pc with
  | none => (P, none)
  | some ins =>
    let P := P.extendAll n (readAddrsBy (fun _ ↦ none) r.fp ins)
    let P := P.extendAll n (readAddrsBy (readBy image P) r.fp ins)
    (P, executeWith (readBy image P) r ins)

/-! ## Bounded checking -/

/-- Failure modes of bounded execution checking. Exhausting fuel makes no claim that a
longer run is invalid; the other cases identify failed semantic or public-boundary checks. -/
inductive CheckError
  | publicBoundary
  | invalidStep
  | finalFrame
  | fuelExhausted
  deriving DecidableEq, Repr

/-- Run to the sentinel in at most `fuel` transitions, reading through a table of powers of at
most `n` entries that grows as the run reaches new addresses. -/
def runToHaltBy {κ : ℕ} (prog : Program) (image : MemImage κ) (n : ℕ) :
    ℕ → PowTable → Regs K → Except CheckError ℕ
  | fuel, P, r =>
    if r.pc = prog.finalPc then
      if r.fp = 1 then .ok 0 else .error .finalFrame
    else match fuel with
      | 0 => .error .fuelExhausted
      | fuel + 1 =>
        let st := stepTable prog image n P r
        match st.2 with
        | none => .error .invalidStep
        | some next => (runToHaltBy prog image n fuel st.1 next).map (· + 1)

/-- Run to the sentinel in at most `fuel` transitions. The result counts only main-run
steps; no filler rows are appended. At zero fuel an already halted state
succeeds, while a nonterminal state reports exhaustion. Addresses are read through a table of
powers grown along the run from the hints (`runToHaltBy`), so each new cell costs the powers up to
it once, not a scan per read. -/
def runToHalt {κ : ℕ} (prog : Program) (image : MemImage κ) (hints : List ℕ) (fuel : ℕ)
    (r : Regs K) : Except CheckError ℕ :=
  runToHaltBy prog image (2 ^ max κ prog.logSize) fuel (PowTable.ofHints hints) r

/-- The executable checks of the memory-size window and the two public words. -/
def checkBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Bool :=
  decide (minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem) &&
    decide (readImage t.image [] (gpow 0) = some input.word0 ∧
      readImage t.image [] (gpow 1) = some input.word1)

/-- Check public memory and find a valid exact main-run length within the supplied fuel.
The image is preserved verbatim; the returned count can be used in `Trace`. -/
def checkWithinFuel {κ : ℕ} (prog : Program) (input : PublicInput) (image : MemImage κ)
    (fuel : ℕ) (hints : List ℕ := []) : Except CheckError ℕ :=
  if checkBoundary input (⟨κ, image, 0⟩ : Trace prog) then
    runToHalt prog image hints fuel Regs.initial
  else .error .publicBoundary

/-- Validate a claimed exact-length execution, including its public memory and final frame:
the bounded search with the announced count as its budget must halt at exactly that count.
A successful witness generator must still establish that its output passes this check. -/
def checkTrace (prog : Program) (input : PublicInput) (t : Trace prog)
    (hints : List ℕ := []) : Bool :=
  decide (checkWithinFuel prog input t.image t.steps hints = .ok t.steps)

/-! ## Refinement to the reference semantics -/

/-- A hit of the scan is genuine: from `cur = g ^ i`, `some j` means `a = g ^ j`. -/
theorem scan_eq_some {κ : ℕ} {a : K} (fuel i : ℕ) {j : Fin (2 ^ κ)}
    (h : scan κ a fuel i (gpow i) = some j) : a = gpow j := by
  induction fuel generalizing i with
  | zero => exact nomatch h
  | succ fuel ih =>
    unfold scan at h
    by_cases hi : i < 2 ^ κ
    · rw [dite_eq_left hi] at h
      by_cases ha : gpow i = a
      · rw [ite_eq_left ha] at h
        cases h
        exact ha.symm
      · rw [ite_eq_right ha, ← gpow_succ] at h
        exact ih (i + 1) h
    · rw [dite_eq_right hi] at h
      exact nomatch h

/-- A miss of the scan is genuine: from `cur = g ^ i`, `none` means no index in the window
`[i, i + fuel)` addresses `a`. -/
theorem scan_eq_none {κ : ℕ} {a : K} (fuel i : ℕ) (h : scan κ a fuel i (gpow i) = none)
    (j : Fin (2 ^ κ)) (hij : i ≤ j) (hj : (j : ℕ) < i + fuel) : a ≠ gpow j := by
  induction fuel generalizing i with
  | zero => intro _; omega
  | succ fuel ih =>
    unfold scan at h
    by_cases hi : i < 2 ^ κ
    · rw [dite_eq_left hi] at h
      by_cases ha : gpow i = a
      · rw [ite_eq_left ha] at h
        exact nomatch h
      · rw [ite_eq_right ha, ← gpow_succ] at h
        intro haj
        rcases Nat.eq_or_lt_of_le hij with hij' | hij'
        · apply ha
          rw [hij']
          exact haj.symm
        · exact ih (i + 1) h hij' (by omega) haj
    · exact absurd (lt_of_le_of_lt hij j.isLt) hi

/-- The address search agrees with the reference logarithm for every hint list, whenever the
address representation is injective on the selected domain. -/
theorem addressIndex_eq_gLog {κ : ℕ} (hκ : κ < 64) (hints : List (Fin (2 ^ κ))) (a : K) :
    addressIndex κ hints a = gLog? κ a := by
  unfold addressIndex
  cases hf : hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | some i =>
    have hgi : decide (gpow (i : ℕ) = a) = true :=
      List.find?_some (p := fun j : Fin (2 ^ κ) ↦ decide (gpow j = a)) hf
    exact ((gLog?_spec hκ).mpr (of_decide_eq_true hgi).symm).symm
  | none =>
    have h1 : (1: K) = gpow 0 := (pow_zero g).symm
    cases hs : scan κ a (2 ^ κ) 0 1 with
    | some j =>
      rw [h1] at hs
      exact ((gLog?_spec hκ).mpr (scan_eq_some _ _ hs)).symm
    | none =>
      rw [h1] at hs
      symm
      rw [gLog?_eq_none_iff]
      intro j
      exact scan_eq_none _ _ hs j (Nat.zero_le _) (by have := j.isLt; omega)

/-- Executable reads preserve success, failure, and the exact word returned. -/
theorem readImage_eq_read {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (hints : List ℕ)
    (a : K) : readImage image hints a = image.read a := by
  rw [readImage, MemImage.read, addressIndex_eq_gLog hκ]

/-- Executable fetch agrees with typed reference fetch on every field address. -/
theorem fetchInstruction_eq_fetch (prog : Program) (hints : List ℕ) (pc : K) :
    fetchInstruction prog hints pc = prog.fetch pc := by
  have hκ : prog.logSize < 64 := lt_of_le_of_lt prog.logSize_le (by decide)
  rw [fetchInstruction, Program.fetch, addressIndex_eq_gLog hκ]

/-- The checked instruction is the reference instruction: the same arms, an equal reader. -/
theorem executeChecked_eq_execute {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (hints : List ℕ)
    (r : Regs K) : executeChecked image hints r = execute image r := by
  unfold executeChecked execute
  rw [show readImage image hints = image.read from funext (readImage_eq_read hκ image hints)]

/-- The checked program step has exactly the reference step's behavior. -/
theorem stepChecked_eq_step {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (hints : List ℕ) (r : Regs K) : stepChecked prog image hints r = step prog image r := by
  unfold stepChecked step
  rw [fetchInstruction_eq_fetch, executeChecked_eq_execute hκ]

/-- A guess is used only when it is checked, so the guessed search is the reference logarithm
for every table, whatever its index guesses. -/
theorem addressIndexBy_eq_gLog {κ : ℕ} (hκ : κ < 64) (P : PowTable) (a : K) :
    addressIndexBy κ P a = gLog? κ a := by
  have hscan : scan κ a (2 ^ κ) 0 1 = gLog? κ a := addressIndex_eq_gLog hκ [] a
  unfold addressIndexBy
  split
  · split_ifs with h
    · exact ((gLog?_spec hκ).mpr ((P.pow_eq _).symm.trans h.2).symm).symm
    · exact hscan
  · exact hscan

/-- Guessed reads are the reference reads. -/
theorem readBy_eq_read {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (P : PowTable)
    (a : K) : readBy image P a = image.read a := by
  rw [readBy, MemImage.read, addressIndexBy_eq_gLog hκ]

/-- Guessed fetches are the reference fetches. -/
theorem fetchBy_eq_fetch (prog : Program) (P : PowTable) (pc : K) :
    fetchBy prog P pc = prog.fetch pc := by
  have hκ : prog.logSize < 64 := lt_of_le_of_lt prog.logSize_le (by decide)
  rw [fetchBy, Program.fetch, addressIndexBy_eq_gLog hκ]

/-- The limbs at the reference reader are `MemImage.limbsAt`. -/
theorem limbsBy_read {κ : ℕ} (L : MemImage κ) : limbsBy L.read = L.limbsAt := rfl

/-- The cell at the reference reader is `MemImage.cellAt`. -/
theorem cellBy_read {κ : ℕ} (L : MemImage κ) : cellBy L.read = L.cellAt := rfl

/-- Execution at a guessed reader is the reference execution. -/
theorem executeWith_readBy {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (P : PowTable) :
    executeWith (readBy image P) = execute image := by
  funext r ins
  rw [execute, show readBy image P = image.read from funext (readBy_eq_read hκ image P)]

/-- The table-driven step is the reference step, whatever the table. -/
theorem stepTable_snd {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ) (n : ℕ)
    (P : PowTable) (r : Regs K) : (stepTable prog image n P r).2 = step prog image r := by
  unfold stepTable step
  simp only [fetchBy_eq_fetch]
  cases prog.fetch r.pc with
  | none => rfl
  | some ins => simp only [executeWith_readBy hκ]; rfl

/-- The table-driven run succeeds exactly on the reference executions within the budget, whatever
the table. -/
theorem runToHaltBy_eq_ok_iff {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (m fuel n : ℕ) (P : PowTable) (r : Regs K) :
    runToHaltBy prog image m fuel P r = .ok n ↔
      n ≤ fuel ∧ run prog image n r = some (Regs.final prog) := by
  induction fuel generalizing r n P with
  | zero =>
    rw [runToHaltBy]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n <;> simp
    · have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
      cases n <;> simp [hr]
    · have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
      cases n <;> simp [hr]
  | succ fuel ih =>
    rw [runToHaltBy]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n with
      | zero => simp
      | succ n => simp [run_succ_of_eq hpc]
    · cases n with
      | zero =>
        have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
        simp [hr]
      | succ n => simp [run_succ_of_eq hpc]
    · simp only [stepTable_snd hκ]
      cases hs : step prog image r with
      | none =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          simp [hr]
        | succ n => simp [run_succ_of_ne hpc, hs]
      | some next =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          cases he : runToHaltBy prog image m fuel (stepTable prog image m P r).1 next <;>
            simp [he, Except.map, hr]
        | succ n =>
          have hm : (runToHaltBy prog image m fuel (stepTable prog image m P r).1 next).map
                (· + 1) = .ok (n + 1) ↔
              runToHaltBy prog image m fuel (stepTable prog image m P r).1 next = .ok n := by
            cases runToHaltBy prog image m fuel (stepTable prog image m P r).1 next <;>
              simp [Except.map]
          rw [hm, ih]
          simp only [Nat.add_le_add_iff_right, run_succ_of_ne hpc, hs, Option.bind_eq_bind,
            Option.bind_some]

/-- Every successful bounded check gives an exact reference execution of the reported
length, and every such execution within the budget is found. -/
theorem runToHalt_eq_ok_iff {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (hints : List ℕ) (fuel n : ℕ) (r : Regs K) :
    runToHalt prog image hints fuel r = .ok n ↔
      n ≤ fuel ∧ run prog image n r = some (Regs.final prog) :=
  runToHaltBy_eq_ok_iff hκ prog image _ fuel n _ r

/-- Boundary checking is equivalent to the reference public boundary, including size caps. -/
theorem checkBoundary_eq_true_iff {prog : Program} (input : PublicInput) (t : Trace prog) :
    checkBoundary input t = true ↔ HasPublicBoundary input t := by
  simp only [checkBoundary, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hmin, hmax⟩, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ] at hwords
    exact ⟨hmin, hmax, hwords⟩
  · rintro ⟨hmin, hmax, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ]
    exact ⟨⟨hmin, hmax⟩, hwords⟩

/-- The public bounded checker accepts exactly valid executions whose length fits the
budget, for every hint list. This theorem also excludes oversized images and wrong public
words. -/
theorem checkWithinFuel_eq_ok_iff {κ : ℕ} (prog : Program) (input : PublicInput)
    (image : MemImage κ) (fuel n : ℕ) (hints : List ℕ) :
    checkWithinFuel prog input image fuel hints = .ok n ↔
      n ≤ fuel ∧ ValidExecution prog input ⟨κ, image, n⟩ := by
  unfold checkWithinFuel
  split_ifs with hb
  · have hb' := (checkBoundary_eq_true_iff input _).mp hb
    have hκ : κ < 64 := lt_of_le_of_lt hb'.2.1 (by decide)
    rw [runToHalt_eq_ok_iff hκ]
    simp only [ValidExecution, show HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog)
      from hb', true_and]
  · have hb' : ¬ HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog) := by
      intro h
      exact hb ((checkBoundary_eq_true_iff input _).mpr h)
    simp [ValidExecution, hb']

/-- Exact checking accepts precisely the valid reference executions, for every hint list.
The equivalence is unconditional: the checker itself rejects sizes outside the public
boundary. -/
theorem checkTrace_eq_true_iff (prog : Program) (input : PublicInput) (t : Trace prog)
    (hints : List ℕ) : checkTrace prog input t hints = true ↔ ValidExecution prog input t := by
  rw [checkTrace, decide_eq_true_iff, checkWithinFuel_eq_ok_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨le_rfl, h⟩⟩

end
end LeanerVM.Semantics
