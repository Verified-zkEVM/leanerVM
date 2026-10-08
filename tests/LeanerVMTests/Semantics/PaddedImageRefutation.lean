import LeanerVM.Semantics.FillCycle
import LeanerVM.Semantics.FillerRows
import LeanerVMTests.Semantics.FillBlocks

/-!
# Layer 10 tests: the blueprint's completeness fails on the image

`constraintCompleteness` as the blueprint states it takes a valid execution `t` and asks for a
witness whose image is `t`'s. `ValidExecution` pins the image only where the run reads and at
`g^0`, `g^1`, and the padding rows of every table read and write cells of that same image. Here is
a valid execution of well formed bytecode whose image admits no `XOR` step at any registers or
operands: the five words it holds are linearly independent over `GF(2)`, so none is the sum of two.

The `XOR` table must have a row (`Caps.heights` gives `2^τ ≥ 1` rows) and a row of it is a step by
Layer 6 soundness and `mem_channel_sound`. That last implication is Layer 9's, blocked, and is
argued here and not checked: what is checked is the semantic obstruction, that no `XOR` step exists
on this image, and that the repository's own `FillerRowsValid` fails on any filler row that fetches
an `XOR`. The corrected target (`Trace.PaddedFrom`, `Trace.Fits`) gives the fill frames the room
they need above the image.

The image has the public words `y` and `x·y`, the `JUMP` operand cells `(d, d)` and `1`, and `y²`
everywhere else; the program is the ladder program with its first slot replaced by `JUMP [g^2, g^2,
g^3]` to the sentinel, so every block of the ladder is still there.
-/

namespace LeanerVMTests.Semantics.PaddedImageRefutation

open LeanerVM.Parameters LeanerVM.Semantics
open LeanerVMTests.Semantics.FillBlocks

/-- The sentinel counter of a `2^11`-slot program, as a literal term. The elaborator unifies two
`K` terms by evaluating powers of `g`, so it is never a definition (status finding E8). -/
local notation "d₀" => (gpow 2047 : K)

/-- Reading the address of a literal index gives the cell at that index. -/
theorem read_lit {κ : ℕ} (L : MemImage κ) (j : ℕ) (hκ : κ < 64 := by decide)
    (hj : j < 2 ^ κ := by decide) : L.read (gpow j) = some (L ⟨j, hj⟩) :=
  MemImage.read_gpow hκ L ⟨j, hj⟩

/-! ## The image -/

/-- `y`, the first public word. -/
def wA : E := E.ofLimbs 0 1 0

/-- `x·y`, the second public word (`K.ofBits 2` is `x`). -/
def wB : E := E.ofLimbs 0 (K.ofBits 2) 0

/-- `y²`, the filler word. -/
def vS : E := E.ofLimbs 0 0 1

/-- The five words the image holds, for the sentinel counter `d`. -/
def S (d : K) : List E := [wA, wB, ofK d, ofK 1, vS]

/-- No word of `S` is the sum of two words of `S`: the five words are linearly independent over
`GF(2)`. Checked in the kernel on the `5^3` triples. -/
theorem S_sumfree_bool :
    (S d₀).all (fun x ↦ (S d₀).all (fun y ↦ (S d₀).all (fun z ↦ decide (z ≠ x + y)))) = true := by
  decide +kernel

/-- No word of the five is the sum of two of them. -/
theorem S_sumfree : ∀ x ∈ S d₀, ∀ y ∈ S d₀, ∀ z ∈ S d₀, z ≠ x + y := by
  intro x hx y hy z hz
  have := S_sumfree_bool
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this x hx y hy z hz

/-- The sentinel counter of a `2^11`-slot program is not `1`. -/
theorem d₀_ne_one : d₀ ≠ 1 := by decide +kernel

/-- The sentinel counter of a `2^11`-slot program is not `0`. -/
theorem d₀_ne_zero : d₀ ≠ 0 := by decide +kernel

/-- The image: the two public words, the `JUMP` operand cells `(d, d)` and `1`, and `y²`
everywhere else. -/
def badImage (d : K) : MemImage minLogMem := fun i ↦
  match (i : ℕ) with
  | 0 => wA
  | 1 => wB
  | 2 => ofK d
  | 3 => ofK 1
  | _ => vS

/-- Every cell of the image is one of the five words. -/
theorem badImage_mem (d : K) (i : Fin (2 ^ minLogMem)) : badImage d i ∈ S d := by
  obtain ⟨i, hi⟩ := i
  unfold badImage
  match i, hi with
  | 0, _ => simp [S]
  | 1, _ => simp [S]
  | 2, _ => simp [S]
  | 3, _ => simp [S]
  | n + 4, _ => simp [S]

/-- The public input whose words are the first two cells. -/
def badInput : PublicInput := ⟨![0, 1, 0, K.ofBits 2]⟩

/-! ## No `XOR` instruction steps on this image -/

/-- On an image where no word is the sum of two words, no `XOR` executes, whatever the operands and
registers. -/
theorem no_xor_execute {κ : ℕ} (hκ : κ < 64) (L : MemImage κ)
    (hL : ∀ i j k, L k ≠ L i + L j) (r : Regs K) (oA oB oC : K) :
    execute L r (.xor oA oB oC) = none := by
  unfold execute executeWith
  rcases hA : L.read (r.fp * oA) with _ | vA
  · simp [hA]
  rcases hB : L.read (r.fp * oB) with _ | vB
  · simp [hA, hB]
  rcases hC : L.read (r.fp * oC) with _ | vC
  · simp [hA, hB, hC]
  obtain ⟨i, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hA
  obtain ⟨j, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hB
  obtain ⟨k, -, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hC
  simp [hA, hB, hC, hL i j k]

/-- No `XOR` executes on the image, at any registers and operands. -/
theorem badImage_no_xor (r : Regs K) (oA oB oC : K) :
    execute (badImage d₀) r (.xor oA oB oC) = none :=
  no_xor_execute (by decide) (badImage d₀)
    (fun i j k ↦ S_sumfree _ (badImage_mem d₀ i) _ (badImage_mem d₀ j) _ (badImage_mem d₀ k))
    r oA oB oC

/-- The all-zero image. -/
def zeroImage : MemImage minLogMem := fun _ ↦ 0

/-- Control: the sum-free hypothesis is what blocks the step. On the all-zero image, where
`0 = 0 + 0`, an `XOR` of three cells executes. -/
theorem zeroImage_xor :
    execute zeroImage ⟨gpow 5, 1⟩ (.xor (gpow 0) (gpow 0) (gpow 0)) =
      some (Regs.next ⟨gpow 5, 1⟩) := by
  have h : zeroImage.read (((⟨gpow 5, 1⟩ : Regs K).fp) * gpow 0) = some 0 := by
    show zeroImage.read (1 * gpow 0) = some 0
    rw [one_mul]
    exact read_lit zeroImage 0
  exact executeWith_xor_of_reads h h h (add_zero 0).symm

/-- So no state whose instruction is an `XOR` steps, in any program. -/
theorem badImage_no_xor_step (prog : Program) (r : Regs K) (oA oB oC : K)
    (h : prog.fetch r.pc = some (.xor oA oB oC)) : step prog (badImage d₀) r = none := by
  rw [step_of_fetch_eq_some h]
  exact badImage_no_xor r oA oB oC

/-- Hence no collection of filler rows with an `XOR` start is valid on this image: the
repository's own filler predicate fails. -/
theorem badImage_fillers_invalid (prog : Program) (starts : List (Regs K)) (r : Regs K)
    (hr : r ∈ starts) (oA oB oC : K) (h : prog.fetch r.pc = some (.xor oA oB oC)) :
    ¬ FillerRowsValid prog (badImage d₀) starts := by
  intro hv
  obtain ⟨next, -, hn⟩ := hv.step_mem hr
  rw [badImage_no_xor_step prog r oA oB oC h] at hn
  exact absurd hn (by simp)

/-! ## The trace is valid -/

theorem bad_run (prog : Program) (d : K) (hd : prog.finalPc = d) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (h0 : prog.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3))) :
    run prog (badImage d) 1 Regs.initial = some (Regs.final prog) := by
  have hne : (Regs.initial : Regs K).pc ≠ prog.finalPc := by
    rw [hd]; exact fun h ↦ hd1 h.symm
  have e2 : (badImage d).read (gpow 2) = some (ofK d) := by
    rw [read_lit (badImage d) 2]; rfl
  have e3 : (badImage d).read (gpow 3) = some (ofK 1) := by
    rw [read_lit (badImage d) 3]; rfl
  have hin : IsInK (ofK d) := (isInK_iff _).mpr ⟨d, rfl⟩
  have hin1 : IsInK (ofK (1 : K)) := (isInK_iff _).mpr ⟨1, rfl⟩
  have hne0 : ofK d ≠ 0 := by
    intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simp only [limb_ofK, limb_zero] at this
    exact hd0 this
  rw [run_succ_of_ne hne, step_of_fetch_eq_some (r := Regs.initial) h0]
  show (execute (badImage d) ⟨1, 1⟩ (.jump (gpow 2) (gpow 2) (gpow 3))) >>= _ = _
  simp only [execute, executeWith, one_mul, e2, e3]
  have hin1' : IsInK (1 : E) := by simpa using hin1
  have hl1 : (1 : E).limb 0 = 1 := by simpa using limb_ofK (1 : K) 0
  simp [hin, hin1', hne0, limb_ofK, hl1, run_zero, Regs.final, hd]

/-- The image holds the public words at `g^0` and `g^1`. -/
theorem bad_boundary {prog : Program} (d : K) (steps : ℕ) :
    HasPublicBoundary badInput (⟨minLogMem, badImage d, steps⟩ : Trace prog) := by
  refine ⟨le_rfl, (by decide : minLogMem ≤ maxLogMem), ?_, ?_⟩
  · rw [read_lit (badImage d) 0]; rfl
  · rw [read_lit (badImage d) 1]; rfl

/-- For every `2^11`-slot program whose first instruction is `JUMP [g^2, g^2, g^3]`, one step to
the sentinel is a valid execution on `badImage d₀`. -/
theorem bad_valid (prog : Program) (hL : prog.logSize = 11)
    (h0 : prog.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3))) :
    ValidExecution prog badInput (⟨minLogMem, badImage d₀, 1⟩ : Trace prog) := by
  have hfin : prog.finalPc = d₀ := by
    have h : 2 ^ prog.logSize - 1 = 2047 := by rw [hL]; norm_num
    unfold Program.finalPc
    rw [h]
  exact ⟨bad_boundary d₀ 1, bad_run prog d₀ hfin d₀_ne_zero d₀_ne_one h0⟩

/-! ## A well formed program with such a trace -/

/-- The ladder program with its first slot replaced by `JUMP [g^2, g^2, g^3]`: every block is
still there, and the sentinel slot is still a `SET_CONSTANT`. -/
def ladderJumpProg : Program :=
  ⟨11, by decide, fun i ↦
    if (i : ℕ) = 0 then .jump (gpow 2) (gpow 2) (gpow 3) else ladderCode i⟩

/-- Away from slot `0` the two programs agree. -/
theorem ladderJump_fetch (n : ℕ) (hn : n < 2048) (h0 : n ≠ 0) :
    ladderJumpProg.fetch (gpow n) = ladderProg.fetch (gpow n) := by
  rw [ladderJumpProg.fetch_gpow ⟨n, hn⟩, ladder_fetch n hn]
  congr 1
  simp only [ladderJumpProg, h0, ↓reduceIte]

/-- A block of the ladder that starts at slot `1` or later is a block of the changed program. -/
theorem ladderJump_isFillBlock {t : Opcode} {s p : ℕ} (h : IsFillBlock ladderProg t s p)
    (hp : 1 ≤ p) : IsFillBlock ladderJumpProg t s p := by
  have hb : p + s + 1 < 2 ^ 11 := h.below
  refine ⟨h.below, fun i hi ↦ ?_, ?_⟩
  · have := ladderJump_fetch (p + i) (by omega) (by omega)
    rw [this]
    exact h.dummies i hi
  · have := ladderJump_fetch (p + s) (by omega) (by omega)
    rw [this]
    exact h.close

/-- The changed program has every block. -/
theorem ladderJump_hasFillBlocks : HasFillBlocks ladderJumpProg := by
  intro t s hs
  obtain ⟨k, hk, ht⟩ : ∃ k, k < 6 ∧ tableOf k = t := by
    cases t
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩,
      ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩]
  simp only [fillSizes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 128 0 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 64 129 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 32 194 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 16 227 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 8 244 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 4 253 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 2 258 (by norm_num) (by decide)
      (by decide)) (by omega)⟩
  · exact ⟨_, ladderJump_isFillBlock (ladder_block t k hk ht 1 261 (by norm_num) (by decide)
      (by decide)) (by omega)⟩

/-- The changed program is well formed bytecode. -/
theorem ladderJump_wellFormed : WellFormedBytecode ladderJumpProg :=
  ⟨by decide, ladderJump_hasFillBlocks⟩

/-- Its first slot is the `JUMP`. -/
theorem ladderJump_fetch_one :
    ladderJumpProg.fetch 1 = some (.jump (gpow 2) (gpow 2) (gpow 3)) := by
  have h : ladderJumpProg.fetch (gpow 0) = some (ladderJumpProg.code ⟨0, by decide⟩) :=
    ladderJumpProg.fetch_gpow ⟨0, by decide⟩
  rw [show gpow 0 = (1 : K) from pow_zero g] at h
  rw [h]
  simp [ladderJumpProg]

/-- **The obstruction.** Well formed bytecode with a valid execution whose image admits no `XOR`
step at any registers or operands. The `XOR` table needs a row, and a row of it is a step (Layer 6
soundness and `mem_channel_sound`, Layer 9: argued, not checked), so no witness represents this
trace; the padding that completeness needs must add cells above the image. -/
theorem image_obstruction :
    WellFormedBytecode ladderJumpProg ∧
      ∃ (input : PublicInput) (t : Trace ladderJumpProg), ValidExecution ladderJumpProg input t ∧
        ∀ (r : Regs K) (oA oB oC : K), execute t.image r (.xor oA oB oC) = none :=
  ⟨ladderJump_wellFormed, badInput, ⟨minLogMem, badImage d₀, 1⟩,
    bad_valid ladderJumpProg rfl ladderJump_fetch_one, badImage_no_xor⟩

/-! ## The padding repairs it -/

/-- On the padded image of the same trace, the `XOR` fill cycle has a frame on which its dummy
steps: the corrected target gives the table the rows the image alone could not. -/
theorem padded_bad_xor_step :
    step ladderJumpProg (padImage (badImage d₀) (fun _ _ ↦ 1))
        ⟨gpow 1, gpow (frameBase minLogMem (8 * tableIdx .xor + 0))⟩ =
      some ⟨g * gpow 1, gpow (frameBase minLogMem (8 * tableIdx .xor + 0))⟩ := by
  have hb := ladderJump_isFillBlock
    (ladder_block .xor 0 (by norm_num) rfl 128 0 (by norm_num) (by decide) (by decide))
    (by omega)
  have hf : ladderJumpProg.fetch (gpow 1) = some (fillDummy .xor) := by
    simpa using hb.dummies 0 (by norm_num)
  exact fill_dummy_step (by decide) (by decide) (badImage d₀) (fun _ _ ↦ 1) .xor
    (k := 0) (by norm_num) hf

end LeanerVMTests.Semantics.PaddedImageRefutation
