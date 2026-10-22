/-
  LeanVM.E2E.Complete.Rom.Pad

  T6-prob, recursion: the honest execution padded to a committed size above `2^21`, so that its
  stack has at least `22` variables, the guest's floor on a child's stack (`End.Limits.stackLog`).
-/

module

public import LeanVM.E2E.Complete.Rom.Chooser

/-!
# Padding the memory

leanVM's prover pads the memory of a run with zero cells until the stacked witness reaches the
aggregation's floor `MU_MIN = 22` (`leanvm_core/src/cpu/execute.rs:909-918`, `min_log_committed`
set at `rec_aggregation/src/aggregation.rs:2231`). Here:

* `padImage κ' L`: the memory `L` of `2^κ` words zero-extended to `2^κ'` words. Every read that
  succeeds on `L` succeeds on it with the same word (`padImage_read_of`), and every read with the
  default `0` is unchanged (`padImage_read_getD`).
* An execution on `L` is one on `padImage κ' L` with the same instruction counts
  (`runB_padImage`, `runCountB_padImage`), so its committed size grows by `4 (2^κ' − 2^κ)` only.
* `exists_padded`: a valid execution of committed size at most `2^28` gives one of committed size
  in `(2^21, 2^28]`, reading the same words with default `0` (unpadded when already above
  `2^21`, else padded to `κ' = 19`).
* `exists_stack_total`: `exists_stack_of_validB` with the stack's blocks' total the committed size,
  so a committed size above `2^21` gives `22 ≤ leanIsaμ` (`le_leanIsaμ_of_total`).
* `decodeHonest_leaf_of_getD`: a node without children decodes (`DecodeHonest`) on any memory
  reading the same words with default `0`: V_I's decoder reads the number of children from
  `main`'s frame by `wd`.
* **`nodeExec_nodeLog_big`**: a node without children, valid and within the limits, has an
  execution on its own log's strings whose stack has at least 22 variables.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Arithmetization LeanVM.Protocol.Compile.Rom
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The zero-extended memory -/

/-- The memory `L` zero-extended to `2^κ'` words. -/
noncomputable def padImage {κ : ℕ} (κ' : ℕ) (L : MemImage κ) : MemImage κ' :=
  fun i ↦ if h : (i : ℕ) < 2 ^ κ then L ⟨i, h⟩ else 0

/-- A read that succeeds on `L` succeeds on its extension with the same word. -/
theorem padImage_read_of {κ κ' : ℕ} (hκ' : κ' < 64) (hle : κ ≤ κ') {L : MemImage κ} {a : K}
    {v : E} (h : L.read a = some v) : (padImage κ' L).read a = some v := by
  have hκ : κ < 64 := by omega
  obtain ⟨i, rfl, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp h
  have hi : (i : ℕ) < 2 ^ κ' := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hle)
  have := MemImage.read_gpow hκ' (padImage κ' L) ⟨i, hi⟩
  simpa [padImage, i.isLt] using this

/-- **Reads with default `0` are unchanged** by the extension. -/
theorem padImage_read_getD {κ κ' : ℕ} (hκ' : κ' < 64) (hle : κ ≤ κ') (L : MemImage κ) (a : K) :
    ((padImage κ' L).read a).getD 0 = (L.read a).getD 0 := by
  cases h : L.read a with
  | some v => rw [padImage_read_of hκ' hle h]
  | none =>
    cases h' : (padImage κ' L).read a with
    | none => rfl
    | some v =>
      obtain ⟨j, rfl, rfl⟩ := (MemImage.read_eq_some_iff hκ' _).mp h'
      have hn := (MemImage.read_eq_none_iff L).mp h
      simp only [Option.getD_some, Option.getD_none, padImage]
      split_ifs with hj
      · exact absurd rfl (hn ⟨j, hj⟩)
      · rfl

/-! ## Executions on the extension -/

/-- An instruction executing on a reader executes alike on any reader extending it. -/
theorem executeWithB_of_ext {S : BlakeSem} {rd rd2 : K → Option E}
    (hrd : ∀ a v, rd a = some v → rd2 a = some v) {r r2 : Regs K} {i : Instr}
    (h : executeWithB S rd r i = some r2) : executeWithB S rd2 r i = some r2 := by
  cases i <;> simp only [executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  all_goals
    repeat (obtain ⟨x, h1, h⟩ := h; first | refine ⟨x, hrd _ _ h1, ?_⟩ | refine ⟨x, h1, ?_⟩)
  all_goals exact h

theorem stepB_of_ext {S : BlakeSem} {prog : Program} {κ κ' : ℕ} {L : MemImage κ}
    {L' : MemImage κ'} (hrd : ∀ a v, L.read a = some v → L'.read a = some v) {r r2 : Regs K}
    (h : stepB S prog L r = some r2) : stepB S prog L' r = some r2 := by
  unfold stepB at h ⊢
  obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hi]
  exact executeWithB_of_ext hrd h

/-- **A run on `L` is a run on any memory extending it.** -/
theorem runB_of_ext {S : BlakeSem} {prog : Program} {κ κ' : ℕ} {L : MemImage κ}
    {L' : MemImage κ'} (hrd : ∀ a v, L.read a = some v → L'.read a = some v) :
    ∀ (n : ℕ) {r r2 : Regs K}, runB S prog L n r = some r2 → runB S prog L' n r = some r2
  | 0, r, r2, h => h
  | n + 1, r, r2, h => by
    unfold runB at h ⊢
    split_ifs at h ⊢ with hf
    obtain ⟨r1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [stepB_of_ext hrd h1]
    exact runB_of_ext hrd n h2

/-- **The instruction counts of a run are those on any memory extending it.** -/
theorem runCountB_of_ext {S : BlakeSem} {prog : Program} {κ κ' : ℕ} {L : MemImage κ}
    {L' : MemImage κ'} (hrd : ∀ a v, L.read a = some v → L'.read a = some v) (op : Opcode) :
    ∀ (n : ℕ) {r r2 : Regs K}, runB S prog L n r = some r2 →
      runCountB S prog L' op n r = runCountB S prog L op n r
  | 0, r, r2, _ => rfl
  | n + 1, r, r2, h => by
    unfold runB at h
    split_ifs at h with hf
    obtain ⟨r1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have h1' := stepB_of_ext hrd h1
    unfold runCountB
    obtain ⟨i, hi, -⟩ := Option.bind_eq_some_iff.mp h1
    rw [hi, h1, h1']
    dsimp only
    rw [runCountB_of_ext hrd op n h2]

/-! ## The padded execution -/

/-- `22 ≤ leanIsaμ` when the blocks' total exceeds `2^21`. -/
theorem le_leanIsaμ_of_total {prog : Program} {s : Sizes}
    (h : 2 ^ 21 < (LeanIsa.blocks prog s).total) : 22 ≤ leanIsaμ prog s := by
  unfold leanIsaμ
  refine le_trans ?_ (le_max_left _ _)
  by_contra hc
  push Not at hc
  have h1 := Nat.le_pow_clog (b := 2) (by norm_num) (LeanIsa.blocks prog s).total
  have h2 : (2 : ℕ) ^ Nat.clog 2 (LeanIsa.blocks prog s).total ≤ 2 ^ 21 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

variable {Sm : BlakeSem}

/-- The committed size's tables part: what the instruction counts contribute. -/
noncomputable def countsPart (Sm : BlakeSem) {prog : Program} (t : Trace prog) : ℕ :=
  15 * 2 ^ Nat.clog 2 (t.countB Sm .xor) + 15 * 2 ^ Nat.clog 2 (t.countB Sm .mulNative) +
    8 * 2 ^ Nat.clog 2 (t.countB Sm .setConstant) + 15 * 2 ^ Nat.clog 2 (t.countB Sm .deref) +
    14 * 2 ^ Nat.clog 2 (t.countB Sm .jump) + 19 * 2 ^ Nat.clog 2 (t.countB Sm .blake2s) +
    2 ^ 8 * 2 ^ Nat.clog 2 (t.countB Sm .blake2s)

/-- The committed size: the memory, the bytecode, the tables. -/
theorem committedSizeB_split {prog : Program} (t : Trace prog) :
    t.committedSizeB Sm = 4 * 2 ^ t.κ + 2 ^ prog.logSize + countsPart Sm t := by
  unfold Trace.committedSizeB countsPart
  dsimp only
  ring

/-- **A valid execution, padded above `2^21`**: of committed size in `(2^21, 2^28]`, on a memory
reading the same words with default `0`. -/
theorem exists_padded {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB Sm prog input t) (hsize : t.committedSizeB Sm ≤ 2 ^ 28) :
    ∃ t' : Trace prog, ValidExecutionB Sm prog input t' ∧ t'.committedSizeB Sm ≤ 2 ^ 28 ∧
      2 ^ 21 < t'.committedSizeB Sm ∧ ∀ a, (t'.image.read a).getD 0 = (t.image.read a).getD 0 := by
  by_cases hbig : 2 ^ 21 < t.committedSizeB Sm
  · exact ⟨t, hv, hsize, hbig, fun _ ↦ rfl⟩
  push Not at hbig
  obtain ⟨⟨h16, h32, h0, h1⟩, hrun⟩ := hv
  rw [committedSizeB_split] at hbig
  have hlog : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  have hκ : t.κ ≤ 19 := by
    by_contra hc
    push Not at hc
    have : (2 : ℕ) ^ 20 ≤ 2 ^ t.κ := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have h64 : (19 : ℕ) < 64 := by norm_num
  have hrd : ∀ a v, t.image.read a = some v → (padImage 19 t.image).read a = some v :=
    fun _ _ h ↦ padImage_read_of h64 hκ h
  have hcount : ∀ op, (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog).countB Sm op =
      t.countB Sm op := fun op ↦ runCountB_of_ext hrd op t.steps hrun
  have hparts : countsPart Sm (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog) =
      countsPart Sm t := by
    unfold countsPart
    simp only [hcount]
  have hsz := committedSizeB_split (Sm := Sm) (⟨19, padImage 19 t.image, t.steps⟩ : Trace prog)
  rw [hparts] at hsz
  have e19 : (2 : ℕ) ^ (19 : ℕ) = 524288 := by norm_num
  dsimp only at hsz
  rw [e19] at hsz
  refine ⟨⟨19, padImage 19 t.image, t.steps⟩, ⟨⟨by show 16 ≤ 19; omega, by show 19 ≤ 32; omega,
    padImage_read_of h64 hκ h0, padImage_read_of h64 hκ h1⟩, runB_of_ext hrd _ hrun⟩, by omega,
    by omega, fun a ↦ padImage_read_getD h64 hκ t.image a⟩

/-- **An admissible witness with its blocks' total** (`exists_admissible_witnessB`, the total
kept). -/
theorem exists_admissible_witness_total [Fact (Canonical Sm)] {prog : Program}
    {input : PublicInput} {t : Trace prog} (hv : ValidExecutionB Sm prog input t)
    (hbudget : t.committedSizeB Sm ≤ 2 ^ maxMu) :
    ∃ w s, SatisfiedByB prog input w ∧ ImageOf w t ∧ Sizes.ofWitness w = some s ∧
      s.Admissible prog ∧ (LeanIsa.blocks prog s).total = t.committedSizeB Sm := by
  have hcount : ∀ op, t.countB Sm op = runRowsB Sm t op := countB_eq_runRowsB hv.2
  have hheight : ∀ op, 2 ^ Nat.clog 2 (t.countB Sm op) ≤ t.committedSizeB Sm := by
    intro op
    have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
    simp only [Trace.committedSizeB]
    cases op <;> omega
  have hcap : (2 : ℕ) ^ maxMu ≤ 2 ^ maxLogRows := Nat.pow_le_pow_right (by norm_num) (by decide)
  have hrows : ∀ op, runRowsB Sm t op ≤ 2 ^ maxLogRows := fun op ↦ by
    rw [← hcount]
    exact (Nat.le_pow_clog (by norm_num) _).trans (((hheight op).trans hbudget).trans hcap)
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompletenessB_rows hv hrows
  obtain ⟨s, hs⟩ := sizes_of_satisfiedByG hw
  refine ⟨w, s, hw, hrep, hs, ?_⟩
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  have hmem : (witnessSizes w hpos).logMem = t.κ := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.countB Sm (tableOpcode j) := fun j ↦
    (hlen j).trans (hcount _).symm
  have htotal : (LeanIsa.blocks prog (witnessSizes w hpos)).total = t.committedSizeB Sm := by
    have e : tableOpcode 0 = .xor ∧ tableOpcode 1 = .mulNative ∧ tableOpcode 2 = .setConstant ∧
        tableOpcode 3 = .deref ∧ tableOpcode 4 = .jump ∧ tableOpcode 5 = .blake2s := by decide
    rw [blocks_total_eq, hmem, pow_add 2 8]
    simp only [Sizes.τ, hr, e, Trace.committedSizeB]
    ring
  refine ⟨⟨?_, ?_, fun j ↦ (hr j).trans_le (by rw [hcount]; exact hrows _), ?_⟩, htotal⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1
  · exact leanIsaμ_le_of_total_le (htotal ▸ hbudget)

/-- **The stack of an execution with its blocks' total** (`exists_stack_of_validB`, the total
kept). -/
theorem exists_stack_total [Fact (Canonical Sm)] (hfree : ∀ b, Sm.row b → blakeFree.row b)
    {prog : Program} {input : PublicInput} {t : Trace prog} (hv : ValidExecutionB Sm prog input t)
    (hbudget : t.committedSizeB Sm ≤ 2 ^ 28) :
    ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), s.Admissible prog ∧
      M3HoldsBlind (inst prog s) input q ∧ (inst prog s).PaddingHonest q ∧
      candidateRun prog s q = some t ∧ (LeanIsa.blocks prog s).total = t.committedSizeB Sm := by
  obtain ⟨w, s, hw, hrep, hs, hadm, htot⟩ := exists_admissible_witness_total hv hbudget
  refine ⟨s, stackOfG (genFree Sound.F₀.slot) prog s w, hadm,
    (m3HonestBlind_stackOfG (F := Sound.F₀) hw hs).1,
    (m3HonestBlind_stackOfG (F := Sound.F₀) hw hs).2, ?_, htot⟩
  have himg := (witnessOf_stackOfG (F := Sound.F₀) (gen := genFree Sound.F₀.slot) hw hs).2.2.2.2
  have hsig : imageOf w.data = ⟨t.κ, t.image⟩ := by
    obtain ⟨hκ, hi⟩ := hrep
    revert hκ hi
    generalize imageOf w.data = p
    obtain ⟨κ, img⟩ := p
    intro hκ hi
    simp only at hκ hi
    subst hκ
    exact image_sigma_eq rfl _ _ fun i ↦ hi i i.isLt
  unfold candidateRun
  rw [himg, hsig]
  exact haltingRunB_of_validB hfree hv

/-! ## A node without children decodes on the padded memory -/

/-- `main`'s valuation reads with default `0`. -/
theorem valG_congr_getD {κ κ' : ℕ} {L : MemImage κ} {L' : MemImage κ'}
    (h : ∀ a, (L'.read a).getD 0 = (L.read a).getD 0) (fp : K) (C : Check.Cert) :
    Check.valG L' fp C = Check.valG L fp C := by
  funext v
  simp only [Check.valG, Check.wd, h]

/-- **A node without children decodes on any memory reading the same words with default `0`.** -/
theorem decodeHonest_leaf_of_getD {fr : Frames} {t t' : Trace guest} {w : NodeWitness}
    (hw : w.children = []) (h : ∀ a, (t'.image.read a).getD 0 = (t.image.read a).getD 0)
    (hd : DecodeHonest fr t w) : DecodeHonest fr t' w := by
  unfold DecodeHonest at hd ⊢
  simp only [End.decodeAt, B1.Main.decWit, B1.Main.decKids, hw, List.map_nil,
    List.map_eq_nil_iff, List.range_eq_nil] at hd ⊢
  rw [valG_congr_getD h]
  exact hd

/-! ## A node without children has a big execution -/

/-- **A node without children, valid and within the limits, has an execution on its own log's
strings whose stack has at least 22 variables** (`nodeExec_nodeLog`, padded). -/
theorem nodeExec_nodeLog_big (H : Bytes → Digest) {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) (hleaf : w.children = []) :
    ∃ e : NodeExecOn (nodeLog H s w) H (digestOf H s) w, 22 ≤ leanIsaμ guest e.1.sz := by
  have hD := nodeLog_count_lt hlim hrel
  have hpi : statementDigestWith (answeredOn (nodeLog H s w) H) (seedOf H) s =
      some (digestOf H s) := by
    rw [statementDigestWith_answeredOn _ _ fun x hx ↦ by
      simp only [nodeLog, nodeLogWith, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inl hx)))))]
    exact statementDigestWith_someH H s
  have hrel' := nodeRelWith_answeredOn (D := nodeLog H s w) (fun _ hx ↦ hx) hrel
  let I := intermediatesOf (nodeLog H s w) hD
  obtain ⟨t, fr, hv, hsize, hdec⟩ := guestCompleteModel (CompModel.chain I H) H
    (fun _ _ h ↦ (answeredOn_some h).2) (seedOf H) s w (digestOf H s) hpi hrel' hlim hcaps hbud
  obtain ⟨t', hv', hsize', hbig, hrd⟩ := exists_padded hv hsize
  obtain ⟨sz, q, hadm, hrel'', hpad, hrun, htot⟩ :=
    exists_stack_total chainSem_le_free hv' hsize'
  exact ⟨⟨⟨nodeLog H s w, I, t', fr, sz, q, hv', decodeHonest_leaf_of_getD hleaf hrd hdec, hadm,
    ⟨hrel'', hpad⟩, hrun⟩, rfl⟩, le_leanIsaμ_of_total (htot ▸ hbig)⟩

end
end LeanVM.E2E.Complete
