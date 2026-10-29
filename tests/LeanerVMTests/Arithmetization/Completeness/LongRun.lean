import LeanerVM.Arithmetization.Completeness.Theorem
import LeanerVMTests.Semantics.FillBlocks
import LeanerVMTests.Semantics.LongRun

/-!
# Layer 10 tests: no witness represents a run that does not fit

`Trace.Fits` bounds every table's padded height by `2^32`. A witness that satisfies `Caps` has at
most `2^32` rows in each of its eight tables, and one that represents a trace has a row for every
step of it, with the state it steps from: distinct steps of a run that halts are distinct states,
so distinct rows. Hence a witness that satisfies `Caps` and represents a valid trace has at most
`8 * 2^32` steps in the trace (`steps_le_rows`).

The run of `Semantics.LongRun` loops `2^30` frames of thirty-three steps and a `JUMP`: it has
`33 * 2^30 + 1 > 8 * 2^32` steps and is valid. So for every program of its shape,
`constraintCompleteness` without the size hypothesis `hfit` is false: no witness satisfies the
statement and represents this trace (`completeness_fails_on_long_run`), and the trace is not one
that fits (`Semantics.LongRun`). The shape is inhabited by well formed bytecode, the compiler's
layout with the loop in front (`completeness_needs_fit`), so the other hypothesis of the theorem
holds and the failure is about the sizes alone.
-/

namespace LeanerVMTests.Arithmetization.Completeness.LongRun

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open Air.Flat (EnsembleWitness)
open LeanerVMTests.Semantics.FillBlocks LeanerVMTests.Semantics.LongRun

/-! ## Distinct states -/

/-- The register states of a run that halts at the sentinel are pairwise distinct. -/
theorem run_inj {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ} {r₀ rf : Regs K}
    (h : run prog L n r₀ = some rf) (hf : rf.pc = prog.finalPc) {a b : ℕ} {r : Regs K}
    (ha : run prog L a r₀ = some r) (hb : run prog L b r₀ = some r) : a = b := by
  -- no run continues past the sentinel
  have hle : ∀ m s, run prog L m r₀ = some s → m ≤ n := by
    intro m s hm
    by_contra hlt
    obtain ⟨k, hk⟩ : ∃ k, m = n + (k + 1) := ⟨m - n - 1, by omega⟩
    rw [hk, run_add, h] at hm
    change run prog L (k + 1) rf = some s at hm
    rw [run_succ_of_eq hf] at hm
    exact absurd hm (by simp)
  -- the case `a < b` is contradictory; symmetry gives the rest
  have key : ∀ a b : ℕ, run prog L a r₀ = some r → run prog L b r₀ = some r → a < b → False := by
    intro a b ha hb hab
    have hbn := hle b r hb
    -- from `r`: `n - a` steps reach `rf`, and `b - a` steps return to `r`
    have h1 : run prog L (n - a) r = some rf := by
      have := h
      rw [show n = a + (n - a) by omega, run_add, ha] at this
      exact this
    have h2 : run prog L (b - a) r = some r := by
      have := hb
      rw [show b = a + (b - a) by omega, run_add, ha] at this
      exact this
    have h3 : run prog L (n - a - (b - a)) r = some rf := by
      have := h1
      rw [show n - a = (b - a) + (n - a - (b - a)) by omega, run_add, h2] at this
      exact this
    obtain ⟨r₁, hr₁, hne⟩ := run_intermediate h1 (m := n - a - (b - a)) (by omega)
    rw [h3] at hr₁
    obtain rfl := Option.some.inj hr₁
    exact hne hf
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (key a b ha hb hab).elim
  · rfl
  · exact (key b a hb ha hab).elim

/-- The `k`-th register state of a valid trace is the run's state after `k` steps. -/
theorem regs_getElem' {prog : Program} {t : Trace prog}
    (h : run prog t.image t.steps Regs.initial = some (Regs.final prog)) (k : ℕ)
    (hk : k < t.regs.length) : run prog t.image k Regs.initial = some t.regs[k] := by
  have hk' : k ≤ t.steps := by
    have := Trace.regs_length h
    omega
  rw [List.getElem_of_eq (regs_eq_map h) hk, List.getElem_map, List.getElem_range]
  exact run_stateAt h hk'

/-- Two register pairs with the same components are equal. -/
theorem regs_ext' {a b : Regs K} (h1 : a.pc = b.pc) (h2 : a.fp = b.fp) : a = b := by
  cases a; cases b; simp_all

/-! ## The counting bound -/

/-- A witness that satisfies `Caps` and represents a valid trace has at least as many rows as the
trace has steps, over its eight tables: `t.steps ≤ 8 * 2^32`. -/
theorem steps_le_rows {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (hv : ValidExecution prog input t) (hc : Caps w) (hr : AssignmentRepresents w t) :
    t.steps ≤ 8 * 2 ^ 32 := by
  obtain ⟨-, hrun⟩ := hv
  have hlen : t.regs.length = t.steps + 1 := Trace.regs_length hrun
  have hrow : ∀ k : Fin t.steps, ∃ (j : Fin 8) (row : Array K), row ∈ (tableAt w j).table ∧
      rowMessagesOn (tableAt w j) row StatePull.toRaw =
        [#[(t.regs[k.val]'(by omega)).pc, (t.regs[k.val]'(by omega)).fp]] := by
    intro k
    have hk : k.val + 1 < t.regs.length := by have := k.isLt; omega
    obtain ⟨tb, htb, row, hrow, hpull, -⟩ := hr.regs_embed k hk
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp htb
    exact ⟨j, row, hrow, hpull⟩
  choose j row hmem hmsg using hrow
  have hinj : Function.Injective fun k : Fin t.steps ↦ (⟨j k, row k⟩ : Σ _ : Fin 8, Array K) := by
    intro k k' h
    have hh := Sigma.mk.inj h
    have hj : j k = j k' := hh.1
    have hr' : row k = row k' := eq_of_heq hh.2
    have h1 := hmsg k
    have h2 := hmsg k'
    rw [← hj, ← hr', h1] at h2
    simp only [List.cons.injEq, and_true, Array.mk.injEq] at h2
    obtain ⟨hpc, hfp⟩ := h2
    have hreg : t.regs[k.val]'(by have := k.isLt; omega) =
        t.regs[k'.val]'(by have := k'.isLt; omega) := regs_ext' hpc hfp
    have ha := regs_getElem' hrun k.val (by have := k.isLt; omega)
    have hb := regs_getElem' hrun k'.val (by have := k'.isLt; omega)
    rw [← hreg] at hb
    exact Fin.ext (run_inj hrun rfl ha hb)
  let T : Finset (Σ _ : Fin 8, Array K) :=
    (Finset.univ : Finset (Fin 8)).sigma fun j ↦ (tableAt w j).table.toFinset
  have hlen' : ∀ j : Fin 8, (tableAt w j).table.length ≤ 2 ^ 32 := by
    intro j
    obtain ⟨τ, hτ, hl⟩ := hc.heights (tableAt w j) (mem_tables_iff.mpr ⟨j, rfl⟩)
    rw [hl]
    exact Nat.pow_le_pow_right (by norm_num) (by unfold maxLogRows at hτ; omega)
  calc t.steps = (Finset.univ : Finset (Fin t.steps)).card := by simp
    _ ≤ T.card := Finset.card_le_card_of_injOn (fun k ↦ (⟨j k, row k⟩ : Σ _ : Fin 8, Array K))
        (fun k _ ↦ by
          simp only [T, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ,
            Finset.mem_coe, List.mem_toFinset, true_and]
          exact hmem k)
        hinj.injOn
    _ = ∑ j : Fin 8, ((tableAt w j).table.toFinset).card := Finset.card_sigma _ _
    _ ≤ ∑ _j : Fin 8, 2 ^ 32 := Finset.sum_le_sum fun j _ ↦
        (List.toFinset_card_le _).trans (hlen' j)
    _ = 8 * 2 ^ 32 := by simp


/-! ## The refutation -/

/-- **`constraintCompleteness` fails on long runs.**  For every program of the shape, there is a
valid execution that no witness of `SatisfiedBy` represents. -/
theorem completeness_fails_on_long_run (prog : Program) (sh : Shape prog) :
    ∃ (input : PublicInput) (t : Trace prog), ValidExecution prog input t ∧
      ¬ ∃ w : EnsembleWitness (leanIsaEnsemble prog),
          SatisfiedBy prog input w ∧ AssignmentRepresents w t := by
  obtain ⟨input, t, hv, hbig⟩ := long_run_valid prog sh
  refine ⟨input, t, hv, ?_⟩
  rintro ⟨w, hsat, hrep⟩
  have hle := steps_le_rows hv hsat.caps hrep
  norm_num at hle hbig
  omega


/-! ## Well formed bytecode of the shape

The compiler's layout with the loop in front: thirty-three `SET_CONSTANT [g^0] g`, the `JUMP`, then
for each of the six tables its blocks of sizes `128 .. 1` back to back (`263` slots a table), then
`SET_CONSTANT` up to the sentinel at slot `2047`. -/

/-- The instruction at slot `i`. -/
def longCode (i : ℕ) : Instr :=
  if i ≤ 32 then .setConstant (gpow 0) (ofK g)
  else if i = 33 then .jump (gpow 1) (gpow 2) (gpow 3)
  else if i ≤ 1611 then
    (if (i - 34) % 263 ∈ closeOffsets then fillClose else fillDummy (tableOf ((i - 34) / 263)))
  else .setConstant (gpow 0) (ofK g)

/-- `34 + 6 * 263 = 1612` slots padded to `2^11`. -/
def longProg : Program := ⟨11, by decide, fun i ↦ longCode i⟩

/-- The instruction at a slot, fetched through the address of the slot. -/
theorem long_fetch (n : ℕ) (hn : n < 2048) : longProg.fetch (gpow n) = some (longCode n) :=
  longProg.fetch_gpow ⟨n, hn⟩

/-- A block of the layout: size `s` at offset `c` of the `k`-th table's slots. -/
theorem long_block (t : Opcode) (k : ℕ) (hk : k < 6) (ht : tableOf k = t) (s c : ℕ)
    (hc : c + s < 263) (hclose : c + s ∈ closeOffsets)
    (hdummy : ∀ j, j < s → c + j ∉ closeOffsets) :
    IsFillBlock longProg t s (34 + 263 * k + c) := by
  refine ⟨?_, ?_, ?_⟩
  · show 34 + 263 * k + c + s + 1 < 2 ^ 11
    norm_num
    omega
  · intro j hj
    have hn : 34 + 263 * k + c + j < 2048 := by omega
    rw [long_fetch _ hn]
    congr 1
    unfold longCode
    have h0 : ¬ 34 + 263 * k + c + j ≤ 32 := by omega
    have h0' : 34 + 263 * k + c + j ≠ 33 := by omega
    have h1 : 34 + 263 * k + c + j ≤ 1611 := by omega
    have h2 : (34 + 263 * k + c + j - 34) % 263 = c + j := by omega
    have h3 : (34 + 263 * k + c + j - 34) / 263 = k := by omega
    simp only [h0, h0', h1, h2, h3, hdummy j hj, ht, ↓reduceIte]
  · have hn : 34 + 263 * k + c + s < 2048 := by omega
    rw [long_fetch _ hn]
    congr 1
    unfold longCode
    have h0 : ¬ 34 + 263 * k + c + s ≤ 32 := by omega
    have h0' : 34 + 263 * k + c + s ≠ 33 := by omega
    have h1 : 34 + 263 * k + c + s ≤ 1611 := by omega
    have h2 : (34 + 263 * k + c + s - 34) % 263 = c + s := by omega
    simp only [h0, h0', h1, h2, hclose, ↓reduceIte]

/-- Every table has a block of every size. -/
theorem long_hasFillBlocks : HasFillBlocks longProg := by
  intro t s hs
  obtain ⟨k, hk, ht⟩ : ∃ k, k < 6 ∧ tableOf k = t := by
    cases t
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩,
      ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩]
  simp only [fillSizes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, long_block t k hk ht 128 0 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 64 129 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 32 194 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 16 227 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 8 244 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 4 253 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 2 258 (by norm_num) (by decide) (by decide)⟩
  · exact ⟨_, long_block t k hk ht 1 261 (by norm_num) (by decide) (by decide)⟩

/-- The sentinel slot holds a `SET_CONSTANT`. -/
theorem long_sentinelSafe : SentinelSafe longProg := by decide

/-- The layout is well formed bytecode. -/
theorem long_wellFormed : WellFormedBytecode longProg :=
  ⟨long_sentinelSafe, long_hasFillBlocks⟩

/-- It has the shape of the long run. -/
theorem long_shape : Shape longProg where
  sets := fun s hs ↦ by
    rw [long_fetch s (by omega)]
    simp [longCode, hs]
  jump := by
    rw [long_fetch 33 (by norm_num)]
    simp [longCode]
  big := by decide

/-- **The size hypothesis is load-bearing, for well formed bytecode.** Well formed bytecode has a
valid execution that no witness of `SatisfiedBy` represents: `constraintCompleteness` needs `hfit`,
and `Semantics.LongRun` shows that this trace does not fit. -/
theorem completeness_needs_fit :
    WellFormedBytecode longProg ∧
      ∃ (input : PublicInput) (t : Trace longProg), ValidExecution longProg input t ∧ ¬ t.Fits ∧
        ¬ ∃ w : EnsembleWitness (leanIsaEnsemble longProg),
            SatisfiedBy longProg input w ∧ AssignmentRepresents w t := by
  refine ⟨long_wellFormed, ?_⟩
  obtain ⟨input, t, hv, hbig⟩ := long_run_valid longProg long_shape
  have h35 : (2 : ℕ) ^ 35 = 8 * 2 ^ 32 := by norm_num
  refine ⟨input, t, hv, fun hf ↦ ?_, ?_⟩
  · have := hf.steps_le hv.2
    have hcap : maxLogRows = 32 := rfl
    rw [hcap] at this
    omega
  · rintro ⟨w, hsat, hrep⟩
    have hle := steps_le_rows hv hsat.caps hrep
    omega

end LeanerVMTests.Arithmetization.Completeness.LongRun
