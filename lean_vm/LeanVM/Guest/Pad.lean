/-
  LeanVM.Guest.Pad

  A valid execution on a larger memory: the memory extended past its end keeps every run and
  every instruction count, and commits at least `4` cells per word of the larger memory.
-/

module

public import LeanVM.Semantics.KeccakCells
public import LeanVM.Spec.Statement

/-!
# Padding the memory

The verifier admits a memory of any size `2^κ`, `16 ≤ κ ≤ 32` (`HasPublicBoundary`). A run on a
memory reads only addresses below its end; on the memory extended past it (`padImage`) it reads
the same words, so it steps to the same registers and executes the same instructions
(`run_pad`, `runCount_pad`). `Trace.pad`: the trace on `2^κ'` words, `κ ≤ κ' ≤ 32`, still a valid
execution (`validExecution_pad`) of the same counts, its committed size the original's but for
the memory's `4 · 2^κ'` cells (`committedSize_pad`). The aggregation guest pads its runs to a
committed size of at least `2^22` this way, so its proofs have a stack log at least `MU_MIN`,
the least the guest has an opening arm for (`aggregation.rs:1921-1925` grows the `SET` table
instead; the committed size is what both secure).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **The memory `L` extended to `2^κ'` words**, zero past its end. -/
noncomputable def padImage {κ : ℕ} (κ' : ℕ) (L : MemImage κ) : MemImage κ' :=
  fun i ↦ if h : i.val < 2 ^ κ then L ⟨i.val, h⟩ else 0

/-- A reader extending another: every word the first reads, the second reads too. -/
def ReadExt (read read' : K → Option E) : Prop := ∀ a v, read a = some v → read' a = some v

theorem readExt_padImage {κ κ' : ℕ} (h : κ ≤ κ') (h' : κ' < 64) (L : MemImage κ) :
    ReadExt L.read (padImage κ' L).read := by
  intro a v hr
  have hκ : κ < 64 := by omega
  obtain ⟨i, rfl, rfl⟩ := (MemImage.read_eq_some_iff hκ L).mp hr
  have hi : i.val < 2 ^ κ' := lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) h)
  rw [show gpow (i : ℕ) = gpow ((⟨i.val, hi⟩ : Fin (2 ^ κ')) : ℕ) from rfl,
    MemImage.read_gpow h' (padImage κ' L) ⟨i.val, hi⟩]
  simp [padImage]

theorem readCells_ext {read read' : K → Option E} (h : ReadExt read read') (fp : K)
    (offset : Fin 13 → K) {x : Fin 13 → E} (hx : readCells read fp offset = some x) :
    readCells read' fp offset = some x :=
  (readCells_eq_some_iff read' fp offset x).mpr fun c ↦
    h _ _ ((readCells_eq_some_iff read fp offset x).mp hx c)

/-- **An instruction executes alike on an extending reader.** -/
theorem executeWith_ext {read read' : K → Option E} (h : ReadExt read read') (r : Regs K)
    (ins : Instr) {r' : Regs K} (hx : executeWith read r ins = some r') :
    executeWith read' r ins = some r' := by
  cases ins with
  | xor oA oB oC =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨a, ha, b, hb, c, hc, rest⟩ := hx
    exact ⟨a, h _ _ ha, b, h _ _ hb, c, h _ _ hc, rest⟩
  | mulNative oA oB oC =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨a, ha, b, hb, c, hc, rest⟩ := hx
    exact ⟨a, h _ _ ha, b, h _ _ hb, c, h _ _ hc, rest⟩
  | setConstant o k =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨a, ha, rest⟩ := hx
    exact ⟨a, h _ _ ha, rest⟩
  | deref o1 o2 o3 mode =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨p, hp, u, hu, v3, h3, v2, h2, rest⟩ := hx
    exact ⟨p, h _ _ hp, u, hu, v3, h _ _ h3, v2, h _ _ h2, rest⟩
  | jump oc od of =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨c, hc, d, hd, f, hf, rest⟩ := hx
    exact ⟨c, h _ _ hc, d, h _ _ hd, f, h _ _ hf, rest⟩
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨i, hi, o, ho, rest⟩ := hx
    exact ⟨i, readCells_ext h _ _ hi, o, readCells_ext h _ _ ho, rest⟩

variable {prog : Program} {κ κ' : ℕ} {L : MemImage κ} {L' : MemImage κ'}

theorem step_ext (h : ReadExt L.read L'.read) {r r' : Regs K} (hs : step prog L r = some r') :
    step prog L' r = some r' := by
  cases hf : prog.fetch r.pc with
  | none => rw [step_eq_none_of_fetch_eq_none hf] at hs; cases hs
  | some ins =>
    rw [step_of_fetch_eq_some hf] at hs ⊢
    exact executeWith_ext h r ins hs

/-- **A run on an extending memory**: the same registers, the same instructions. -/
theorem run_ext (h : ReadExt L.read L'.read) :
    ∀ (n : ℕ) (r r' : Regs K), run prog L n r = some r' →
      run prog L' n r = some r' ∧ ∀ op, runCount prog L' op n r = runCount prog L op n r
  | 0, r, r', hr => ⟨hr, fun _ ↦ rfl⟩
  | n + 1, r, r', hr => by
    by_cases hp : r = Regs.final prog
    · rw [run_succ_of_eq hp] at hr; cases hr
    · rw [run_succ_of_ne_final hp] at hr
      obtain ⟨r1, hs, hr1⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨ih1, ih2⟩ := run_ext h n r1 r' hr1
      have hs' := step_ext h hs
      refine ⟨by rw [run_succ_of_ne_final hp, hs']; exact ih1, fun op ↦ ?_⟩
      cases hf : prog.fetch r.pc with
      | none => rw [step_eq_none_of_fetch_eq_none hf] at hs; cases hs
      | some ins => simp only [runCount, hf, hs, hs', ih2 op]

/-- **The trace on `2^κ'` words.** -/
noncomputable def _root_.LeanVM.Semantics.Trace.pad (t : Trace prog) (κ' : ℕ) : Trace prog :=
  ⟨κ', padImage κ' t.image, t.steps⟩

theorem validExecution_pad {input : PublicInput} {t : Trace prog} {κ' : ℕ}
    (hv : ValidExecution prog input t) (hκ : t.κ ≤ κ') (hκ' : κ' ≤ maxLogMem) :
    ValidExecution prog input (t.pad κ') ∧ ∀ op, (t.pad κ').count op = t.count op := by
  have h64 : κ' < 64 := by unfold maxLogMem at hκ'; omega
  have he := readExt_padImage hκ h64 t.image
  obtain ⟨⟨h16, -, h0, h1⟩, hr⟩ := hv
  obtain ⟨hr', hc⟩ := run_ext he t.steps _ _ hr
  exact ⟨⟨⟨le_trans h16 hκ, hκ', he _ _ h0, he _ _ h1⟩, hr'⟩, hc⟩

theorem committedSize_pad (t : Trace prog) (κ' : ℕ)
    (hc : ∀ op, (t.pad κ').count op = t.count op) :
    (t.pad κ').committedSize + 4 * 2 ^ t.κ = t.committedSize + 4 * 2 ^ κ' := by
  simp only [Semantics.Trace.committedSize, hc]
  simp only [Semantics.Trace.pad]
  omega

/-- The memory alone commits `4` cells per word. -/
theorem four_mul_le_committedSize (t : Trace prog) : 4 * 2 ^ t.κ ≤ t.committedSize := by
  unfold Semantics.Trace.committedSize
  simp only [Nat.add_assoc]
  exact Nat.le_add_right _ _

end
end LeanVM.Guest
