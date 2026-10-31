/-
  LeanVM.Guest.B1.Main.World

  `main`'s run as the coverage table's writers: the segments of the marks, the running counts as
  their bases, the writers in their regions, and the bijection.
-/

module

public import LeanVM.Guest.B1.Main.Kids

/-!
# `main`'s coverage table, filled

From `MainFacts` and the children's records (`KidOk`): the segments (`segsOf`), the running
counts `written[c] = g^(a c)` (`written_eq`), the writers in their regions (`writers`), so a
slot function with `Cover` (`cover_bij`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

/-- The segments of `main`'s marks. -/
noncomputable def segsOf (σ : Val) (K : ℕ → KidRec) : Segs :=
  ⟨lg σ 2, lg σ 5, lg σ 6, fun c => (K c).ex, fun c => (K c).es⟩

variable {rd : Reader} {σ : Val} {K : ℕ → KidRec}

theorem segsOf_RX : (segsOf σ K).RX = lg σ 2 := rfl
theorem segsOf_RS : (segsOf σ K).RS = lg σ 5 := rfl
theorem segsOf_NC : (segsOf σ K).NC = lg σ 6 := rfl
theorem segsOf_ex (c : ℕ) : (segsOf σ K).ex c = (K c).ex := rfl
theorem segsOf_es (c : ℕ) : (segsOf σ K).es c = (K c).es := rfl

/-- The region sizes. -/
noncomputable abbrev LXS (σ : Val) : ℕ := lg σ 0 + lg σ 1
noncomputable abbrev LSS (σ : Val) : ℕ := lg σ 3 + lg σ 4

theorem a_le (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) :
    ∀ c ≤ lg σ 6, (segsOf σ K).a c ≤ 131070 + c * 131070 := by
  intro c
  induction c with
  | zero =>
    intro _
    have h2 := (MF.counts 2 (by simp)).2
    have h5 := (MF.counts 5 (by simp)).2
    rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]
    omega
  | succ c ih =>
    intro hc
    have := ih (by omega)
    obtain ⟨b1, b2⟩ := (hK c (by omega)).bounds
    rw [Segs.a.eq_2, segsOf_ex, segsOf_es]
    nlinarith

/-- **The running counts**: `written[c] = g^(a c)`. -/
theorem written_eq (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) :
    ∀ c ≤ lg σ 6, LoadHolds rd (σ (.n 380)) c (gen ^ (segsOf σ K).a c) := by
  intro c
  induction c with
  | zero => intro _; rw [Segs.a.eq_1, segsOf_RX, segsOf_RS]; exact MF.written0
  | succ c ih =>
    intro hc
    have hk := hK c (by omega)
    have hb := loadHolds_unique hk.base (ih (by omega))
    have := hk.next
    rw [hb, ← pow_add, ← pow_add] at this
    rw [Segs.a.eq_2, segsOf_ex, segsOf_es]
    exact this

set_option maxRecDepth 20000 in
/-- **The writers of the coverage table.** -/
theorem writers (MF : MainFacts C rd σ) (hK : ∀ c < lg σ 6, KidOk C rd σ c (K c)) :
    Writers rd (σ (.n 67)) (segsOf σ K) (LXS σ) (LSS σ) := by
  have eX : LXS σ = lg σ 0 + lg σ 1 := rfl
  have eS : LSS σ = lg σ 3 + lg σ 4 := rfl
  have hT := MF.total
  have h40 := MF.lxs
  have h41 := MF.lss
  have hc2 := (MF.counts 2 (by simp)).1
  have hw := written_eq MF hK
  have hbase : ∀ c < lg σ 6, (K c).base = gen ^ (segsOf σ K).a c :=
    fun c hc => loadHolds_unique (hK c hc).base (hw c (by omega))
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun c hc j hj => ?_, fun c hc j hj => ?_, ?_, by omega⟩
  · obtain ⟨s, hbl, hl, -⟩ := MF.rawx i hi
    exact ⟨s, belowLog_lt (by omega) h40 hbl, hl⟩
  · obtain ⟨s, hbl, hl, -⟩ := MF.raws j hj
    refine ⟨s, belowLog_lt (by omega) h41 hbl, ?_⟩
    rw [h40, hc2, ← pow_add, ← pow_add, loadHolds_gen_pow_iff, Nat.add_zero] at hl
    exact hl
  · obtain ⟨hbl, hl, -⟩ := (hK c hc).xrec j hj
    refine ⟨(K c).ox j, belowLog_lt (by omega) h40 hbl, ?_⟩
    rw [one_mul, loadHolds_gen_pow_iff, hbase c hc, ← pow_add, Nat.add_zero] at hl
    exact hl
  · obtain ⟨hbl, hl, -⟩ := (hK c hc).srec j hj
    refine ⟨(K c).os j, belowLog_lt (by omega) h41 hbl, ?_⟩
    rw [h40, ← pow_add, loadHolds_gen_pow_iff, hbase c hc, ← pow_add, ← pow_add,
      Nat.add_zero] at hl
    exact hl
  · rw [segsOf_NC]
    have h1 := hw (lg σ 6) le_rfl
    have h2 := MF.writtenN
    rw [hT.1] at h2
    have := loadHolds_unique h1 h2
    have hb := a_le MF hK (lg σ 6) le_rfl
    have hk6 := MF.kids.2
    exact gen_pow_inj34 (by omega) (by omega) this

end
end LeanVM.Guest.B1.Main
