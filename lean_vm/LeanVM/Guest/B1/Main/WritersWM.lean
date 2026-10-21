/-
  LeanVM.Guest.B1.Main.WritersWM

  `main`'s coverage argument over a hash model, the holders given (`WritersW.lean` over a
  `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.LoopsWM
public import LeanVM.Guest.B1.Main.WritersW

/-!
# The writers over a hash model

`SlotGoodWM M pc pr …`: `SlotGoodW` with the holders' checks over the model (`XmssHeldWith M.H`,
`SphincsHeldWith M.H`, `DaHeldWith M.H pc pr`, `Spec/NodeWith.lean`); `writers_good_wM` is
`writers_good_w` over the children's `ChildAtM`. The proof is the deployed one: the coverage
argument reads only the children's marks, never a hash. `kidStmt_eq` is used as it is.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

/-- **Slot `s`, with the mark `g^e`, is certified by its holder over a model** (`SlotGoodW`):
`hX e s` holds the leanXMSS table's claim `s`, `hS` the leanSPHINCS claim, `hD` the DA claim, by
the slot's region, each direct check over the model's hash. -/
def SlotGoodWM (M : HashModel) (pc pr : LeanDa.Digest) (rd : Reader) (F : Frame)
    (chs : List Child)
    (hX : ℕ → ℕ → Holder LeanXmss.Signature) (hS : ℕ → ℕ → Holder Sphincs.Signature)
    (hD : ℕ → ℕ → Holder Da.Witness) (e s : ℕ) : Prop :=
  (s < F.Lx → XmssHeldWith M.H chs (entryX rd F.lxT s) (hX e s)) ∧
    (F.Lx ≤ s → s < F.Lx + F.Ls →
      SphincsHeldWith M.H chs (entryS rd F.spT (s - F.Lx)) (hS e (s - F.Lx))) ∧
    (F.Lx + F.Ls ≤ s → ∀ cl, DaAt rd F.daR (s - (F.Lx + F.Ls)) cl →
      DaHeldWith M.H pc pr chs cl (hD e (s - (F.Lx + F.Ls))))

/-- **Every mark certifies its slot, by its holder, over a model** (`writers_good_w`). -/
theorem writers_good_wM {M : HashModel} {pc pr : LeanDa.Digest} {F : Frame} {seed : Digest} {chs : List Child} {a2 a5 a7 : ℕ}
    {hX : ℕ → ℕ → Holder LeanXmss.Signature} {hS : ℕ → ℕ → Holder Sphincs.Signature}
    {hD : ℕ → ℕ → Holder Da.Witness}
    (hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls))
    (h3 : ∀ i < a2, ∃ s < F.Lx, LoadHolds rd F.cover s (gen ^ i) ∧
      XmssHeldWith M.H chs (entryX rd F.lxT s) (hX i s))
    (h4 : ∀ j < a5, ∃ s < F.Ls, LoadHolds rd F.cover (F.Lx + s) (gen ^ (a2 + j)) ∧
      SphincsHeldWith M.H chs (entryS rd F.spT s) (hS (a2 + j) s))
    (ha7 : a7 ≤ 1)
    (hd : a7 = 1 → ∃ i < F.Md, LoadHolds rd F.daC i (gen ^ (a2 + a5)) ∧
      ∀ cl, DaAt rd F.daR i cl → DaHeldWith M.H pc pr chs cl (hD (a2 + a5) i))
    (hch : ∀ c (hc : c < chs.length), ChildAtM M bytecode rd F seed c chs[c])
    (hbase : ∀ c ≤ chs.length, LoadHolds rd F.written c (gen ^ counts (a2 + a5 + a7) chs c))
    (hkid : ∀ e c, c < chs.length → counts (a2 + a5 + a7) chs c ≤ e →
      e < counts (a2 + a5 + a7) chs (c + 1) →
        ∀ s, hX e s = .child c ∧ hS e s = .child c ∧ hD e s = .child c) :
    ∀ e < counts (a2 + a5 + a7) chs chs.length, ∃ s < F.Lx + F.Ls + F.Md,
      LoadHolds rd F.cover s (gen ^ e) ∧ SlotGoodWM M pc pr rd F chs hX hS hD e s := by
  intro e he
  rcases Nat.lt_or_ge e a2 with h1 | h1
  · obtain ⟨s, hs, hl, hh⟩ := h3 e h1
    exact ⟨s, by omega, hl, fun _ => hh, fun h _ => absurd h (by omega),
      fun h => absurd h (by omega)⟩
  rcases Nat.lt_or_ge e (a2 + a5) with h2 | h2
  · obtain ⟨s, hs, hl, hh⟩ := h4 (e - a2) (by omega)
    rw [show a2 + (e - a2) = e by omega] at hl hh
    refine ⟨F.Lx + s, by omega, hl, fun h => absurd h (by omega), fun _ _ => ?_,
      fun h => absurd h (by omega)⟩
    rwa [Nat.add_sub_cancel_left]
  rcases Nat.lt_or_ge e (a2 + a5 + a7) with h5 | h5
  · obtain ⟨i, hi, hl, hw⟩ := hd (by omega)
    rw [hdaC, loadHolds_mul_gen_pow, show a2 + a5 = e by omega] at hl
    rw [show a2 + a5 = e by omega] at hw
    refine ⟨F.Lx + F.Ls + i, by omega, hl, fun h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ => ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact hw
  obtain ⟨c, hc, hc1, hc2⟩ := exists_segment (counts (a2 + a5 + a7) chs)
    (counts_mono (a2 + a5 + a7) chs) (show counts (a2 + a5 + a7) chs 0 ≤ e by simpa [counts])
    chs.length he
  have hk := hkid e c hc hc1 hc2
  rw [counts_succ _ _ _ hc, nOf] at hc2
  obtain ⟨base, hw0, -, -, -, -, hXc, hSc, hDc, -⟩ := hch c hc
  have hb := loadHolds_unique hw0 (hbase c (by omega))
  subst hb
  set b := counts (a2 + a5 + a7) chs c
  have hget : chs[c]? = some chs[c] := List.getElem?_eq_getElem hc
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length) with g1 | g1
  · obtain ⟨s, hs, hl, he'⟩ := hXc (e - b) (by omega)
    rw [← pow_add, show b + (e - b) = e by omega] at hl
    refine ⟨s, by omega, hl, fun _ => ?_, fun h => absurd h (by omega),
      fun h => absurd h (by omega)⟩
    rw [(hk s).1]
    exact ⟨chs[c], hget, List.mem_of_getElem? he'⟩
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length +
    chs[c].statement.claims.sphincs.length) with g2 | g2
  · obtain ⟨s, hs, hl, he'⟩ := hSc (e - b - chs[c].statement.claims.xmss.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      (e - b - chs[c].statement.claims.xmss.length)) = e by omega] at hl
    refine ⟨F.Lx + s, by omega, hl, fun h => absurd h (by omega), fun _ _ => ?_,
      fun h => absurd h (by omega)⟩
    rw [Nat.add_sub_cancel_left, (hk s).2.1]
    exact ⟨chs[c], hget, List.mem_of_getElem? he'⟩
  · obtain ⟨i, hi, hl, hcl⟩ := hDc (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      chs[c].statement.claims.sphincs.length + (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length)) = e by omega, hdaC, loadHolds_mul_gen_pow] at hl
    refine ⟨F.Lx + F.Ls + i, by omega, hl, fun h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ cl hcl' => ?_⟩
    rw [Nat.add_sub_cancel_left] at hcl' ⊢
    rw [(hk i).2.2]
    have hcl'' := List.getElem?_eq_getElem (l := chs[c].statement.claims.da)
      (i := e - b - chs[c].statement.claims.xmss.length - chs[c].statement.claims.sphincs.length)
      (by omega)
    have := daAt_unique hcl' (hcl _ hcl'')
    subst this
    exact ⟨chs[c], hget, List.mem_of_getElem? hcl''⟩

end
end LeanVM.Guest.B1.Main
