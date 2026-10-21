/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm1

  The buffers' assembly over a completeness model (`Whir/OsAsm1.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm1
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsLv
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsPoint
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsGlued

/-!
# The buffers' assembly over a completeness model (`Whir/OsAsm1.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {cfg : OsCfg} {d : OsData}

theorem ownQ_setC (Q : List E) : d.ownQW Ht cfg Q = (d.ownQW Ht cfg []).set 8 Q := rfl

/-- The buffers' entries without the decoders' pointers: those with them, or empty. -/
theorem bufL_ownQ_nilC {b : ℕ} {Q : List E} {q : ℕ × List E} (hq : q ∈ bufL b (osSizes cfg) (d.ownQW Ht cfg [])) :
    q ∈ bufL b (osSizes cfg) (d.ownQW Ht cfg Q) ∨ q.2 = [] := by
  unfold bufL at hq ⊢
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  simp only [List.length_zip] at hi
  by_cases h8 : i = 8
  · subst h8; right; simp [List.getElem_zip, ownQW]
  · left
    refine List.mem_iff_getElem.mpr ⟨i, by simp [ownQ_lengthC (Ht := Ht)] at hi ⊢; omega, ?_⟩
    simp only [List.getElem_zip]
    congr 1
    rw [List.getElem_of_eq (ownQ_setC (Ht := Ht) Q), List.getElem_set_ne (Ne.symm h8)]

/-- **The buffers with the decoders' pointers hold those without.** -/
theorem memL_ownQ_nilC {rd : Reader} {b : ℕ} {Q : List E} (h : MemL rd (bufL b (osSizes cfg) (d.ownQW Ht cfg Q))) :
    MemL rd (bufL b (osSizes cfg) (d.ownQW Ht cfg [])) := by
  intro q hq
  rcases bufL_ownQ_nilC (Ht := Ht) (Q := Q) hq with h1 | h1
  · exact h q h1
  · rw [h1]; exact readsAt_nil _ _

theorem regionL_ownQ_nilC {b : ℕ} {Q : List E} {i : ℕ} (h : RegionL (bufL b (osSizes cfg) (d.ownQW Ht cfg [])) i) :
    RegionL (bufL b (osSizes cfg) (d.ownQW Ht cfg Q)) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases bufL_ownQ_nilC (Ht := Ht) (Q := Q) hq with h3 | h3
  · exact ⟨q, h3, h1, h2⟩
  · rw [h3] at h2; simp at h2; omega

/-- **A level's window of the decoders' pointers.** -/
theorem memL_osWC (hlay : OsLayoutOk cfg) {rd : Reader} {b : ℕ} {ps : ℕ → ℕ}
    (h : MemL rd (bufL b (osSizes cfg) (d.ownQW Ht cfg (qbpC cfg fs cert ps)))) {l : ℕ} (hl : l < cfg.levels.length) :
    MemL rd (osW fs cert cfg b l (ps l)) := by
  intro q hq
  rw [osW, List.mem_singleton] at hq
  subst hq
  have h8 := os_memL_bufL h (ownQ_lengthC (Ht := Ht) _) (j := 8) (by rw [os_length_osSizes]; omega)
  have e : (d.ownQW Ht cfg (qbpC cfg fs cert ps)).getD 8 [] = qbpC cfg fs cert ps := rfl
  rw [e] at h8
  have hw := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
    (c := fun l => qbpSeg cfg fs cert l (ps l)) h8
    (fun a c hac hc => by simp only [qbpSeg, List.length_map, List.length_range]; exact hlay.pos a c hac hc)
    (fun a ha => by simp only [qbpSeg, List.length_map, List.length_range]; exact hlay.posFit a ha) hl
  rw [ofK_gpow_mul] at hw
  exact hw

theorem regionL_osWC (hlay : OsLayoutOk cfg) {b : ℕ} {ps : ℕ → ℕ} {l p : ℕ} (hl : l < cfg.levels.length) {i : ℕ}
    (h : RegionL (osW fs cert cfg b l p) i) :
    RegionL (bufL b (osSizes cfg) (d.ownQW Ht cfg (qbpC cfg fs cert ps))) i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rw [osW, List.mem_singleton] at hq
  subst hq
  refine ⟨_, os_bufL_mem (ownQ_lengthC (Ht := Ht) _) (j := 8) (by rw [os_length_osSizes]; omega), ?_, ?_⟩
  · simp only at h1 ⊢; omega
  · have e : (d.ownQW Ht cfg (qbpC cfg fs cert ps)).getD 8 [] = qbpC cfg fs cert ps := rfl
    rw [e, qbpC, os_length_segC]
    simp only [qbpSeg, List.length_map, List.length_range] at h2
    have := hlay.posFit l hl
    simp only at h2 ⊢; omega

/-- The point buffer's words. -/
theorem ownQ_getD_ptC (Q : List E) : (d.ownQW Ht cfg Q).getD (11 + 2 * cfg.levels.length + 1) [] = d.ptCW Ht cfg := by
  have lA : ([d.capsCW Ht cfg, d.flagsCW Ht cfg, d.fmsgCW Ht cfg, d.rootsCW Ht cfg, d.fchCW Ht cfg, d.betasCW Ht cfg, d.qwCW Ht cfg, d.qposCW Ht cfg,
      Q, d.oodzCW Ht cfg, d.oodCW Ht cfg] : List (List E)).length = 11 := rfl
  have lF : ((List.range cfg.levels.length).flatMap fun l => [d.sqzCW Ht cfg l, d.rewCW Ht cfg l]).length =
      2 * cfg.levels.length := by simp [List.length_flatMap, List.map_const']; ring
  unfold ownQW
  simp only [List.append_assoc]
  rw [← lA, ← lF, Nat.add_assoc, os_getD_skip, os_getD_skip]
  rfl

end OsData

/-- **The last level of the list.** -/
theorem os_lvsLast_eqC (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) lvl cv p w osp roots, Hs ≠ [] →
    osLvsLast cfg xs lvl p roots Hs =
      (((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getLastD default).lvl,
        ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getLastD default).p,
        ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getLastD default).roots,
        ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getLastD default).H)
  | [], _, _, _, _, _, _, h => absurd rfl h
  | [H], lvl, cv, p, w, osp, roots, _ => rfl
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, _ => by
    rw [osLvsLast, os_lvsLast_eqC cfg xs (H' :: Hs) (lvl + 1) _ _ _ _ _ (by simp)]
    rfl

end
end LeanVM.Guest.B1
