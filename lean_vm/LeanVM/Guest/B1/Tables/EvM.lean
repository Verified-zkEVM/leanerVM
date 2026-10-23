/-
  LeanVM.Guest.B1.Tables.EvM

  Forward evaluation with the body's own stores: a load reads what an earlier store of the body
  wrote there, else the given memory. The honest valuation of a body that reads its own buffers.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Evaluation through the body's stores

`Fwd.ev rd w` reads every load from one memory `rd`. A body that stores into its own buffers and
reads them back needs the words it stored: `evM rd0 w` keeps a log of the stores so far (address,
word) and reads each load from `rd0` overlaid by the log (`ovl`, the first word logged at an
address). `evM_spec`: every statement satisfies `Good` for the memory of its step, a prefix of the
final log over `rd0`; a store's word is logged right after that prefix.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- A log of stores: addresses and words, in order. -/
abbrev SLog : Type := List (K × E)

/-- The memory `rd0` overlaid by a log: a logged address answers its first logged word. -/
def ovl (rd0 : Reader) (log : SLog) : Reader := fun a =>
  match log.find? (fun e => decide (e.1 = a)) with
  | some e => some e.2
  | none => rd0 a

/-- The store a statement makes at the counter `c`, on the valuation `σ`. -/
def stWr (c : Nat) (σ : Val) : Stmt → SLog
  | .atom (.load d p off) => if oldB c d then [((σ p).limb 0 * gpow off, σ d)] else []
  | _ => []

/-- **The evaluator through the stores.** -/
noncomputable def evM (rd0 : Reader) (w : Nat → E) : List E → SLog → List Stmt → List E × SLog
  | l, log, [] => (l, log)
  | l, log, s :: ss =>
    evM rd0 w (l ++ newS (ovl rd0 log) w l s)
      (log ++ stWr l.length (B1.Val.ofArgs l) s) ss

theorem stWr_congr {c : Nat} {σ σ' : Val} {s : Stmt} (he : ∀ v ∈ s.vals, σ v = σ' v) :
    stWr c σ s = stWr c σ' s := by
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [stWr]
      have hd := he d (by simp [Stmt.vals, Atom.vals])
      have hp := he p (by simp [Stmt.vals, Atom.vals])
      rw [hd, hp]
    | _ => rfl
  | _ => rfl

theorem stWr_old {l m : List E} {s : Stmt} {c' : Nat} (hc : chkS l.length s = some c') :
    stWr l.length (B1.Val.ofArgs (l ++ m)) s = stWr l.length (B1.Val.ofArgs l) s := by
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [chkS, chkA] at hc
      simp only [stWr]
      split_ifs with hd
      · split at hc
        · rename_i hp
          rw [ofArgs_old (oldB_spec hp).2, ofArgs_old (oldB_spec hd).2]
        · exact absurd hc (by simp)
      · rfl
    | _ => rfl
  | _ => rfl

/-- **What evaluation through the stores gives.** -/
theorem evM_spec (rd0 : Reader) (w : Nat → E) : ∀ (ss : List Stmt) (l : List E) (log : SLog)
    {c' : Nat}, chk l.length ss = some c' →
      (evM rd0 w l log ss).1.length = c' ∧ (∃ m, (evM rd0 w l log ss).1 = l ++ m) ∧
        log <+: (evM rd0 w l log ss).2 ∧
        ∀ s ∈ ss, ∃ (lg : SLog) (c : Nat), log <+: lg ∧
          lg ++ stWr c (B1.Val.ofArgs (evM rd0 w l log ss).1) s <+: (evM rd0 w l log ss).2 ∧
          storeHd c s ⊆ storesOf l.length ss ∧
          GoodS (ovl rd0 lg) (storesOf l.length ss) w (B1.Val.ofArgs (evM rd0 w l log ss).1) s
  | [], l, log, c', h => by
    simp only [chk, Option.some.injEq] at h
    subst h
    exact ⟨rfl, ⟨[], by simp [evM]⟩, List.prefix_refl _, by simp⟩
  | s :: ss, l, log, c', h => by
    simp only [chk] at h
    split at h
    · rename_i c1 hc1
      obtain ⟨hl1, hv1, hg1⟩ := stepS (ovl rd0 log) w l hc1
      have h' : chk (l ++ newS (ovl rd0 log) w l s).length ss = some c' := by rw [hl1]; exact h
      obtain ⟨hlen, ⟨m, hm⟩, hpre, hg⟩ := evM_spec rd0 w ss _
        (log ++ stWr l.length (B1.Val.ofArgs l) s) h'
      have hst : storesOf l.length (s :: ss) = storeHd l.length s ++ storesOf c1 ss := by
        simp [storesOf, hc1]
      refine ⟨hlen, ⟨newS (ovl rd0 log) w l s ++ m, by simp only [evM]; rw [hm, List.append_assoc]⟩,
        (List.prefix_append _ _).trans hpre, ?_⟩
      intro t ht
      rw [hst]
      simp only [evM]
      rcases List.mem_cons.mp ht with rfl | ht
      · refine ⟨log, l.length, List.prefix_refl _, ?_, fun b hb => List.mem_append_left _ hb, ?_⟩
        · have he : stWr l.length (B1.Val.ofArgs (l ++ newS (ovl rd0 log) w l t ++ m)) t =
              stWr l.length (B1.Val.ofArgs l) t := by
            rw [List.append_assoc]; exact stWr_old hc1
          rw [hm, he]; exact hpre
        · refine goodS_mono (fun b hb => List.mem_append_left _ hb) (goodS_congr (fun v hv => ?_) hg1)
          rw [hm]
          exact (ofArgs_old (by rw [hl1]; exact hv1 v hv)).symm
      · rw [hl1] at hg
        obtain ⟨lg, c, hlg, hlg2, hsub, hgt⟩ := hg t ht
        exact ⟨lg, c, (List.prefix_append _ _).trans hlg, hlg2,
          fun b hb => List.mem_append_right _ (hsub hb),
          goodS_mono (fun b hb => List.mem_append_right _ hb) hgt⟩
    · exact absurd h (by simp)

end
end LeanVM.Guest.B1.Tables
