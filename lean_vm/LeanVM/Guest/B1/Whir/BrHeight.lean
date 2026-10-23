/-
  LeanVM.Guest.B1.Whir.BrHeight

  The trees the Spec's levels open have the height the levels' positions have bits.
-/

module

public import LeanVM.Guest.B1.Whir.BrAt

/-!
# The levels' trees' heights

`chain_heights`: in an honest chain whose first commitment has the first level's height, each
level's tree has height `L.D` (its message log after its rounds plus its rate's log): the next
level's commitment is read with `levelShape L.ml next`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {logN lane : ℕ}

theorem SpLv.ws1_folds_length (L : SpLv) : L.ws1.folds.length = L.ws.folds.length + L.level.fold := by
  simp only [SpLv.ws1, List.length_append, SpLv.chs_length]

/-- **Each level after the first opens a tree of height `L.D`.** -/
theorem chain_heights : ∀ (cfg : List Whir.Level) (lvl : ℕ) (ws : WhirState) (F : Fs) (xs : List E)
    (os : List Opening) (R : List (Digest × ℕ × ℕ)) (Ls : List SpLv) (res : WhirEnd × FSt),
    SpChain logN lane lvl cfg ws F xs os R Ls res → R.length = lvl + 1 →
    ∀ i, i + 1 < Ls.length → (Ls.getD (i + 1) default).height = (Ls.getD (i + 1) default).D
  | [level], lvl, ws, F, xs, os, R, [L], res, _, _, i, hi => absurd hi (by simp)
  | level :: next :: cfg, lvl, ws, F, xs, os, R, L :: Ls, res, h, hR, i, hi => by
    obtain ⟨e1, e2, e3, e4, e5, e6, d, xsR, osR, hOk, -, -, h'⟩ := h
    rcases i with _ | i
    · obtain ⟨hl, hat, hws, -, ⟨d', hok'⟩, -⟩ := chain_at _ _ _ _ _ _ _ _ _ h'
      have h0 : 0 < Ls.length := by rw [hl]; simp
      have hat0 := hat 0 h0
      have hr := hok'.root
      rw [hat0.index, Nat.add_zero, List.getElem?_append_right (by rw [hR])] at hr
      simp only [hR, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hr
      simp only [List.getD_cons_succ]
      have hh : (levelShape L.ml next (3 * 2 ^ next.fold)).1 = (Ls.getD 0 default).height :=
        congrArg Prod.fst hr.2
      rw [← hh, levelShape]
      have hlev : (Ls.getD 0 default).level = next := by simpa using hat0.level
      have hlog : (Ls.getD 0 default).logN = L.logN := by rw [hat0.logN, e1]
      have hf1 := SpLv.ws1_folds_length (Ls.getD 0 default)
      have hf0 : (Ls.getD 0 default).ws.folds.length = L.ws1.folds.length := by
        rw [hws, SpLv.wsEnd_folds]; rfl
      simp only [SpLv.D, SpLv.ml, hlev, hlog] at hf1 ⊢
      omega
    · simp only [List.getD_cons_succ]
      exact chain_heights _ _ _ _ _ _ _ Ls res h' (by simp [hR]) i (by simpa using hi)
  | [], _, _, _, _, _, _, _, _, h, _, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, [], _, h, _, _, _ => by simp [SpChain] at h
  | [_], _, _, _, _, _, _, _ :: _ :: _, _, h, _, _, _ => by simp [SpChain] at h
  | _ :: _ :: _, _, _, _, _, _, _, [], _, h, _, _, _ => by simp [SpChain] at h

/-- **The first level opens the committed root's tree**, at the shape it was committed with. -/
theorem chain_height0 {cfg : List Whir.Level} {lvl : ℕ} {ws : WhirState} {F : Fs} {xs : List E}
    {os : List Opening} {R : List (Digest × ℕ × ℕ)} {Ls : List SpLv} {res : WhirEnd × FSt}
    (h : SpChain logN lane lvl cfg ws F xs os R Ls res) :
    ((Ls.getD 0 default).root, (Ls.getD 0 default).height, (Ls.getD 0 default).width) =
      R.getD lvl default := by
  obtain ⟨hl, hat, -, -, ⟨d, hok⟩, -⟩ := chain_at _ _ _ _ _ _ _ _ _ h
  have hne : 0 < Ls.length := by
    rcases cfg with _ | ⟨a, _ | ⟨b, cfg⟩⟩ <;> rcases Ls with _ | ⟨L, _ | ⟨L', Ls⟩⟩ <;>
      simp_all [SpChain]
  have hr := hok.root
  rw [(hat 0 hne).index, Nat.add_zero] at hr
  rw [List.getD_eq_getElem?_getD (l := R), hr]
  rfl

end
end LeanVM.Guest.B1.Whir
