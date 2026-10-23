/-
  LeanVM.Guest.B1.Sig.KSeqComplete

  Sequential blocks of constants, sums, copies, `KECCAK`s and hints, each defining the next fresh
  values from values below them, complete on canonical cells.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# Sequential blocks with `KECCAK`s and hints

`KSeq b ss b'`: each atom of `ss` defines the next fresh values from `b` (a canonical constant, a sum
or a copy of one value, a `KECCAK`'s thirteen, a hint's run) from values below it, ending at `b'`.
`kseq_complete`: from a valuation whose values the block reads from below `b` and whose hinted values
are canonical, the block holds of an extension on `b ..< b'` keeping the hints, all its values
canonical.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- An atom defining the values from `b` up to `m`, from values below `b`. -/
def KSeqA (b : Nat) : Atom → Nat → Prop
  | .const d c, m => d = .n b ∧ IsCanonical128 c ∧ m = b + 1
  | .add d x y, m => d = .n b ∧ NBv b x ∧ NBv b y ∧ m = b + 1
  | .copy d x, m => d = .n b ∧ NBv b x ∧ m = b + 1
  | .keccak ins outs _ _, m => outs = runV b 13 ∧ ins.length = 13 ∧ (∀ v ∈ ins, NBv b v) ∧ m = b + 13
  | .hint (.witness _ (.stack vs)), m => vs = runV b (m - b) ∧ b ≤ m
  | _, _ => False

/-- A block of such atoms from `b` to `b'`. -/
def KSeq : Nat → List Stmt → Nat → Prop
  | b, [], b' => b' = b
  | b, .atom a :: ss, b' => ∃ m, KSeqA b a m ∧ KSeq m ss b'
  | _, _ :: _, _ => False

/-- The hinted values of a block are canonical. -/
def HintsCan (σ : Val) (ss : List Stmt) : Prop :=
  ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, IsCanonical128 (σ v)

/-- The hinted values of a block are kept. -/
def HintsKept (σ σ' : Val) (ss : List Stmt) : Prop :=
  ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, σ' v = σ v

theorem KSeqA.le {b m : Nat} {a : Atom} (h : KSeqA b a m) : b ≤ m := by
  cases a with
  | const d c => obtain ⟨-, -, rfl⟩ := h; omega
  | add d x y => obtain ⟨-, -, -, rfl⟩ := h; omega
  | copy d x => obtain ⟨-, -, rfl⟩ := h; omega
  | keccak ins outs i o => obtain ⟨-, -, -, rfl⟩ := h; omega
  | hint hh =>
      match hh, h with
      | .witness _ (.stack _), ⟨_, hbm⟩ => exact hbm
  | _ => exact h.elim

theorem KSeq.le : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq b ss b' → b ≤ b'
  | _, [], _, h => by simp only [KSeq] at h; omega
  | _, .atom _ :: _, _, ⟨_, h1, h2⟩ => le_trans h1.le (KSeq.le h2)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem KSeq.append : ∀ {b m b' : Nat} {xs ys : List Stmt}, KSeq b xs m → KSeq m ys b' →
    KSeq b (xs ++ ys) b'
  | _, _, _, [], _, h1, h2 => by simp only [KSeq] at h1; subst h1; exact h2
  | _, _, _, .atom _ :: _, _, ⟨m', h1, h2⟩, h3 => ⟨m', h1, KSeq.append h2 h3⟩
  | _, _, _, .ite .. :: _, _, h, _ | _, _, _, .match_ .. :: _, _, h, _
  | _, _, _, .call .. :: _, _, h, _ | _, _, _, .callIf .. :: _, _, h, _
  | _, _, _, .dispatch .. :: _, _, h, _ | _, _, _, .ret _ :: _, _, h, _ => h.elim

theorem KSeq.atoms : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq b ss b' → atomsOnly ss = true
  | _, [], _, _ => rfl
  | _, .atom _ :: ss, _, ⟨_, _, h⟩ => (KSeq.atoms h : atomsOnly ss = true)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

theorem runV_mem_nb {o n m : Nat} (h : o + n ≤ m) {v : V} (hv : v ∈ runV o n) : NBv m v := by
  simp only [runV, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  exact ⟨o + k, by omega, rfl⟩

theorem KSeqA.vals {b m : Nat} {a : Atom} (h : KSeqA b a m) : NumBelow m a.vals := by
  have hle := h.le
  intro v hv
  cases a with
  | const d c =>
      obtain ⟨rfl, -, rfl⟩ := h
      simp only [Atom.vals, List.mem_singleton] at hv
      subst hv; exact ⟨b, by omega, rfl⟩
  | add d x y =>
      obtain ⟨rfl, hx, hy, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨b, by omega, rfl⟩
      · exact hx.mono' (by omega)
      · exact hy.mono' (by omega)
  | copy d x =>
      obtain ⟨rfl, hx, rfl⟩ := h
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨b, by omega, rfl⟩
      · exact hx.mono' (by omega)
  | keccak ins outs i o =>
      obtain ⟨rfl, -, hin, rfl⟩ := h
      simp only [Atom.vals, List.mem_append] at hv
      rcases hv with hv | hv
      · exact (hin v hv).mono' (by omega)
      · exact runV_mem_nb (by omega) hv
  | hint hh =>
      match hh, h with
      | .witness _ (.stack vs), ⟨e, _⟩ =>
          subst e
          simp only [Atom.vals, Hint.vals, Dest.vals] at hv
          exact runV_mem_nb (by omega) hv
  | _ => exact h.elim

theorem KSeq.numBelow : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq b ss b' →
    NumBelow b' (Stmt.valsList ss)
  | _, [], _, _ => NumBelow.nil _
  | _, .atom _ :: _, _, ⟨_, h1, h2⟩ => by
      rw [valsList_cons]
      exact (h1.vals.mono (KSeq.le h2)).append (KSeq.numBelow h2)
  | _, .ite .. :: _, _, h | _, .match_ .. :: _, _, h | _, .call .. :: _, _, h
  | _, .callIf .. :: _, _, h | _, .dispatch .. :: _, _, h | _, .ret _ :: _, _, h => h.elim

/-- A block's hints lie in its range. -/
theorem KSeq.hint_range : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq b ss b' →
    ∀ s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ ss → ∀ v ∈ vs, ∃ k, b ≤ k ∧ k < b' ∧ v = .n k
  | _, [], _, _, _, _, h, _, _ => absurd h (by simp)
  | b, .atom a :: ss, b', ⟨m, h1, h2⟩, s, vs, hm, v, hv => by
      have hle := KSeq.le h2
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        obtain ⟨e, hbm⟩ := h1
        subst e
        simp only [runV, List.mem_map, List.mem_range] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        exact ⟨b + k, by omega, by omega, rfl⟩
      · obtain ⟨k, h1', h2', e⟩ := KSeq.hint_range h2 s vs hm v hv
        exact ⟨k, le_trans h1.le h1', h2', e⟩
  | _, .ite .. :: _, _, h, _, _, _, _, _ | _, .match_ .. :: _, _, h, _, _, _, _, _
  | _, .call .. :: _, _, h, _, _, _, _, _ | _, .callIf .. :: _, _, h, _, _, _, _, _
  | _, .dispatch .. :: _, _, h, _, _, _, _, _ | _, .ret _ :: _, _, h, _, _, _, _, _ => h.elim

/-- **One atom of a sequential block completes**, its values canonical, a hint keeping its own. -/
theorem kseqA_complete {b m : Nat} {a : Atom} (h : KSeqA b a m) (σ : Val)
    (hc : ∀ v ∈ a.vals, NBv b v → IsCanonical128 (σ v))
    (hh : ∀ s vs, a = .hint (.witness s (.stack vs)) → ∀ v ∈ vs, IsCanonical128 (σ v)) :
    ∃ σ', Ext b m σ σ' ∧ a.Holds rd σ' ∧ (∀ j, b ≤ j → j < m → IsCanonical128 (σ' (.n j))) ∧
      ∀ s vs, a = .hint (.witness s (.stack vs)) → ∀ v ∈ vs, σ' v = σ v := by
  have hat : ∀ {σ' : Val} {Post : Val → Prop}, Completes (fun _ _ _ => True) rd b m [.atom a] σ Post →
      ∃ σ', Ext b m σ σ' ∧ Post σ' ∧ a.Holds rd σ' := fun ⟨σ', he, hp, hh'⟩ =>
    ⟨σ', he, hp, (hh' True (fun _ => True) trivial).1⟩
  cases a with
  | const d c =>
      obtain ⟨rfl, hcan, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (cst_complete (C := fun _ _ _ => True) (rd := rd) σ b c)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]; exact hcan
  | add d x y =>
      obtain ⟨rfl, hx, hy, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (addS_complete (C := fun _ _ _ => True) (rd := rd) σ b hx hy)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]
      exact canon_add (hc x (by simp [Atom.vals]) hx) (hc y (by simp [Atom.vals]) hy)
  | copy d x =>
      obtain ⟨rfl, hx, rfl⟩ := h
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (copyS_complete (C := fun _ _ _ => True) (rd := rd) σ b hx)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b by omega, hp]
      exact hc x (by simp [Atom.vals]) hx
  | keccak ins outs i o =>
      obtain ⟨rfl, hl, hin, rfl⟩ := h
      have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 (ins.map σ) cc) := by
        intro cc
        simp only [cells13]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [hl]; exact cc.isLt)]
        simp only [Option.map_some, Option.getD_some]
        exact hc _ (by simp [Atom.vals, List.getElem_mem]) (hin _ (List.getElem_mem _))
      obtain ⟨σ', he, hp, ha⟩ := hat (σ' := σ) (kecS_complete (C := fun _ _ _ => True) (rd := rd) σ b hl hin hcan i o)
      refine ⟨σ', he, ha, fun j h1 h2 => ?_, fun s vs e => by cases e⟩
      rw [show j = b + (j - b) by omega, hp (j - b) (by omega)]
      exact canon_kOut _ _ _ _
  | hint hh' =>
      match hh', h with
      | .witness s0 (.stack vs0), ⟨e, hbm⟩ =>
          refine ⟨σ, Ext.refl _ _ _, trivial, fun j h1 h2 => ?_, fun s vs _ v _ => rfl⟩
          have := hh s0 vs0 rfl (.n j) (by
            rw [e]; simp only [runV, List.mem_map, List.mem_range]; exact ⟨j - b, by omega, by
              congr 1; omega⟩)
          exact this
      | .bits .., hf => exact hf.elim
      | .bitsExp .., hf => exact hf.elim
      | .limbs .., hf => exact hf.elim
      | .log2Ceil .., hf => exact hf.elim
      | .witness _ (.heap ..), hf => exact hf.elim
  | _ => exact h.elim

/-- **A sequential block completes** on canonical cells, keeping its hints. -/
theorem kseq_complete : ∀ {b : Nat} {ss : List Stmt} {b' : Nat}, KSeq b ss b' → ∀ σ : Val,
    (∀ v ∈ Stmt.valsList ss, NBv b v → IsCanonical128 (σ v)) → HintsCan σ ss →
    ∃ σ', Ext b b' σ σ' ∧ AtomsHold rd σ' ss ∧ (∀ j, b ≤ j → j < b' → IsCanonical128 (σ' (.n j))) ∧
      HintsKept σ σ' ss
  | _, [], _, h, σ, _, _ => by
      simp only [KSeq] at h; subst h
      exact ⟨σ, Ext.refl _ _ _, fun _ ha => absurd ha (by simp), fun j h1 h2 => by omega,
        fun _ _ h => absurd h (by simp)⟩
  | b, .atom a :: ss, b', ⟨m, h1, h2⟩, σ, hc, hh => by
      have hbm := h1.le
      have hmb := KSeq.le h2
      obtain ⟨σ1, he1, ha1, hc1, hk1⟩ := kseqA_complete (rd := rd) h1 σ
        (fun v hv hb => hc v (by rw [valsList_cons]; exact List.mem_append_left _ (by simpa [Stmt.vals] using hv)) hb)
        (fun s vs e v hv => hh s vs (by rw [e]; exact List.mem_cons_self ..) v hv)
      have hag1 : AgreeBelow b σ σ1 := he1.agree
      obtain ⟨σ2, he2, ha2, hc2, hk2⟩ := kseq_complete h2 σ1 (fun v hv hm => by
          obtain ⟨k, hk, rfl⟩ := hm
          by_cases hkb : k < b
          · rw [← hag1 k hkb]
            exact hc _ (by rw [valsList_cons]; exact List.mem_append_right _ hv) ⟨k, hkb, rfl⟩
          · exact hc1 k (by omega) hk)
        (fun s vs hm v hv => by
          obtain ⟨k, hk1, hk2, rfl⟩ := KSeq.hint_range h2 s vs hm v hv
          rw [he1.apply (Or.inr hk1)]
          exact hh s vs (List.mem_cons_of_mem _ hm) _ hv)
      have hag2 : AgreeBelow m σ1 σ2 := he2.agree
      refine ⟨σ2, he1.trans he2 hbm hmb, fun x hx => ?_, fun j hj1 hj2 => ?_, fun s vs hm v hv => ?_⟩
      · rcases List.mem_cons.mp hx with e | hx
        · cases e
          exact (atom_congr a fun v hv => by
            obtain ⟨k, hk, rfl⟩ := h1.vals v hv
            exact hag2 k hk).mp ha1
        · exact ha2 x hx
      · by_cases hjm : j < m
        · rw [← hag2 j hjm]; exact hc1 j hj1 hjm
        · exact hc2 j (by omega) hj2
      · rcases List.mem_cons.mp hm with e | hm
        · obtain ⟨k, hj1, hj2, rfl⟩ : ∃ k, b ≤ k ∧ k < m ∧ v = .n k := by
            cases e
            obtain ⟨e', -⟩ := h1
            rw [e'] at hv
            simp only [runV, List.mem_map, List.mem_range] at hv
            obtain ⟨k, hk, rfl⟩ := hv
            exact ⟨b + k, by omega, by omega, rfl⟩
          rw [← hag2 k hj2]
          exact hk1 s vs (Stmt.atom.inj e).symm _ hv
        · obtain ⟨k, hj1, hj2, rfl⟩ := KSeq.hint_range h2 s vs hm v hv
          rw [hk2 s vs hm _ hv, he1.apply (Or.inr hj1)]
  | _, .ite .. :: _, _, h, _, _, _ | _, .match_ .. :: _, _, h, _, _, _ | _, .call .. :: _, _, h, _, _, _
  | _, .callIf .. :: _, _, h, _, _, _ | _, .dispatch .. :: _, _, h, _, _, _ | _, .ret _ :: _, _, h, _, _, _ =>
      h.elim

/-- **A sequential block completes**, as `Completes`. -/
theorem kseq_completes {b b' : Nat} {ss : List Stmt} (h : KSeq b ss b') (σ : Val)
    (hc : ∀ v ∈ Stmt.valsList ss, NBv b v → IsCanonical128 (σ v)) (hh : HintsCan σ ss) :
    Completes C rd b b' ss σ (fun σ' => AtomsHold rd σ' ss ∧
      (∀ j, b ≤ j → j < b' → IsCanonical128 (σ' (.n j))) ∧ HintsKept σ σ' ss) := by
  obtain ⟨σ', he, ha, hc', hk⟩ := kseq_complete (rd := rd) h σ hc hh
  exact completes_atoms h.atoms he ⟨ha, hc', hk⟩ ha

end
end LeanVM.Guest.B1.Sig
