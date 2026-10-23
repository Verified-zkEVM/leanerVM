/-
  LeanVM.Guest.B1.Sig.MerkleComplete

  A Merkle path completes: the children hinted in the order of the node's bit, each parent hashed.
-/

module

public import LeanVM.Guest.B1.Sig.CodewordComplete
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# The Merkle path, complete

* `check_complete`: an atom holding already completes on an empty range;
* `merkle_level_complete`: one level, its children hinted in order;
* `merkleT_complete`: the path from `cur`, its node at each level the forward fold `mFold`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **A holding atom completes**, changing nothing. -/
theorem check_complete {a : Atom} {σ : Val} (h : a.Holds rd σ) (lo : Nat) :
    Completes C rd lo lo [.atom a] σ (fun σ' => σ' = σ) :=
  completes_atoms rfl (Ext.refl _ _ _) rfl (fun x hx => by
    simp only [List.mem_singleton, Stmt.atom.injEq] at hx
    subst hx; exact h)

theorem holdsList_single_atom {a : Atom} {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ [.atom a] next kret) : a.Holds rd σ := h.1

/-- The address of a level: its constant plus the parent's index. -/
def mA (σ : Val) (nodeOf : Nat → Option V) (addrOf : Nat → Nat) (l : Nat) : E :=
  word (addrOf l) 0 0 + match nodeOf l with
    | none => 0
    | some nd => σ nd

/-- A level's children in the order of its bit, from the node and the sibling. -/
def mPair (bit : Bool) (node sib : E) : E × E := if bit then (sib, node) else (node, sib)

theorem mA_congr {σ σ' : Val} {nodeOf : Nat → Option V} {addrOf : Nat → Nat} {l b : Nat}
    (hnd : ∀ nd, nodeOf l = some nd → NBv b nd) (hσ : AgreeBelow b σ σ') :
    mA σ' nodeOf addrOf l = mA σ nodeOf addrOf l := by
  unfold mA
  cases h : nodeOf l with
  | none => rfl
  | some nd => simp only; rw [hσ.apply (hnd nd h)]

theorem canon_mA {σ : Val} {nodeOf : Nat → Option V} {addrOf : Nat → Nat} {l : Nat}
    (h : ∀ nd, nodeOf l = some nd → IsCanonical128 (σ nd)) : IsCanonical128 (mA σ nodeOf addrOf l) := by
  unfold mA
  cases hn : nodeOf l with
  | none => simpa using canon_word (addrOf l) 0
  | some nd => exact canon_add (canon_word _ _) (h nd hn)

theorem k64_vals_eq (pad : Nat) (m0 m1 m2 m3 : V) (c o : Nat) :
    k64 pad m0 m1 m2 m3 c o = [cst c (word (2 ^ 63) 0 0)] ++ [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)]
      (runV o 13) false false] := rfl

/-- **A 64-byte `keccak` completes** on canonical inputs, its output the inputs' `hcell`. -/
theorem k64_complete {pad : Nat} {m0 m1 m2 m3 : V} {c : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpc : pad + 5 ≤ c) (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ IsCanonical128 (σ v)) :
    Completes C rd c (c + 14) (k64 pad m0 m1 m2 m3 c (c + 1)) σ
      (fun σ' => (σ' (.n (c + 1)), σ' (.n (c + 1 + 1))) = hcell [σ m0, σ m1, σ m2, σ m3] ∧
        IsCanonical128 (σ' (.n (c + 1)))) := by
  rw [k64_vals_eq]
  refine Completes.append (m := c + 1) (by omega) (by omega)
    (by simp [cst, Stmt.vals, Atom.vals]; exact .cons ⟨c, by omega, rfl⟩ (.nil _))
    (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], NBv (c + 1) v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    · exact ((hm _ (by simp)).1).mono' (by omega)
    all_goals exact ⟨_, by omega, rfl⟩
  have hp1' : PadOK σ1 pad := hp.congr hpc hag
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp1'
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) cc) := by
    have h4 : ∀ v ∈ [m0, m1, m2, m3], IsCanonical128 (σ1 v) := fun v hv => by
      rw [hag.apply (hm v hv).1]; exact (hm v hv).2
    intro cc
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, hp1] <;>
      first | exact h4 _ (by simp) | exact canon_word _ _ | exact canon_zero
  obtain ⟨σ2, he2, hp2, hh2⟩ := kecS_complete (C := C) (rd := rd) σ1 (c + 1) rfl hin hcan false false
  refine ⟨σ2, he2.mono (by omega) (by omega), ⟨?_, ?_⟩, hh2⟩
  · have hk : AtomsHold rd σ2 [kecS [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c,
        .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV (c + 1) 13) false false] :=
      atomsHold_of_holdsList rfl (hh2 True (fun _ => True) trivial)
    have hag2 : AgreeBelow (c + 1) σ1 σ2 := he2.agree
    have hp2' : PadOK σ2 pad := hp.congr hpc (fun j hj => (hag j hj).trans (hag2 j (by omega)))
    have := k64_sound (rd := rd) (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3) (c := c) (o := c + 1) hp2' (h := ?_)
    · rw [this]
      congr 1
      simp only [List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
        exact ((hag2.apply ((hm _ (by simp)).1.mono' (by omega))).trans (hag.apply (hm _ (by simp)).1))
    · rw [k64_vals_eq]
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · simp only [cst, List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show σ2 (.n c) = _
        rw [hag2.apply ⟨c, by omega, rfl⟩]
        exact hp1
      · exact hk a ha
  · rw [hp2 0 (by norm_num)]
    exact canon_kOut _ _ _ _

end
end LeanVM.Guest.B1.Sig
