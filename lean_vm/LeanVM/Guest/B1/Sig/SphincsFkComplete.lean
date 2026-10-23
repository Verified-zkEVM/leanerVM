/-
  LeanVM.Guest.B1.Sig.SphincsFkComplete

  The forest keys of `verify_sig_lean_sphincs` are sequential: a key's chains and its leaf's hash
  read the key's address, `P`, the forest address constants and the padding run.
-/

module

public import LeanVM.Guest.B1.Sig.KSeqComplete
public import LeanVM.Guest.B1.Sig.SphincsSub

/-!
# The forest keys, sequential

* `SX a1 a2`: the external values a forest block reads: two cells, `P`, the address constants
  `n165 … n205` and the padding run;
* `k48_kseq`, `fkChain_kseq`, `fkChains_kseq`, `fkArmPre_kseq`: a key's chains and its leaf's hash
  are sequential;
* `fkChains_hints`, `fkCB_lt`: their only hints are the chains' values, at the chains' increasing
  bases.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The external values a forest block reads: two cells, `P`, the address constants and the padding
run. -/
def SX (a1 a2 : V) (v : V) : Prop :=
  v = a1 ∨ v = a2 ∨ v = sPP ∨ (∃ k < 41, v = .n (165 + k)) ∨ InR sPad 5 v

variable {lo : Nat} {a1 a2 : V}

theorem sx_pp {b : Nat} (hlo : 190 ≤ lo) : KRd lo (SX a1 a2) b sPP :=
  Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), ⟨2, by omega, rfl⟩⟩

theorem sx_pad {b k : Nat} (hlo : 190 ≤ lo) (hk : k < 5) : KRd lo (SX a1 a2) b (.n (sPad + k)) :=
  Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩))), ⟨sPad + k, by simp only [sPad]; omega, rfl⟩⟩

theorem sx_cst {b k : Nat} (hlo : 206 ≤ lo) (hk : k < 41) : KRd lo (SX a1 a2) b (.n (165 + k)) :=
  Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))), ⟨165 + k, by omega, rfl⟩⟩

theorem sx_a1 {b : Nat} (h : NBv lo a1) : KRd lo (SX a1 a2) b a1 := Or.inr ⟨Or.inl rfl, h⟩

theorem sx_a2 {b : Nat} (h : NBv lo a2) : KRd lo (SX a1 a2) b a2 := Or.inr ⟨Or.inr (Or.inl rfl), h⟩

theorem krd_in {X : V → Prop} {b k : Nat} (h1 : lo ≤ k) (h2 : k < b) : KRd lo X b (.n k) :=
  Or.inl ⟨k, h1, h2, rfl⟩

theorem hint1_kseqA {X : V → Prop} (s : String) (b : Nat) :
    KSeqA lo X b (.hint (.witness s (.stack [.n b]))) (b + 1) :=
  ⟨by simp [runV], by omega⟩

/-- A 48-byte `keccak` of `P`, `a` and `v` is sequential. -/
theorem k48_kseq {a v : V} {c : Nat} (hlo : 206 ≤ lo) (hc : lo ≤ c) (ha : KRd lo (SX a1 a2) c a)
    (hv : KRd lo (SX a1 a2) c v) : KSeq lo (SX a1 a2) c (k48 a v c (c + 1)) (c + 14) :=
  ⟨c + 1, ⟨rfl, canon_word _ _, rfl⟩, c + 14, ⟨rfl, rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sx_pp (by omega)
    · exact ha.mono (by omega)
    · exact hv.mono (by omega)
    · exact sx_pad (k := 0) (by omega) (by norm_num)
    · exact sx_pad (k := 1) (by omega) (by norm_num)
    · exact sx_pad (k := 2) (by omega) (by norm_num)
    · exact sx_pad (k := 3) (by omega) (by norm_num)
    · exact sx_pad (k := 4) (by omega) (by norm_num)
    · exact krd_in hc (by omega)
    · exact sx_pad (k := 1) (by omega) (by norm_num)
    · exact sx_pad (k := 2) (by omega) (by norm_num)
    · exact sx_pad (k := 3) (by omega) (by norm_num)
    · exact sx_pad (k := 4) (by omega) (by norm_num), rfl⟩, rfl⟩

theorem fkSteps_kseq {i d : Nat} (hi : i < 6) (hd : d ≤ 4) {keyAt : V} {b : Nat} (hlo : 206 ≤ lo)
    (hb : lo ≤ b) (hk : NBv lo keyAt) : ∀ m ≤ d, KSeq lo (SX keyAt keyAt) (b + 1) ((List.range m).flatMap
      fun j => addS (.n (b + 1 + 15 * j)) keyAt (sTws (4 * i + 4 - d + j)) ::
        k48 (.n (b + 1 + 15 * j)) (if j = 0 then .n b else .n (b + 1 + 15 * j - 13))
          (b + 1 + 15 * j + 1) (b + 1 + 15 * j + 2)) (b + 1 + 15 * m)
  | 0, _ => rfl
  | m + 1, hm => by
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      refine KSeq.append (fkSteps_kseq hi hd hlo hb hk m (by omega)) ?_
      refine ⟨b + 1 + 15 * m + 1, ⟨rfl, sx_a1 hk, sx_cst (k := 4 * i + 4 - d + m) hlo (by omega), rfl⟩, ?_⟩
      have := k48_kseq (a1 := keyAt) (a2 := keyAt) (a := .n (b + 1 + 15 * m))
        (v := if m = 0 then .n b else .n (b + 1 + 15 * m - 13)) (c := b + 1 + 15 * m + 1) hlo (by omega)
        (krd_in (by omega) (by omega)) (by split <;> exact krd_in (by omega) (by omega))
      rw [show b + 1 + 15 * (m + 1) = b + 1 + 15 * m + 1 + 14 by omega]
      exact this

/-- **A chain is sequential**, its top below its end. -/
theorem fkChain_kseq {t i : Nat} (hi : i < 6) {keyAt : V} {b : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ b)
    (hk : NBv lo keyAt) :
    KSeq lo (SX keyAt keyAt) b (fkChain t i keyAt b).1 (fkChain t i keyAt b).2.1 ∧
      (∃ j, b ≤ j ∧ j < (fkChain t i keyAt b).2.1 ∧ (fkChain t i keyAt b).2.2 = .n j) ∧
      b + 1 ≤ (fkChain t i keyAt b).2.1 := by
  have hd5 := spCode_lt t i
  unfold fkChain
  simp only
  by_cases h0 : spCode t i = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨⟨b + 1, hint1_kseqA _ b, rfl⟩, ⟨b, le_rfl, by omega, rfl⟩, le_rfl⟩
  · have hs := fkSteps_kseq (i := i) (d := spCode t i) hi (by omega) hlo hb hk (spCode t i) le_rfl
    by_cases hi2 : i < 2
    · simp only [h0, hi2, ↓reduceIte]
      exact ⟨⟨b + 1, hint1_kseqA _ b, hs⟩, ⟨_, by omega, by omega, rfl⟩, by omega⟩
    · simp only [h0, hi2, ↓reduceIte]
      refine ⟨⟨b + 1, hint1_kseqA _ b, KSeq.append hs ⟨b + 2 + 15 * spCode t i,
        ⟨rfl, krd_in (by omega) (by omega), by omega⟩, rfl⟩⟩, ⟨_, by omega, by omega, rfl⟩, by omega⟩

/-- **A key's chains are sequential**, their tops below their end. -/
theorem fkChains_kseq {t : Nat} {keyAt : V} (hlo : 206 ≤ lo) (hk : NBv lo keyAt) :
    ∀ (m i b : Nat), i + m ≤ 6 → lo ≤ b →
    KSeq lo (SX keyAt keyAt) b (fkChains t keyAt m i b).1 (fkChains t keyAt m i b).2.1 ∧
      (∀ v ∈ (fkChains t keyAt m i b).2.2, ∃ j, b ≤ j ∧ j < (fkChains t keyAt m i b).2.1 ∧ v = .n j) ∧
      (fkChains t keyAt m i b).2.2.length = m
  | 0, _, _, _, _ => ⟨rfl, fun v hv => by simp [fkChains] at hv, rfl⟩
  | m + 1, i, b, hm, hb => by
      obtain ⟨c1, ⟨j0, hj0, hj1, e0⟩, c3⟩ := fkChain_kseq (t := t) (by omega : i < 6) hlo hb hk
      obtain ⟨r1, r2, r3⟩ := fkChains_kseq hlo hk m (i + 1) (fkChain t i keyAt b).2.1 (by omega)
        (by omega)
      have hle := KSeq.le r1
      refine ⟨KSeq.append c1 r1, fun v hv => ?_, by simp [fkChains, r3]⟩
      simp only [fkChains, List.mem_cons] at hv ⊢
      rcases hv with rfl | hv
      · exact ⟨j0, hj0, by omega, e0⟩
      · obtain ⟨j, h1, h2, e⟩ := r2 v hv
        exact ⟨j, by omega, h2, e⟩

/-- A key's chains' only hints are the chains' values, at the chains' bases. -/
theorem fkChains_hints {t : Nat} {keyAt : V} : ∀ (m i b : Nat), ∀ s vs,
    Stmt.atom (.hint (.witness s (.stack vs))) ∈ (fkChains t keyAt m i b).1 →
      ∃ k < m, vs = [.n (fkCB t keyAt i b k)]
  | 0, _, _, _, _, h => absurd h (by simp [fkChains])
  | m + 1, i, b, s, vs, h => by
      simp only [fkChains, List.mem_append] at h
      rcases h with h | h
      · refine ⟨0, by omega, ?_⟩
        unfold fkChain at h
        simp only at h
        split at h
        · simp only [hintW, List.mem_singleton, Stmt.atom.injEq, Atom.hint.injEq, Hint.witness.injEq,
            Dest.stack.injEq] at h
          rw [h.2]; rfl
        · split at h
          · simp only [hintW, List.mem_cons, Stmt.atom.injEq, Atom.hint.injEq, Hint.witness.injEq,
              Dest.stack.injEq, List.mem_flatMap, List.mem_range] at h
            rcases h with ⟨-, rfl⟩ | ⟨j, -, hj⟩
            · rfl
            · simp [addS, k48, cst, kecS] at hj
          · simp only [hintW, List.cons_append, List.mem_cons, Stmt.atom.injEq, Atom.hint.injEq,
              Hint.witness.injEq, Dest.stack.injEq, List.mem_append, List.mem_flatMap, List.mem_range,
              copyS] at h
            rcases h with ⟨-, rfl⟩ | (⟨j, -, hj⟩ | hj)
            · rfl
            · simp [addS, k48, cst, kecS] at hj
            · simp at hj
      · obtain ⟨k, hk, e⟩ := fkChains_hints m (i + 1) (fkChain t i keyAt b).2.1 s vs h
        refine ⟨k + 1, by omega, ?_⟩
        rw [e]
        rfl

theorem fkCB_lt {t : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ b) (hk : NBv lo keyAt) :
    ∀ k k', k < k' → k' ≤ 6 → fkCB t keyAt 0 b k < fkCB t keyAt 0 b k' := by
  have step : ∀ k, k < 6 → ∀ b', lo ≤ b' → ∀ i, i + k < 6 →
      fkCB t keyAt i b' k < fkCB t keyAt i b' (k + 1) := by
    intro k
    induction k with
    | zero =>
        intro _ b' hb' i hi
        have := (fkChain_kseq (t := t) (i := i) (by omega) hlo hb' hk).2.2
        simp only [fkCB, fkChains]
        exact this
    | succ k ih =>
        intro hk6 b' hb' i hi
        have hc := (fkChain_kseq (t := t) (i := i) (by omega) hlo hb' hk).2.2
        have := ih (by omega) (fkChain t i keyAt b').2.1 (by omega) (i + 1) (by omega)
        simp only [fkCB, fkChains] at this ⊢
        exact this
  intro k k' hkk hk'
  induction k' with
  | zero => omega
  | succ k' ih =>
      rcases Nat.lt_or_ge k k' with h | h
      · exact lt_trans (ih h (by omega)) (step k' (by omega) b hb 0 (by omega))
      · have : k = k' := by omega
        subst this
        exact step k (by omega) b hb 0 (by omega)

/-- **The key's prefix is sequential**: the chains, the leaf's address and hash, ending `15` past
the chains. -/
theorem fkArmPre_kseq {t : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ b) (hk : NBv lo keyAt) :
    KSeq lo (SX keyAt keyAt) b ((fkChains t keyAt 6 0 b).1 ++
      [addS (.n (fkChains t keyAt 6 0 b).2.1) keyAt (sTws 24),
      cst ((fkChains t keyAt 6 0 b).2.1 + 1) (word (2 ^ 63 + 1) 0 0),
      kecS [sPP, .n (fkChains t keyAt 6 0 b).2.1, (fkChains t keyAt 6 0 b).2.2.getD 0 (.n 0),
        (fkChains t keyAt 6 0 b).2.2.getD 1 (.n 0), (fkChains t keyAt 6 0 b).2.2.getD 2 (.n 0),
        (fkChains t keyAt 6 0 b).2.2.getD 3 (.n 0), (fkChains t keyAt 6 0 b).2.2.getD 4 (.n 0),
        (fkChains t keyAt 6 0 b).2.2.getD 5 (.n 0), .n ((fkChains t keyAt 6 0 b).2.1 + 1),
        .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
        (runV ((fkChains t keyAt 6 0 b).2.1 + 2) 13) false false])
      ((fkChains t keyAt 6 0 b).2.1 + 15) := by
  obtain ⟨c1, c2, c3⟩ := fkChains_kseq (t := t) (keyAt := keyAt) hlo hk 6 0 b (by omega) hb
  have hle := KSeq.le c1
  have htop : ∀ i, i < 6 → KRd lo (SX keyAt keyAt) ((fkChains t keyAt 6 0 b).2.1 + 2)
      ((fkChains t keyAt 6 0 b).2.2.getD i (.n 0)) := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [c3]; exact hi)]
    simp only [Option.getD_some]
    obtain ⟨j, h1, h2, e⟩ := c2 _ (List.getElem_mem _)
    rw [e]
    exact krd_in (by omega) (by omega)
  refine KSeq.append c1 ⟨(fkChains t keyAt 6 0 b).2.1 + 1,
    ⟨rfl, sx_a1 hk, sx_cst (k := 24) hlo (by norm_num), rfl⟩, (fkChains t keyAt 6 0 b).2.1 + 2,
    ⟨rfl, canon_word _ _, rfl⟩, (fkChains t keyAt 6 0 b).2.1 + 15, ⟨rfl, rfl, fun v hv => ?_, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sx_pp (by omega)
  · exact krd_in (by omega) (by omega)
  · exact htop 0 (by norm_num)
  · exact htop 1 (by norm_num)
  · exact htop 2 (by norm_num)
  · exact htop 3 (by norm_num)
  · exact htop 4 (by norm_num)
  · exact htop 5 (by norm_num)
  · exact krd_in (by omega) (by omega)
  · exact sx_pad (k := 1) (by omega) (by norm_num)
  · exact sx_pad (k := 2) (by omega) (by norm_num)
  · exact sx_pad (k := 3) (by omega) (by norm_num)
  · exact sx_pad (k := 4) (by omega) (by norm_num)

end
end LeanVM.Guest.B1.Sig
