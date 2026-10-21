/-
  LeanVM.Guest.B1.Main.AggLoop99CS

  `AggLoop99C.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.AggLoop99C
public import LeanVM.Guest.B1.Main.AggLoop99S
public import LeanVM.Guest.B1.Main.AggStepsCS

/-!
# `AggLoop99C.lean` under any `BLAKE2S` semantics

Each definition and lemma of `AggLoop99C.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem}

variable {rd : Reader}

section Blocks

variable {C : CallRel} {kret : List E → Prop} {c : ℕ}
  {N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 : E} {fs cc mp er ec : List E}

local notation "σ99" => l99Val c N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 fs cc mp er ec

theorem l99S_pre (k : ℕ) (hk : k < 63) :
    Stmt.HoldsListB S C rd σ99 (l99Pre (k + 1)) True kret := by
  rw [holdsS_l99Pre]
  rcases k with _ | k
  · simp only [preV, ↓reduceIte, l99Val]
    b1_lookc
    refine ⟨rfl, rfl, ?_⟩
    simp [preG, Finset.prod_range_succ, phiE_zero]
  · simp only [preV_succ, l99Val]
    b1_lookc
    exact ⟨rfl, rfl, Finset.prod_range_succ _ _⟩

theorem l99S_suf (k : ℕ) (hk : k < 63) :
    Stmt.HoldsListB S C rd σ99 (l99Suf k) True kret := by
  rw [holdsS_l99Suf]
  rcases k with _ | k
  · simp only [↓reduceIte, l99Val]
    b1_lookc
    refine ⟨rfl, rfl, ?_⟩
    simp [sufG]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 203 + 3 * (k + 1) = 206 + 3 * k by ring,
      l99Val]
    b1_lookc
    exact ⟨rfl, rfl, prod_Ico_pred _ (by omega)⟩

theorem l99S_row (hR : ∀ i < 64, LoadHolds rd eqR (62 + i) (er.getD i 0)) (k : ℕ) (hk : k < 63) :
    Stmt.HoldsListB S C rd σ99 (l99Row (k + 1)) True kret := by
  rw [holdsS_l99Row]
  rcases k with _ | k
  · simp only [↓reduceIte, l99Val]
    b1_lookc
    refine ⟨hR 1 (by omega), rfl, ?_⟩
    simp [rowG, Finset.sum_range_succ]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 459 + 3 * (k + 1) = 462 + 3 * k by ring,
      l99Val]
    b1_lookc
    exact ⟨hR _ (by omega), rfl, Finset.sum_range_succ _ _⟩

theorem l99S_rowEq (hfl : fs.length = 106) (hml : mp.length = 28) (hF : ReadsAt rd fp fs)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 8) :
    Stmt.HoldsListB S C rd σ99 (l99RowEq k) True kret := by
  rw [holdsS_l99RowEq]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp [rowEqG, rowProd]
  · simp only [show 650 + 6 * (k + 1) = 656 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [rowEqG, rowProd, Finset.prod_range_succ (n := k + 1), mul_assoc]

theorem l99S_col (hfl : fs.length = 106) (hF : ReadsAt rd fp fs)
    (hE : ∀ i < 64, LoadHolds rd eqC (62 + i) (ec.getD i 0)) (k : ℕ) (hk : k < 63) :
    Stmt.HoldsListB S C rd σ99 (l99Col (k + 1)) True kret := by
  rw [holdsS_l99Col]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨readsAt_getD' hF (by omega), hE 1 (by omega), rfl, ?_⟩
    simp [colG, Finset.sum_range_succ]
  · simp only [show 701 + 4 * (k + 1) = 705 + 4 * k by ring, l99Val]
    b1_lookc
    refine ⟨by rw [show 41 + (k + 1 + 1) = 42 + (k + 1) by omega]; exact readsAt_getD' hF (by omega),
      hE _ (by omega), rfl, ?_⟩
    simp only [colG, Finset.sum_range_succ (n := k + 2)]
    rw [show 42 + (k + 1) = 41 + (k + 2) by omega, show k + 1 + 1 = k + 2 by omega]

theorem l99S_colEq (hfl : fs.length = 106) (hml : mp.length = 28) (hF : ReadsAt rd fp fs)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 8) :
    Stmt.HoldsListB S C rd σ99 (l99ColEq k) True kret := by
  rw [holdsS_l99ColEq]
  rcases k with _ | k
  · simp only [Nat.mul_zero, Nat.add_zero, l99Val]
    b1_lookc
    b1_lit
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [colEqG, colG, colProd, colSum, Nat.reduceAdd, Finset.prod_range_one]
  · simp only [show 953 + 6 * (k + 1) = 959 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [colEqG, colProd, Finset.prod_range_succ (n := k + 1), mul_assoc]

theorem l99S_car (hcl : cc.length = 53) (hml : mp.length = 28) (hC : ReadsAt rd cp cc)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 27) :
    Stmt.HoldsListB S C rd σ99 (l99Car (k + 1)) True kret := by
  rw [holdsS_l99Car]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hC (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp [carG, carProd, Finset.prod_range_succ]
  · simp only [show 1009 + 6 * (k + 1) = 1015 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, by rw [show 23 + (k + 1 + 1) = 24 + (k + 1) by omega]; exact readsAt_getD' hC (by omega),
      rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [carG, carProd, Finset.prod_range_succ (n := k + 2)]
    rw [show 24 + (k + 1) = 23 + (k + 2) by omega, show k + 1 + 1 = k + 2 by omega]

end Blocks

/-- **`__loop99` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop99S_back {N frow eqR mpp eqC crow lamm wsums : E} (d c : ℕ) (fp cp w0 w1 l1 l2 l3 : E)
    (fs cc mp er ec : List E) (hfl : fs.length = 106) (hcl : cc.length = 53) (hml : mp.length = 28)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp) (hF : ReadsAt rd fp fs)
    (hC : ReadsAt rd cp cc) (hM : ReadsAt rd mpp mp)
    (hR : ∀ i < 64, LoadHolds rd eqR (62 + i) (er.getD i 0))
    (hE : ∀ i < 64, LoadHolds rd eqC (62 + i) (ec.getD i 0))
    (hl1 : LoadHolds rd lamm (3 * c) l1) (hl2 : LoadHolds rd lamm (3 * c + 1) l2)
    (hl3 : LoadHolds rd lamm (3 * c + 2) l3) (hw0 : LoadHolds rd wsums (2 * c) w0)
    (hw1 : LoadHolds rd wsums (2 * c + 1) w1)
    (hn0 : LoadHolds rd wsums (2 * c + 2) (w0 + l1 * l99U fs er ec mp + l2 * carProd cc mp 28))
    (hn1 : LoadHolds rd wsums (2 * c + 3)
      (w1 + l1 * fs.getD 23 0 * l99U fs er ec mp + l3 * carProd cc mp 28))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop99" [gen ^ c * gen, N, frow, eqR, mpp, eqC, crow, lamm, wsums] []) :
    coreProgram.relNB S rd (d + 1) "__loop99" [gen ^ c, N, frow, eqR, mpp, eqC, crow, lamm, wsums] [] := by
  rw [relNS_succ_iff find_loop99]
  refine ⟨l99Val c N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 fs cc mp er ec,
    by simp only [show Fn.params Data.core572 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]
      from rfl, List.map_cons, List.map_nil, l99Val]; b1_lookb, ?_⟩
  rw [core572_body, l99Body]
  simp only [holdsListB_append,
    holdsListB_flatten_range 63 (fun i => l99Pre (i + 1)) (fun _ => rfl),
    holdsListB_flatten_range 63 l99Suf (fun _ => rfl),
    holdsListB_flatten_range 64
      (fun i => [Stmt.atom (.mul (.n (394 + i)) (.n (preAt i)) (.n (sufAt (i + 1))))]) (fun _ => rfl),
    holdsListB_flatten_range 63 (fun i => l99Row (i + 1)) (fun _ => rfl),
    holdsListB_flatten_range 8 l99RowEq (fun _ => rfl),
    holdsListB_flatten_range 63 (fun i => l99Col (i + 1)) (fun _ => rfl),
    holdsListB_flatten_range 8 l99ColEq (fun _ => rfl),
    holdsListB_flatten_range 27 (fun k => l99Car (k + 1)) (fun _ => rfl)]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen,
    word_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, l99S_pre, ?_, l99S_suf, ?_, l99_num, ?_, ?_, l99S_row hR, ?_, ?_,
    l99S_rowEq hfl hml hF hM, ?_, ?_, ?_, l99S_col hfl hF hE, l99S_colEq hfl hml hF hM, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, l99S_car hcl hml hC hM, ?_⟩
  all_goals simp only [l99Val]
  all_goals b1_lookc
  all_goals try b1_lit
  · exact loadHolds_of_mul0 rfl hf
  · exact readsAt_getD' hF (by omega)
  · rfl
  · simpa using hR 0 (by omega)
  · rfl
  · exact readsAt_getD' hF (by omega)
  · simpa using hE 0 (by omega)
  · rfl
  · exact loadHolds_of_mul0 rfl hc
  · exact readsAt_getD' hC (by omega)
  · exact readsAt_getD' hM (by omega)
  · simp only [loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
    exact ⟨by ring, by ring, hl1, by ring, hw0, hl2, rfl, hn0, hw1, readsAt_getD' hF (by omega), hl3,
      rfl, hn1, hK, hnext⟩

end
end LeanVM.Guest.B1.Main
