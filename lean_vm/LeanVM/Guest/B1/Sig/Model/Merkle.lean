/-
  LeanVM.Guest.B1.Sig.Model.Merkle

  `hash_values` and `merkle_path` under a hash model (`HashValues`, `Merkle`, `WotsW` over
  `M.sem`): the chain of `hash_values` blocks is a prefix of their bytes, its last block the
  answered hash of all the values; a path's root the fold of answered node hashes.
-/

module

public import LeanVM.Guest.B1.Sig.Model.Wots

/-!
# Hashing values and paths under a hash model

* `hashValues_prefix_model`: the first `q + 1` blocks of `hash_values` leave a prefix of their
  bytes (`hashValues_prefix`, where the deployed lemma names `absorbBlocks` of them; `hvState`
  becomes the prefix);
* `hashValues_model` (`hashValues_sound`): the output is the first cell of the answered hash of
  `P`, `A` and the values;
* `mFoldWith H`: `mFold` with every node's hash answered by `H` (`mFoldWith_deployed`);
  `merkleLevel_model` (`merkleLevel_iff.mp`), `merkle_model` (`merkle_sound_w`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader}

/-! ## `hash_values` -/

theorem holdsListB_flatMap_range (f : Nat → List Stmt) (hf : ∀ j, Stmt.noRetList (f j) = true) (q : Nat)
    (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB M.sem C rd σ ((List.range q).flatMap f) next kret ↔
      (∀ j < q, Stmt.HoldsListB M.sem C rd σ (f j) True kret) ∧ next := by
  rw [List.flatMap_def, holdsListB_flatten _ (by simp [hf])]
  simp

/-- **The first blocks of `hash_values` under a model**: the chaining value after `q + 1` blocks is
a prefix of their bytes (`hashValues_prefix`). -/
theorem hashValues_prefix_model {σ : Val} {pp a : V} {val : Nat → V} {b q : Nat} {X : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ ((ivs b ++ [cst (b + 2) (mdw 64 false),
        b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) ++
        (List.range q).flatMap (hvMid val b)) X kret) :
    M.Prefix ((List.range (q + 1)).map fun j => blockBytes (hvBlock (σ pp) (σ a) (fun i => σ (val i)) j))
      (hvSt σ b (q + 1)) ∧ X := by
  rw [holdsListB_append, holdsListB_flatMap_range _ (hvMid_noRet val b)] at h
  simp only [ivs, cst, b2s, List.cons_append, List.nil_append, holdsListB_cons_atom, holdsListB_nil,
    Atom.HoldsB] at h
  obtain ⟨h0, h1, h2, h3, hmid, hX⟩ := h
  have hp := HashModel.prefix_run (M := M) (bs := []) (n := q + 1) (st := hvSt σ b)
    (md := fun j => σ (.n (b + 3 * j + 2))) (blocks := hvBlock (σ pp) (σ a) (fun i => σ (val i)))
    (by simp only [hvSt, ↓reduceIte]; exact M.prefix_nil) (fun j hj => ?_) (fun j hj => ?_)
  · exact ⟨by simpa using hp, hX⟩
  · rcases j with _ | j
    · simp [h2, mdw_eq]
    · have := (hmid j (by omega)).1
      simp only [Atom.HoldsB] at this
      rw [show b + 3 * (j + 1) + 2 = b + 5 + 3 * j by ring, this, mdw_eq]
      simp only [List.length_nil, Nat.zero_add]
  · rcases j with _ | j
    · have hiv := ivCells_eq_iv
      simp only [Value.ivCells] at hiv
      simp only [hvSt, hvBlock, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      rw [hiv, ← h0, ← h1]
      exact h3
    · have := (hmid j (by omega))
      simp only [hvMid, cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at this
      have := this.2.1
      rw [show b + 5 + 3 * j - 2 = b + 3 * (j + 1) by omega, show b + 5 + 3 * j - 1 = b + 3 * (j + 1) + 1 by omega,
        show b + 5 + 3 * j + 1 = b + 3 * (j + 1 + 1) by ring, show b + 5 + 3 * j + 2 = b + 3 * (j + 1 + 1) + 1 by ring,
        show b + 5 + 3 * j = b + 3 * (j + 1) + 2 by ring] at this
      simp only [hvSt, hvBlock, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show 4 * (j + 1) - 2 = 4 * j + 2 by omega, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
        show 4 * (j + 1) + 1 = 4 * j + 5 by ring, show 4 * (j + 1) = 4 * j + 4 by ring]
      exact this

/-- **The last block of `hash_values` under a model** (`hv_final`): from the prefix of the whole
blocks, the answered hash of all the values. -/
theorem hv_final_model {pp a : E} {vs : Nat → E} {q k : Nat} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (hk : 1 ≤ k) (hk4 : k ≤ 4)
    (hm : blockBytes m = ((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes ++
      List.replicate (64 - 16 * k) 0)
    (hcv : M.Prefix ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)) (cv0, cv1))
    (hmd : md = metadataCell (64 * (q + 1) + 16 * k) true) (hc : M.sem.check m cv0 cv1 o0 o1 md) :
    hcellWith M.H (pp :: a :: (List.range (4 * q + 2 + k)).map vs) = some (o0, o1) := by
  have hlen : (((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes).length = 16 * k := by
    rw [length_flatMap_cellBytes]; simp
  have hne : ((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes ≠ [] := by
    intro he
    have := congrArg List.length he
    rw [hlen] at this
    simp at this
    omega
  obtain ⟨d, hd, ho⟩ := M.final (st := (cv0, cv1)) hcv (by rw [hlen]; omega) (Or.inr hne) (by rw [hm, hlen])
    (by rw [hlen]; simpa [hmd] using hc)
  refine hbWith_of ?_ ho
  rw [hv_bytes_split]
  exact hd

/-- **`hash_values` under a model** (`hashValues_sound`): its output is the first cell of the
answered hash of `P`, `A` and the `n` values, for `n` a multiple of two above 2. -/
theorem hashValues_model {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat}
    (hn : n % 4 = 0 ∨ n % 4 = 2) (hn4 : 4 ≤ n) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (hashValues pp a val n b).1 next kret) :
    (∃ o, hcellWith M.H (σ pp :: σ a :: (List.range n).map fun i => σ (val i)) = some o ∧
      σ (hashValues pp a val n b).2 = o.1) ∧ next := by
  rw [hashValues_eq] at h ⊢
  dsimp only at h ⊢
  set q := (n + 1) / 4 - 1 with hq
  split_ifs at h ⊢ with h4
  · have hnq : n = 4 * q + 2 + 2 := by omega
    rw [holdsListB_append] at h
    obtain ⟨hst, h⟩ := hashValues_prefix_model h
    simp only [cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
    obtain ⟨h0, h1, h2, h3, hn'⟩ := h
    refine ⟨⟨(σ (.n (b + 5 + 3 * q + 3)), σ (.n (b + 5 + 3 * q + 4))), ?_, rfl⟩, hn'⟩
    have hcv : (σ (.n (b + 5 + 3 * q - 2)), σ (.n (b + 5 + 3 * q - 1))) = hvSt σ b (q + 1) := by
      simp only [hvSt, Nat.add_one_ne_zero, ↓reduceIte, Prod.mk.injEq]
      constructor <;> congr 2 <;> omega
    rw [h0, h1, word_zero, h2, mdw_eq] at h3
    have := hv_final_model (M := M) (k := 2) (vs := fun i => σ (val i)) (by norm_num) (by norm_num) ?_
      (by rw [hcv]; exact hst) ?_ h3
    · rw [hnq]; exact this
    · rw [blockBytes_two, show n - 2 = 4 * q + 2 + 0 by omega, show n - 1 = 4 * q + 2 + 1 by omega]
      simp [List.range_succ]
    · rw [hnq]; congr 1; ring
  · have hnq : n = 4 * q + 2 + 4 := by omega
    rw [holdsListB_append] at h
    obtain ⟨hst, h⟩ := hashValues_prefix_model h
    simp only [cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
    obtain ⟨h2, h3, hn'⟩ := h
    refine ⟨⟨(σ (.n (b + 5 + 3 * q + 1)), σ (.n (b + 5 + 3 * q + 2))), ?_, rfl⟩, hn'⟩
    have hcv : (σ (.n (b + 5 + 3 * q - 2)), σ (.n (b + 5 + 3 * q - 1))) = hvSt σ b (q + 1) := by
      simp only [hvSt, Nat.add_one_ne_zero, ↓reduceIte, Prod.mk.injEq]
      constructor <;> congr 2 <;> omega
    rw [h2, mdw_eq] at h3
    have := hv_final_model (M := M) (k := 4) (vs := fun i => σ (val i)) (by norm_num) (by norm_num) ?_
      (by rw [hcv]; exact hst) ?_ h3
    · rw [hnq]; exact this
    · simp only [blockBytes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
      rw [show n - 4 = 4 * q + 2 + 0 by omega, show n - 3 = 4 * q + 2 + 1 by omega,
        show n - 2 = 4 * q + 2 + 2 by omega, show n - 1 = 4 * q + 2 + 3 by omega]
      simp [List.range_succ]
    · rw [hnq]; congr 1; ring

/-! ## Merkle paths -/

/-- `m` levels of a path from `x` at level `l`, every node's hash answered by `H`. -/
def mFoldWith (H : List UInt8 → Option Digest) (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    Nat → Nat → E → Option E
  | 0, _, x => some x
  | m + 1, l, x =>
      (hcellWith H [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).bind fun h =>
        mFoldWith H pp A bits sibs m (l + 1) h.1

theorem mFoldWith_deployed (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ m l x, mFoldWith HashModel.deployed.H pp A bits sibs m l x = some (mFold pp A bits sibs m l x)
  | 0, _, _ => rfl
  | m + 1, l, x => by
      simp only [mFoldWith, hcellWith_deployed, Option.bind_some, mFold]
      exact mFoldWith_deployed pp A bits sibs m (l + 1) _

theorem mFoldWith_congr (H : List UInt8 → Option Digest) (pp : E) (A : Nat → E) (bits : Nat → Bool)
    {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → l' < l + m → sibs l' = sibs' l') → ∀ x,
      mFoldWith H pp A bits sibs m l x = mFoldWith H pp A bits sibs' m l x
  | 0, _, _, _ => rfl
  | m + 1, l, h, x => by
      simp only [mFoldWith]
      rw [h l le_rfl (by omega)]
      congr 1
      funext p
      exact mFoldWith_congr H pp A bits m (l + 1) (fun l' h1 h2 => h l' (by omega) (by omega)) _

/-- A path's root, answered, is canonical. -/
theorem mFoldWith_canonical {H : List UInt8 → Option Digest} {pp : E} {A : Nat → E} {bits : Nat → Bool}
    {sibs : Nat → E} : ∀ {m l : Nat} {x r : E}, 0 < m → mFoldWith H pp A bits sibs m l x = some r →
      IsCanonical128 r
  | 0, _, _, _, h, _ => absurd h (by omega)
  | 1, l, x, r, _, h => by
      simp only [mFoldWith, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, e⟩ := h
      cases e
      exact (isCanonical128_hcellWith hp).1
  | m + 2, l, x, r, _, h => by
      simp only [mFoldWith] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, -, hp⟩ := h
      exact mFoldWith_canonical (m := m + 1) (by omega) hp

/-- **One level of a path under a model** (`merkleLevel_iff.mp`): the children in the order of
the bit, the address the level's, the parent their answered hash. -/
theorem merkleLevel_model {σ : Val} {pp cur : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {l b : Nat} {β : Bool} (hβ : σ (bit l) = bitE β) {X : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs ((if isEnd l then b + 4 else b + 5) + 1) ++ [cst ((if isEnd l then b + 4 else b + 5) + 3) (mdw 64 true),
          b2s pp (.n (if isEnd l then b + 4 else b + 5)) (.n b) (.n (b + 1))
            (.n ((if isEnd l then b + 4 else b + 5) + 1)) (.n ((if isEnd l then b + 4 else b + 5) + 2))
            (.n ((if isEnd l then b + 4 else b + 5) + 4)) (.n ((if isEnd l then b + 4 else b + 5) + 5))
            (.n ((if isEnd l then b + 4 else b + 5) + 3))]) X kret) :
    (if β then σ (.n (b + 1)) else σ (.n b)) = σ cur ∧
      hcellWith M.H [σ pp, mAddr σ node addr isEnd l, σ (.n b), σ (.n (b + 1))] =
        some (σ (.n ((if isEnd l then b + 4 else b + 5) + 4)), σ (.n ((if isEnd l then b + 4 else b + 5) + 5))) ∧
      X := by
  cases he : isEnd l
  · simp only [he, Bool.false_eq_true, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and] at h
    obtain ⟨h2, h3, h2', h4, h5, h6, h7, h8, hc, hX⟩ := h
    rw [h2, hβ, h3, isChild_iff] at h2'
    rw [h6, h7, h8, h5, h4] at hc
    refine ⟨h2', ?_, hX⟩
    simpa [mAddr, he] using (compress4_model hc).2
  · simp only [he, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, true_and, List.append_nil] at h
    obtain ⟨h2, h3, h2', h4, h6, h7, h8, hc, hX⟩ := h
    rw [h2, hβ, h3, isChild_iff] at h2'
    rw [h6, h7, h8, h4] at hc
    refine ⟨h2', ?_, hX⟩
    simpa [mAddr, he] using (compress4_model hc).2

/-- **A Merkle path under a model, for its hinted siblings** (`merkle_sound_w`). -/
theorem merkle_model {σ : Val} {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} : ∀ (m l : Nat) (cur : V) (b : Nat) {next : Prop} {kret : List E → Prop},
      (∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l')) →
      Stmt.HoldsListB M.sem C rd σ (merkle pp bit node addr isEnd m l cur b).1 next kret →
      mFoldWith M.H (σ pp) (mAddr σ node addr isEnd) β (mSibs isEnd β σ m l b) m l (σ cur) =
        some (σ (merkle pp bit node addr isEnd m l cur b).2.1) ∧ next
  | 0, _, _, _, _, _, _, h => ⟨rfl, h⟩
  | m + 1, l, cur, b, next, kret, hβ, h => by
      rw [merkle_eq] at h ⊢
      dsimp only at h ⊢
      rw [holdsListB_append] at h
      obtain ⟨hord, hh, h⟩ := merkleLevel_model (hβ l le_rfl (by omega)) h
      obtain ⟨hs, hn⟩ := merkle_model m (l + 1) _ _ (fun l' h1 h2 => hβ l' (by omega) (by omega)) h
      refine ⟨?_, hn⟩
      have hc := mFoldWith_congr M.H (σ pp) (mAddr σ node addr isEnd) β
        (sibs := mSibs isEnd β σ (m + 1) l b)
        (sibs' := mSibs isEnd β σ m (l + 1) ((if isEnd l then b + 4 else b + 5) + 6)) m (l + 1)
        (fun l' h1 _ => by rw [mSibs, ite_eq_right (by omega)])
      have hsib : (if β l then mSibs isEnd β σ (m + 1) l b l else σ cur) = (if β l then σ (.n b) else σ cur) ∧
          (if β l then σ cur else mSibs isEnd β σ (m + 1) l b l) = (if β l then σ cur else σ (.n (b + 1))) := by
        rw [mSibs, ite_eq_left rfl]
        cases hb : β l <;> simp
      have hpair : [σ pp, mAddr σ node addr isEnd l, if β l then mSibs isEnd β σ (m + 1) l b l else σ cur,
          if β l then σ cur else mSibs isEnd β σ (m + 1) l b l] =
          [σ pp, mAddr σ node addr isEnd l, σ (.n b), σ (.n (b + 1))] := by
        rw [hsib.1, hsib.2]
        cases hb : β l <;> simp [hb] at hord ⊢ <;> rw [hord]
      rw [mFoldWith, hpair, hh, Option.bind_some, hc]
      exact hs

end
end LeanVM.Guest.B1.Sig
