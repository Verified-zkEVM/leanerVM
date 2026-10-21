/-
  LeanVM.Guest.B1.Comp.Sig.HashValues

  `hash_values` complete over any semantics checking its rows, and over a completeness model the
  model's answer for the cells' bytes (`hashValues_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.Sig.Values

/-!
# `hash_values` over a completeness model

`hash_values` hashes `P`, `A` and `n` values as a chain of compressions, four cells a block. Its
completeness (`hashValues_complete`) presets the chain's cells to BLAKE2s' (`hvState`). Here:

* `hashValues_compS`: over any semantics `S`, from cells `st j` after each block whose rows `S`
  checks (the first from the IV, the middle ones, the last `hvLast` into `o`), the block holds
  with its output `o.1`;
* `hashValues_comp`: over a completeness model, the cells of the model's chain of the bytes
  (`CompModel.chainSt`, the rows by `CompModel.chain_checks`), the output the first cell of the
  model's answer (`hcellC`) when it answers the bytes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader}

/-- The last block of `hash_values` over `n` values: the last two and zeros, or the last four. -/
def hvLast (vs : Nat → E) (n : Nat) : Fin 4 → E :=
  if n % 4 = 0 then ![vs (n - 2), vs (n - 1), 0, 0] else ![vs (n - 4), vs (n - 3), vs (n - 2), vs (n - 1)]

/-- One non-final block after the first, its row checked by `S` (`hvBlock_complete`). -/
theorem hvBlock_compS {σ : Val} {m0 m1 m2 m3 : V} {c : Nat} {blk : Fin 4 → E} {j : Nat}
    {cin cout : E × E}
    (hin : Out c (c + 3) m0 ∧ Out c (c + 3) m1 ∧ Out c (c + 3) m2 ∧ Out c (c + 3) m3)
    (hblk : ![σ m0, σ m1, σ m2, σ m3] = blk) (hcv : (σ (.n (c - 2)), σ (.n (c - 1))) = cin)
    (hc2 : 2 ≤ c) (hrow : S.check blk cin.1 cin.2 cout.1 cout.2 (mdw (64 * (j + 1)) false)) :
    CompletesB S C rd c (c + 3)
      [cst c (mdw (64 * (j + 1)) false),
        b2s m0 m1 m2 m3 (.n (c - 2)) (.n (c - 1)) (.n (c + 1)) (.n (c + 2)) (.n c)]
      σ (fun σ' => (σ' (.n (c + 1)), σ' (.n (c + 2))) = cout) := by
  let σ' := upds σ [(c, mdw (64 * (j + 1)) false), (c + 1, cout.1), (c + 2, cout.2)]
  have he : Ext c (c + 3) σ σ' := upds_ext σ _ (by simp)
  have hv : ∀ {v : V}, Out c (c + 3) v → σ' v = σ v := fun hv => he.out hv
  have hm : σ' (.n c) = mdw (64 * (j + 1)) false := upds_cons_self σ c _ _
  have ho1 : σ' (.n (c + 1)) = cout.1 := by
    simp only [σ']; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have ho2 : σ' (.n (c + 2)) = cout.2 := by
    simp only [σ']; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hcv' : (σ' (.n (c - 2)), σ' (.n (c - 1))) = cin := by
    rw [hv (out_of_lt ⟨c - 2, by omega, rfl⟩), hv (out_of_lt ⟨c - 1, by omega, rfl⟩), hcv]
  refine ⟨σ', he, by show (σ' _, σ' _) = cout; rw [ho1, ho2], fun next kret hn => ?_⟩
  simp only [cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
  refine ⟨hm, ?_, hn⟩
  rw [hv hin.1, hv hin.2.1, hv hin.2.2.1, hv hin.2.2.2, hblk, ho1, ho2, hm,
    show σ' (.n (c - 2)) = cin.1 from congrArg Prod.fst hcv',
    show σ' (.n (c - 1)) = cin.2 from congrArg Prod.snd hcv']
  exact hrow

/-- **`hash_values` is complete over a semantics checking its rows** (`hashValues_complete`): the
cells `st` after each block, the last block's output `o`. -/
theorem hashValues_compS {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat} (hn4 : 4 ≤ n) (hin : NB b pp ∧ NB b a ∧ ∀ i < n, NB b (val i))
    (st : Nat → E × E) (o : E × E)
    (h0 : S.check (hvBlock (σ pp) (σ a) (fun i => σ (val i)) 0) iv0 iv1 (st 1).1 (st 1).2
      (mdw 64 false))
    (hm : ∀ j < (n + 1) / 4 - 1, S.check (hvBlock (σ pp) (σ a) (fun i => σ (val i)) (j + 1))
      (st (j + 1)).1 (st (j + 1)).2 (st (j + 2)).1 (st (j + 2)).2 (mdw (64 * (j + 2)) false))
    (hf : S.check (hvLast (fun i => σ (val i)) n) (st ((n + 1) / 4)).1 (st ((n + 1) / 4)).2 o.1 o.2
      (mdw (16 * (n + 2)) true)) :
    CompletesB S C rd b (b + hashValuesSize n) (hashValues pp a val n b).1 σ
      (fun σ' => σ' (hashValues pp a val n b).2 = o.1) := by
  set vs : Nat → E := fun i => σ (val i)
  set q := (n + 1) / 4 - 1 with hq
  have hq1 : (n + 1) / 4 = q + 1 := by omega
  rw [hq1] at hf
  -- the first block
  let σ1 := upds σ [(b, iv0), (b + 1, iv1), (b + 2, mdw 64 false), (b + 3, (st 1).1), (b + 4, (st 1).2)]
  have he1 : Ext b (b + 5) σ σ1 := upds_ext σ _ (by simp)
  have hag1 : AgreeBelow b σ σ1 := he1.agree
  have hb0 : σ1 (.n b) = iv0 := upds_cons_self σ _ _ _
  have hb1 : σ1 (.n (b + 1)) = iv1 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hb2 : σ1 (.n (b + 2)) = mdw 64 false := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hb3 : σ1 (.n (b + 3)) = (st 1).1 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
      upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hb4 : σ1 (.n (b + 4)) = (st 1).2 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
      upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hk : ∀ {v : V}, NB b v → σ1 v = σ v := fun hv => he1.below hv
  -- the middle blocks
  have hMid : ∀ σ', AgreeBelow b σ σ' → (σ' (.n (b + 3)), σ' (.n (b + 4))) = st 1 →
      CompletesB S C rd (b + 5) (b + 5 + 3 * q) ((List.range q).flatMap (hvMid val b)) σ' (fun σ'' =>
        (σ'' (.n (b + 3 * (q + 1))), σ'' (.n (b + 3 * (q + 1) + 1))) = st (q + 1) ∧
        AgreeBelow b σ σ'') := by
    intro σ' hag hst
    have := CompletesB.flatMap_range (S := S) (C := C) (rd := rd) (f := hvMid val b)
      (base := fun j => b + 5 + 3 * j)
      (Inv := fun j σ'' => (σ'' (.n (b + 3 * (j + 1))), σ'' (.n (b + 3 * (j + 1) + 1))) =
        st (j + 1) ∧ AgreeBelow b σ σ'') (fun j => by omega) q
      (fun j hjq => by
        simp only [hvMid, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
          List.nil_append, List.append_nil]
        have hv := fun i (hi : i < n) => NB.mono (hin.2.2 i hi) (show b ≤ b + 5 + 3 * (j + 1) by omega)
        exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
          (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩
          (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
          (.cons ⟨_, by omega, rfl⟩ (.nil _)))))))))))
      (fun j hj σ'' ⟨hst'', hag''⟩ => by
        set c := b + 5 + 3 * j
        have hc := hvBlock_compS (S := S) (C := C) (rd := rd) (σ := σ'') (m0 := val (4 * j + 2))
          (m1 := val (4 * j + 3)) (m2 := val (4 * j + 4)) (m3 := val (4 * j + 5)) (c := c)
          (blk := hvBlock (σ pp) (σ a) vs (j + 1)) (j := j + 1) (cin := st (j + 1)) (cout := st (j + 2))
          ⟨out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)),
            out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)),
            out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)),
            out_of_lt ((hin.2.2 _ (by omega)).mono (by omega))⟩ ?_ ?_ (by omega) (hm j hj)
        · refine (hc.withExt.mono le_rfl (by omega) fun σ3 h3 => ⟨?_, fun k hk' => (hag'' k hk').trans
            (h3.2.agree k (by omega))⟩)
          rw [show b + 3 * (j + 1 + 1) + 1 = c + 2 by omega, show b + 3 * (j + 1 + 1) = c + 1 by omega]
          exact h3.1
        · simp only [hvBlock, Nat.add_one_ne_zero, ↓reduceIte]
          rw [show 4 * (j + 1) - 2 = 4 * j + 2 by omega, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
            show 4 * (j + 1) + 1 = 4 * j + 5 by ring, show 4 * (j + 1) = 4 * j + 4 by ring]
          simp only [vs]
          rw [hag''.apply (hin.2.2 _ (by omega)), hag''.apply (hin.2.2 _ (by omega)),
            hag''.apply (hin.2.2 _ (by omega)), hag''.apply (hin.2.2 _ (by omega))]
        · rw [show c - 2 = b + 3 * (j + 1) by omega, show c - 1 = b + 3 * (j + 1) + 1 by omega]
          exact hst'') σ' ⟨by simpa using hst, hag⟩
    simpa using this
  -- the first block
  have hFirst : CompletesB S C rd b (b + 5) (ivs b ++ [cst (b + 2) (mdw 64 false),
      b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) σ
      (fun σ' => AgreeBelow b σ σ' ∧ (σ' (.n (b + 3)), σ' (.n (b + 4))) = st 1) := by
    refine ⟨σ1, he1, ⟨hag1, by rw [hb3, hb4]⟩, fun next kret hn => ?_⟩
    simp only [ivs, cst, b2s, List.cons_append, List.nil_append, holdsListB_cons_atom, holdsListB_nil,
      Atom.HoldsB]
    refine ⟨hb0, hb1, hb2, ?_, hn⟩
    rw [hk hin.1, hk hin.2.1, hk (hin.2.2 0 (by omega)), hk (hin.2.2 1 (by omega)), hb0, hb1, hb2, hb3,
      hb4]
    simpa [hvBlock] using h0
  rw [hashValues_eq]
  dsimp only
  have hFM := CompletesB.append (m := b + 5) (by omega) (by omega) ?_ hFirst
    (fun σ' _ hp => hMid σ' hp.1 hp.2)
  rotate_left
  · simp only [ivs, cst, b2s, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals,
      Atom.vals, List.append_nil]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons (hin.1.mono (by omega)) (.cons (hin.2.1.mono (by omega))
      (.cons ((hin.2.2 0 (by omega)).mono (by omega)) (.cons ((hin.2.2 1 (by omega)).mono (by omega))
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))
  have hFMb : NumBelow (b + 5 + 3 * q) (Stmt.valsList ((ivs b ++ [cst (b + 2) (mdw 64 false),
      b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) ++
      (List.range q).flatMap (hvMid val b))) := by
    rw [valsList_append]
    refine NumBelow.append ?_ (numBelow_valsList_flatMap _ _ fun j hj => ?_)
    · simp only [ivs, cst, b2s, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals,
        Atom.vals, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons (hin.1.mono (by omega)) (.cons (hin.2.1.mono (by omega))
        (.cons ((hin.2.2 0 (by omega)).mono (by omega)) (.cons ((hin.2.2 1 (by omega)).mono (by omega))
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))
    · simp only [List.mem_range] at hj
      simp only [hvMid, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
        List.nil_append, List.append_nil]
      have hv := fun i (hi : i < n) => NB.mono (hin.2.2 i hi) (show b ≤ b + 5 + 3 * q by omega)
      exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
        (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))
  have hsz : hashValuesSize n = 5 + 3 * q + (if n % 4 = 0 then 5 else 3) := rfl
  split_ifs with h4
  · simp only [h4, ↓reduceIte] at hsz
    simp only [hvLast, h4, ↓reduceIte] at hf
    refine (CompletesB.append (m := b + 5 + 3 * q) (hi := b + 5 + 3 * q + 5) (by omega) (by omega) hFMb
      hFM ?_).mono le_rfl (by omega) fun _ h => h
    rintro σ'' - ⟨hst, hag⟩
    set c := b + 5 + 3 * q with hc
    let σf := upds σ'' [(c, 0), (c + 1, 0), (c + 2, mdw (16 * (n + 2)) true), (c + 3, o.1), (c + 4, o.2)]
    have hef : Ext c (c + 5) σ'' σf := upds_ext _ _ (by simp)
    have hf0 : σf (.n c) = 0 := upds_cons_self _ _ _ _
    have hf1 : σf (.n (c + 1)) = 0 := by simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf2 : σf (.n (c + 2)) = mdw (16 * (n + 2)) true := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf3 : σf (.n (c + 3)) = o.1 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
        upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf4 : σf (.n (c + 4)) = o.2 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
        upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hcv1 : σf (.n (c - 2)) = (st (q + 1)).1 := by
      rw [hef.apply (Or.inl (by omega)), show c - 2 = b + 3 * (q + 1) by omega]; exact congrArg Prod.fst hst
    have hcv2 : σf (.n (c - 1)) = (st (q + 1)).2 := by
      rw [hef.apply (Or.inl (by omega)), show c - 1 = b + 3 * (q + 1) + 1 by omega]
      exact congrArg Prod.snd hst
    have hvv : ∀ i < n, σf (val i) = vs i := fun i hi =>
      (hef.below ((hin.2.2 i hi).mono (by omega))).trans (hag.apply (hin.2.2 i hi))
    refine ⟨σf, hef, by show σf (.n (c + 3)) = o.1; exact hf3, fun next kret hn => ?_⟩
    simp only [cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
    refine ⟨by rw [hf0, word_zero], by rw [hf1, word_zero], hf2, ?_, hn⟩
    rw [hvv _ (by omega), hvv _ (by omega), hf0, hf1, hf2, hf3, hf4, hcv1, hcv2]
    exact hf
  · simp only [h4, ↓reduceIte] at hsz
    simp only [hvLast, h4, ↓reduceIte] at hf
    refine (CompletesB.append (m := b + 5 + 3 * q) (hi := b + 5 + 3 * q + 3) (by omega) (by omega) hFMb
      hFM ?_).mono le_rfl (by omega) fun _ h => h
    rintro σ'' - ⟨hst, hag⟩
    set c := b + 5 + 3 * q with hc
    let σf := upds σ'' [(c, mdw (16 * (n + 2)) true), (c + 1, o.1), (c + 2, o.2)]
    have hef : Ext c (c + 3) σ'' σf := upds_ext _ _ (by simp)
    have hf0 : σf (.n c) = mdw (16 * (n + 2)) true := upds_cons_self _ _ _ _
    have hf1 : σf (.n (c + 1)) = o.1 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf2 : σf (.n (c + 2)) = o.2 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hcv1 : σf (.n (c - 2)) = (st (q + 1)).1 := by
      rw [hef.apply (Or.inl (by omega)), show c - 2 = b + 3 * (q + 1) by omega]; exact congrArg Prod.fst hst
    have hcv2 : σf (.n (c - 1)) = (st (q + 1)).2 := by
      rw [hef.apply (Or.inl (by omega)), show c - 1 = b + 3 * (q + 1) + 1 by omega]
      exact congrArg Prod.snd hst
    have hvv : ∀ i < n, σf (val i) = vs i := fun i hi =>
      (hef.below ((hin.2.2 i hi).mono (by omega))).trans (hag.apply (hin.2.2 i hi))
    refine ⟨σf, hef.mono le_rfl (by omega), by show σf (.n (c + 1)) = o.1; exact hf1, fun next kret hn => ?_⟩
    simp only [cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
    refine ⟨hf0, ?_, hn⟩
    rw [hvv _ (by omega), hvv _ (by omega), hvv _ (by omega), hvv _ (by omega), hf0, hf1, hf2, hcv1, hcv2]
    exact hf

/-! ## Over a completeness model -/

variable {CM : CompModel}

/-- The blocks of `hash_values` over `n` values, the last zero-filled. -/
def hvBlocks (pp a : E) (vs : Nat → E) (n : Nat) (j : Nat) : Fin 4 → E :=
  if j < (n + 1) / 4 then hvBlock pp a vs j else hvLast vs n

/-- The metadata of the blocks of `hash_values`. -/
def hvMds (n : Nat) (j : Nat) : E :=
  if j < (n + 1) / 4 then metadataCell (64 * (j + 1)) false else metadataCell (16 * (n + 2)) true

theorem hvBlocks_bytes_all (pp a : E) (vs : Nat → E) {n : Nat} (hn : n % 4 = 0 ∨ n % 4 = 2)
    (hn4 : 4 ≤ n) :
    (List.range ((n + 1) / 4 + 1)).flatMap (fun j => blockBytes (hvBlocks pp a vs n j)) =
      (pp :: a :: (List.range n).map vs).flatMap cellBytes ++
        List.replicate (64 * ((n + 1) / 4 + 1) - ((pp :: a :: (List.range n).map vs).flatMap cellBytes).length)
          0 := by
  set q := (n + 1) / 4 - 1 with hq
  have hq1 : (n + 1) / 4 = q + 1 := by omega
  rw [hq1, List.range_succ, List.flatMap_append, List.flatMap_singleton]
  have hfirst : (List.range (q + 1)).flatMap (fun j => blockBytes (hvBlocks pp a vs n j)) =
      (List.range (q + 1)).flatMap (fun j => blockBytes (hvBlock pp a vs j)) := by
    refine List.flatMap_congr fun j hj => ?_
    rw [List.mem_range] at hj
    simp only [hvBlocks, hq1, hj, ↓reduceIte]
  have hlen : ((pp :: a :: (List.range n).map vs).flatMap cellBytes).length = 16 * (n + 2) := by
    rw [length_flatMap_cellBytes]; simp
  rw [hfirst, hvBlocks_bytes, hlen]
  simp only [hvBlocks, hq1, lt_irrefl, ↓reduceIte]
  rcases hn with h4 | h4
  · have hnq : n = 4 * q + 2 + 2 := by omega
    have e : (List.range n).map vs = (List.range (4 * q + 2)).map vs ++ [vs (n - 2), vs (n - 1)] := by
      rw [hnq, List.range_add, List.map_append]
      simp [List.range_succ, show 4 * q + 2 + 2 - 2 = 4 * q + 2 by omega,
        show 4 * q + 2 + 2 - 1 = 4 * q + 2 + 1 by omega]
    rw [e, hvLast]
    simp only [h4, ↓reduceIte]
    rw [blockBytes_two, show 64 * (q + 1 + 1) - 16 * (n + 2) = 32 by omega]
    simp only [List.flatMap_cons, List.flatMap_append, List.append_assoc, List.flatMap_nil, List.append_nil]
  · have hnq : n = 4 * q + 2 + 4 := by omega
    have h4' : ¬ n % 4 = 0 := by omega
    have e : (List.range n).map vs = (List.range (4 * q + 2)).map vs ++
        [vs (n - 4), vs (n - 3), vs (n - 2), vs (n - 1)] := by
      rw [hnq, List.range_add, List.map_append]
      simp [List.range_succ, show 4 * q + 2 + 4 - 4 = 4 * q + 2 by omega,
        show 4 * q + 2 + 4 - 3 = 4 * q + 2 + 1 by omega, show 4 * q + 2 + 4 - 2 = 4 * q + 2 + 2 by omega,
        show 4 * q + 2 + 4 - 1 = 4 * q + 2 + 3 by omega]
    rw [e, hvLast]
    simp only [h4', ↓reduceIte]
    rw [show 64 * (q + 1 + 1) - 16 * (n + 2) = 0 by omega]
    simp [blockBytes]

/-- **`hash_values` is complete over a completeness model** (`hashValues_complete`): over canonical
inputs whose bytes the model answers, the output is the first cell of the answer. -/
theorem hashValues_comp {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat}
    (hn : n % 4 = 0 ∨ n % 4 = 2) (hn4 : 4 ≤ n)
    (hin : NB b pp ∧ NB b a ∧ ∀ i < n, NB b (val i))
    (hcan : IsCanonical128 (σ pp) ∧ IsCanonical128 (σ a) ∧ ∀ i < n, IsCanonical128 (σ (val i)))
    (hans : AnsCells CM (σ pp :: σ a :: (List.range n).map fun i => σ (val i))) :
    CompletesB CM.sem C rd b (b + hashValuesSize n) (hashValues pp a val n b).1 σ
      (fun σ' => σ' (hashValues pp a val n b).2 =
        (hcellC CM (σ pp :: σ a :: (List.range n).map fun i => σ (val i))).1) := by
  set vs : Nat → E := fun i => σ (val i) with hvs
  obtain ⟨d, hd⟩ := hans
  have hout : hcellC CM (σ pp :: σ a :: (List.range n).map vs) = digestScalars d := by
    rw [hcellC, hbC, hd, Option.getD_some]
  rw [hout]
  have hbytes := hvBlocks_bytes_all (σ pp) (σ a) vs hn hn4
  have hlen0 : ((σ pp :: σ a :: (List.range n).map vs).flatMap cellBytes).length = 16 * (n + 2) := by
    rw [length_flatMap_cellBytes]; simp
  generalize hx : (σ pp :: σ a :: (List.range n).map vs).flatMap cellBytes = x at hd hbytes hlen0
  have hcanB : ∀ j ≤ (n + 1) / 4, ∀ r, IsCanonical128 (hvBlocks (σ pp) (σ a) vs n j r) := by
    intro j hj r
    unfold hvBlocks
    split
    · exact canonical_hvBlock hcan.1 hcan.2.1 hcan.2.2 (by omega) r
    · unfold hvLast
      split
      · fin_cases r
        · exact hcan.2.2 _ (by omega)
        · exact hcan.2.2 _ (by omega)
        · exact isCanonical128_zero
        · exact isCanonical128_zero
      · fin_cases r <;> exact hcan.2.2 _ (by omega)
  have hrow := CM.chain_checks (n := (n + 1) / 4) (blocks := hvBlocks (σ pp) (σ a) vs n) (md := hvMds n) hd
    (by rw [hlen0]; omega) (by rw [hbytes, hlen0]) hcanB
    (fun j hj => by simp only [hvMds, hj, ↓reduceIte])
    (by simp only [hvMds, lt_irrefl, ↓reduceIte, hlen0])
  have hfin : CM.chainSt x d ((n + 1) / 4 + 1) = digestScalars d := by
    have : nBlocks x = (n + 1) / 4 := by unfold nBlocks; rw [hlen0]; omega
    rw [← this, CM.chainSt_last]
  rw [← hfin]
  have hiv : CM.chainSt x d 0 = (iv0, iv1) := by rw [CM.chainSt_zero, ivCells_eq_iv]
  refine hashValues_compS hn4 hin (CM.chainSt x d) (CM.chainSt x d ((n + 1) / 4 + 1)) ?_ ?_ ?_
  · have h := hrow 0 (Nat.zero_le _)
    have h0 : 0 < (n + 1) / 4 := by omega
    simp only [hvBlocks, hvMds, h0, ↓reduceIte, Nat.zero_add, Nat.mul_one] at h
    rw [hiv] at h
    rw [mdw_eq]; exact h
  · intro j hj
    have h := hrow (j + 1) (by omega)
    have h1 : j + 1 < (n + 1) / 4 := by omega
    simp only [hvBlocks, hvMds, h1, ↓reduceIte] at h
    rw [mdw_eq, show j + 2 = j + 1 + 1 by omega]
    exact h
  · have h := hrow ((n + 1) / 4) le_rfl
    simp only [hvBlocks, hvMds, lt_irrefl, ↓reduceIte] at h
    rw [mdw_eq]; exact h

theorem hashValues_of_comp {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat}
    (hn : n % 4 = 0 ∨ n % 4 = 2) (hn4 : 4 ≤ n)
    (hin : NB b pp ∧ NB b a ∧ ∀ i < n, NB b (val i))
    (hcan : IsCanonical128 (σ pp) ∧ IsCanonical128 (σ a) ∧ ∀ i < n, IsCanonical128 (σ (val i))) :
    Completes C rd b (b + hashValuesSize n) (hashValues pp a val n b).1 σ
      (fun σ' => σ' (hashValues pp a val n b).2 =
        (hcell (σ pp :: σ a :: (List.range n).map fun i => σ (val i))).1) :=
  (hashValues_comp (CM := CompModel.deployed) hn hn4 hin hcan (ansCells_deployed _)).of_deployed

end
end LeanVM.Guest.B1.Sig
