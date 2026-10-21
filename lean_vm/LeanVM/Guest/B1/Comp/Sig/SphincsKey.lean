/-
  LeanVM.Guest.B1.Comp.Sig.SphincsKey

  `sp_forest_key__L{t}` complete over a completeness model: for canonical values at a canonical
  address whose chains and leaf the model answers, it returns the model's child leaf and `t`.
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.Sig.Values
public import LeanVM.Guest.B1.Sig.SphincsKeyComplete
public import LeanVM.Guest.B1.Sig.Model.SphincsKey

/-!
# The forest keys over a completeness model

`SphincsKeyComplete.lean` over a `CompModel`: the forest chains' ends the model's (`fChainC`,
answered `fChainAns`), the child leaf the model's answer for the tips (`fkLeafC`, answered
`FkAnsC`). Against the soundness side's answered leaf (`FkLeafWith`), `fkLeafWith_iff_C`.

* `fkStep_comp`, `fkChain_comp`, `fkChains_comp`, `fkTail_comp`, `fkBody_holdsB`: the blocks;
* `sp_forest_key_comp`: the function's relation under the model's semantics
  (`sp_forest_key_complete`), `sp_forest_key_rel_comp` from `FkLeafWith`, and at the deployed model
  `sp_forest_key_of_comp`;
* `FkCompleteC CM C` (`FkComplete`), `fkCompleteC_relB`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-! ## Forest chains and the child leaf over the model -/

variable (CM) in
/-- `n` steps of forest chain `i` from position `s` over the model (`fChain`). -/
def fChainC (pp ka : E) (i s : Nat) (v : E) : Nat → E
  | 0 => v
  | n + 1 => (hcellC CM [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + n) * stepMul), fChainC pp ka i s v n]).1

variable (CM) in
/-- The model answers every step of `fChainC`. -/
def fChainAns (pp ka : E) (i s : Nat) (v : E) : Nat → Prop
  | 0 => True
  | n + 1 => fChainAns pp ka i s v n ∧
      AnsCells CM [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + n) * stepMul), fChainC CM pp ka i s v n]

theorem fChainWith_eq_some_iff (pp ka : E) (i s : Nat) (v : E) :
    ∀ (n : Nat) {r : E}, fChainWith CM.H pp ka i s v n = some r ↔
      fChainAns CM pp ka i s v n ∧ fChainC CM pp ka i s v n = r
  | 0, r => by simp [fChainWith, fChainAns, fChainC]
  | n + 1, r => by
      simp only [fChainWith, fChainAns, fChainC, Option.bind_eq_some_iff, Option.map_eq_some_iff]
      constructor
      · rintro ⟨y, hy, o, ho, rfl⟩
        obtain ⟨ha, rfl⟩ := (fChainWith_eq_some_iff pp ka i s v n).mp hy
        obtain ⟨ha', rfl⟩ := hcellWith_eq_some_iff.mp ho
        exact ⟨⟨ha, ha'⟩, rfl⟩
      · rintro ⟨⟨ha, ha'⟩, rfl⟩
        exact ⟨_, (fChainWith_eq_some_iff pp ka i s v n).mpr ⟨ha, rfl⟩, _, hcellWith_of_ans ha', rfl⟩

theorem fChainC_deployed (pp ka : E) (i s : Nat) (v : E) :
    ∀ n, fChainC CompModel.deployed pp ka i s v n = fChain pp ka i s v n
  | 0 => rfl
  | n + 1 => by simp only [fChainC, fChain, fChainC_deployed pp ka i s v n]; rfl

theorem fChainAns_deployed (pp ka : E) (i s : Nat) (v : E) :
    ∀ n, fChainAns CompModel.deployed pp ka i s v n
  | 0 => trivial
  | n + 1 => ⟨fChainAns_deployed pp ka i s v n, ansCells_deployed _⟩

theorem canonical_fChainC (pp ka : E) (i s : Nat) {x : E} (hx : IsCanonical128 x) :
    ∀ n, IsCanonical128 (fChainC CM pp ka i s x n)
  | 0 => hx
  | _ + 1 => (isCanonical128_hcellC _).1

/-- Step `j` of an answered chain is answered. -/
theorem fChainAns_step {pp ka : E} {i s : Nat} {v : E} :
    ∀ {n : Nat}, fChainAns CM pp ka i s v n → ∀ j < n,
      AnsCells CM [pp, ka + eOfNat (tw 15 + i * 2 ^ 43 + (s + j) * stepMul), fChainC CM pp ka i s v j]
  | 0, _, _, h => absurd h (by omega)
  | n + 1, ⟨h, h'⟩, j, hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact fChainAns_step h j hj
      · exact h'

variable (CM) in
/-- The child leaf of forest key `t` over the model (`fkLeaf`). -/
def fkLeafC (t : Nat) (pp ka : E) (vals : Nat → E) : E :=
  (hcellC CM (pp :: (ka + eOfNat (tw 16)) :: (List.range 6).map fun k =>
    fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k))).1

variable (CM) in
/-- The model answers the six chains of forest key `t` and the hash of their ends. -/
def FkAnsC (t : Nat) (pp ka : E) (vals : Nat → E) : Prop :=
  (∀ k < 6, fChainAns CM pp ka k (4 - spCode t k) (vals k) (spCode t k)) ∧
    AnsCells CM (pp :: (ka + eOfNat (tw 16)) :: (List.range 6).map fun k =>
      fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k))

theorem fkLeafC_deployed (t : Nat) (pp ka : E) (vals : Nat → E) :
    fkLeafC CompModel.deployed t pp ka vals = fkLeaf t pp ka vals := by
  simp only [fkLeafC, fkLeaf, fChainC_deployed]; rfl

theorem fkAnsC_deployed (t : Nat) (pp ka : E) (vals : Nat → E) : FkAnsC CompModel.deployed t pp ka vals :=
  ⟨fun _ _ => fChainAns_deployed _ _ _ _ _ _, ansCells_deployed _⟩

/-- **The answered child leaf is the model's** (`fkLeafWith_deployed`). -/
theorem fkLeafWith_iff_C {t : Nat} {pp ka : E} {vals : Nat → E} {leaf : E} :
    FkLeafWith CM.H t pp ka vals leaf ↔ FkAnsC CM t pp ka vals ∧ leaf = fkLeafC CM t pp ka vals := by
  constructor
  · rintro ⟨ends, he, o, ho, rfl⟩
    have hE : ∀ k < 6, fChainAns CM pp ka k (4 - spCode t k) (vals k) (spCode t k) ∧
        fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k) = ends k :=
      fun k hk => (fChainWith_eq_some_iff _ _ _ _ _ _).mp (he k hk)
    have hmap : (List.range 6).map ends = (List.range 6).map fun k =>
        fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k) :=
      List.map_congr_left fun k hk => ((hE k (List.mem_range.mp hk)).2).symm
    rw [hmap] at ho
    obtain ⟨ha, rfl⟩ := hcellWith_eq_some_iff.mp ho
    exact ⟨⟨fun k hk => (hE k hk).1, ha⟩, rfl⟩
  · rintro ⟨⟨hc, ha⟩, rfl⟩
    exact ⟨fun k => fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k),
      fun k hk => (fChainWith_eq_some_iff _ _ _ _ _ _).mpr ⟨hc k hk, rfl⟩, _, hcellWith_of_ans ha, rfl⟩

/-! ## A step of a forest chain -/

/-- **A step is complete over the model** (`fkStep_complete`): its cells answered, the next value
is the model's answer for them. -/
theorem fkStep_comp {σ : Val} {i d b j : Nat} (hb : 2 ≤ b) (hpp : IsCanonical128 (σ (.n 1)))
    (hka : IsCanonical128 (σ (.n 0))) (hprev : IsCanonical128 (σ (fkPrev b j)))
    (ha : AnsCells CM [σ (.n 1), σ (.n 0) + eOfNat (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul),
      σ (fkPrev b j)]) :
    CompletesB CM.sem C rd (b + 1 + 8 * j) (b + 1 + 8 * j + 8) (fkStepBlock i d b j) σ (fun σ' =>
      σ' (.n (b + 1 + 8 * j + 6)) = (hcellC CM [σ (.n 1),
        σ (.n 0) + eOfNat (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul), σ (fkPrev b j)]).1 ∧
      AgreeBelow (b + 1 + 8 * j) σ σ') := by
  set c := b + 1 + 8 * j with hc
  set A := word (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul) 0 0 with hA
  set o := hcellC CM [σ (.n 1), σ (.n 0) + A, σ (fkPrev b j)]
  set vs : List E := [A, σ (.n 0) + A, 0, iv0, iv1, mdw 48 true, o.1, o.2]
  set σ' := upds σ ((List.range 8).map fun k => (c + k, vs.getD k 0))
  have he : Ext c (c + 8) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 8, σ' (.n (c + k)) = vs.getD k 0 := upds_range_at c _ 8 σ
  have hk : ∀ k < c, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hpv : σ' (fkPrev b j) = σ (fkPrev b j) := by
    unfold fkPrev; split <;> exact hk _ (by omega)
  have hAc : IsCanonical128 (σ (.n 0) + A) := isCanonical128_add hka (isCanonical128_word _ _)
  have ha' : AnsCells CM [σ (.n 1), σ (.n 0) + A, σ (fkPrev b j)] := by
    rw [hA, word_eq_eOfNat]; exact ha
  have hcmp := compress3_C (CM := CM) ⟨hpp, hAc, hprev⟩ ha'
  refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 6 (by omega)]
    simp only [vs, o, A, List.getD_cons_succ, List.getD_cons_zero, word_eq_eOfNat]
  · simp only [fkStepBlock, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsListB_cons_atom,
      holdsListB_nil, Atom.HoldsB]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    have hprev' : σ' (if j = 0 then .n b else .n (c - 2)) = σ (fkPrev b j) := hpv
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), show c + 3 + 1 = c + 4 by omega, v 4 (by omega),
      v 5 (by omega), v 6 (by omega), v 7 (by omega), hk 0 (by omega), hk 1 (by omega), hprev']
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, word_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcmp, hn⟩ <;> trivial

/-- **A forest chain is complete over the model** (`fkChain_complete`): from the value `x`, its
steps answered, its tip is the model's chain walked its deficit. -/
theorem fkChain_comp {σ : Val} {i d b : Nat} (hb : 2 ≤ b) (hpp : IsCanonical128 (σ (.n 1)))
    (hka : IsCanonical128 (σ (.n 0))) {x : E} (hx : IsCanonical128 x)
    (ha : fChainAns CM (σ (.n 1)) (σ (.n 0)) i (4 - d) x d) :
    CompletesB CM.sem C rd b (b + fkChainSize d) (fkChain i d b) σ (fun σ' =>
      σ' (.n (fkTip d b)) = fChainC CM (σ (.n 1)) (σ (.n 0)) i (4 - d) x d ∧ AgreeBelow b σ σ') := by
  rw [fkChain_eq, hintW]
  apply CompletesB.hint_cons
  let σ1 := Function.update σ (.n b) x
  have he1 : Ext b (b + 1) σ σ1 := ext_update σ x le_rfl (by omega)
  have h01 : σ1 (.n 0) = σ (.n 0) ∧ σ1 (.n 1) = σ (.n 1) :=
    ⟨Function.update_of_ne (by simp; omega) _ _, Function.update_of_ne (by simp; omega) _ _⟩
  refine CompletesB.of_ext (he1.mono le_rfl (by simp [fkChainSize])) ?_
  have hfm := CompletesB.flatMap_range (S := CM.sem) (C := C) (rd := rd) (f := fkStepBlock i d b)
    (base := fun j => b + 1 + 8 * j)
    (Inv := fun j σ' => σ' (.n 0) = σ (.n 0) ∧ σ' (.n 1) = σ (.n 1) ∧
      fkAfter σ' b j = fChainC CM (σ (.n 1)) (σ (.n 0)) i (4 - d) x j ∧ AgreeBelow b σ σ')
    (fun j => by omega) d (fun j _ => by have := fkStepBlock_below i d b j hb; simpa [Nat.mul_add, Nat.add_assoc]
      using this)
    (fun j hj σ' ⟨h0, h1, hjv, hag⟩ => by
      have hpc : IsCanonical128 (σ' (fkPrev b j)) := by
        rw [fkPrev_after σ' b j, hjv]; exact canonical_fChainC _ _ _ _ hx _
      refine (fkStep_comp (CM := CM) (C := C) (rd := rd) (i := i) (d := d) hb (by rw [h1]; exact hpp)
        (by rw [h0]; exact hka) hpc (by rw [h0, h1, fkPrev_after σ' b j, hjv]; exact fChainAns_step ha j hj)).mono
        le_rfl (by omega) fun σ'' ⟨ho, hag'⟩ => ⟨?_, ?_, ?_, ?_⟩
      · rw [← hag' 0 (by omega), h0]
      · rw [← hag' 1 (by omega), h1]
      · rw [fkAfter, ite_neg' (by omega), show b + 1 + 8 * (j + 1 - 1) + 6 = b + 1 + 8 * j + 6 by omega, ho, h0,
          h1, fkPrev_after σ' b j, hjv, fChainC]
      · exact fun k hk => (hag k hk).trans (hag' k (by omega)))
    σ1 ⟨h01.1, h01.2, by simp [fkAfter, σ1, fChainC], fun k hk => (he1.agree k hk)⟩
  refine hfm.mono (by omega) (by simp [fkChainSize]; omega) fun σ' ⟨_, _, hjv, hag⟩ => ⟨?_, hag⟩
  rw [fkTip_after σ' d b, hjv]

/-- **The chains of a forest key are complete over the model** (`fkChains_complete`). -/
theorem fkChains_comp (t : Nat) {pp ka : E} (hpp : IsCanonical128 pp) (hka : IsCanonical128 ka)
    (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) :
    ∀ (m i b : Nat) (σ : Val), 2 ≤ b → σ (.n 1) = pp → σ (.n 0) = ka →
      (∀ r < m, fChainAns CM pp ka (i + r) (4 - spCode t (i + r)) (vals (i + r)) (spCode t (i + r))) →
      CompletesB CM.sem C rd b (fkChains t m i b).2.1 (fkChains t m i b).1 σ (fun σ' =>
        (∀ r < m, σ' (.n ((fkChains t m i b).2.2.getD r 0)) =
          fChainC CM pp ka (i + r) (4 - spCode t (i + r)) (vals (i + r)) (spCode t (i + r))) ∧
        AgreeBelow b σ σ')
  | 0, _, b, σ, _, _, _, _ => CompletesB.nil _ _ _ ⟨fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | m + 1, i, b, σ, hb, h1, h0, ha => by
      simp only [fkChains]
      refine CompletesB.append (m := b + fkChainSize (spCode t i)) (by omega)
        (fkChains_snd t m (i + 1) _) (fkChain_below i _ b hb)
        (fkChain_comp hb (by rw [h1]; exact hpp) (by rw [h0]; exact hka) (hvals i)
          (by rw [h1, h0]; simpa using ha 0 (by omega)))
        fun σ1 _ ⟨htip, hag1⟩ => ?_
      refine (fkChains_comp t hpp hka vals hvals m (i + 1) _ σ1 (by omega)
        (by rw [← hag1 1 (by omega), h1]) (by rw [← hag1 0 (by omega), h0])
        (fun r hr => by rw [show i + 1 + r = i + (r + 1) by omega]; exact ha (r + 1) (by omega))).mono
        le_rfl le_rfl
        fun σ2 ⟨hr, hag2⟩ => ⟨fun r hr' => ?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
      rcases r with _ | r
      · simp only [List.getD_cons_zero, Nat.add_zero]
        rw [← hag2 _ (fkTip_lt _ _), htip, h1, h0]
      · simp only [List.getD_cons_succ]
        rw [hr r (by omega), show i + 1 + r = i + (r + 1) by omega]

/-! ## The key -/

/-- **The statements after the chains are complete over the model** (`fkTail_complete`): the
model's child leaf of the tips, answered, and `t`. -/
theorem fkTail_comp (t : Nat) {σ : Val} {B : Nat} {tip : Nat → V} (htip : ∀ i < 6, NB B (tip i))
    (hpp : IsCanonical128 (σ (.n 1))) (hka : IsCanonical128 (σ (.n 0))) (h2 : 2 ≤ B)
    (htc : ∀ i < 6, IsCanonical128 (σ (tip i)))
    (hans : AnsCells CM (σ (.n 1) :: (σ (.n 0) + eOfNat (tw 16)) :: (List.range 6).map fun i => σ (tip i))) :
    CompletesB CM.sem C rd B (B + 12) (fkTail t B tip) σ (fun σ' =>
      σ' (.n (B + 10)) = (hcellC CM (σ (.n 1) :: (σ (.n 0) + eOfNat (tw 16)) ::
        (List.range 6).map fun i => σ (tip i))).1 ∧ σ' (.n (B + 11)) = word t 0 0) := by
  set A := σ (.n 0) + word (tw 16) 0 0 with hA
  set b0 : Fin 4 → E := ![σ (.n 1), A, σ (tip 0), σ (tip 1)]
  set b1 : Fin 4 → E := ![σ (tip 2), σ (tip 3), σ (tip 4), σ (tip 5)]
  have ebytes : blockBytes b0 ++ blockBytes b1 =
      (σ (.n 1) :: (σ (.n 0) + eOfNat (tw 16)) :: (List.range 6).map fun i => σ (tip i)).flatMap cellBytes := by
    simp only [b0, b1, A, blockBytes_four, ← List.flatMap_append, word_eq_eOfNat]
    simp [List.range_succ]
  set x := hmidC CM b0
  set o := hbC CM (blockBytes b0 ++ blockBytes b1)
  set vs : List E := [word (tw 16) 0 0, A, iv0, iv1, mdw 64 false, x.1, x.2, mdw 128 true, o.1, o.2, o.1,
    word t 0 0]
  set σ' := upds σ ((List.range 12).map fun k => (B + k, vs.getD k 0))
  have he : Ext B (B + 12) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 12, σ' (.n (B + k)) = vs.getD k 0 := upds_range_at B _ 12 σ
  have hk : ∀ k < B, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have htk : ∀ i < 6, σ' (tip i) = σ (tip i) := fun i hi => by
    obtain ⟨k, hk', e⟩ := htip i hi; rw [e]; exact hk k hk'
  have hr : (blockBytes b1).length = 64 := length_blockBytes _
  have hcmp := compress_two_C (CM := CM) (b0 := b0) (b1 := b1) (r := blockBytes b1) (by rw [hr]; simp)
    (by rw [hr]) (by rw [hr]; omega)
    (fin4_canonical.mpr ⟨hpp, isCanonical128_add hka (isCanonical128_word _ _), htc 0 (by omega),
      htc 1 (by omega)⟩)
    (fin4_canonical.mpr ⟨htc 2 (by omega), htc 3 (by omega), htc 4 (by omega), htc 5 (by omega)⟩)
    (by rw [ebytes]; exact hans)
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨?_, ?_⟩, fun next kret hn => ?_⟩
  · rw [v 10 (by omega)]
    simp only [vs, o, List.getD_cons_succ, List.getD_cons_zero, hcellC]
    rw [ebytes]
  · rw [v 11 (by omega)]; rfl
  · simp only [fkTail, cst, addS, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), v 6 (by omega),
      v 7 (by omega), v 8 (by omega), v 9 (by omega), v 10 (by omega), v 11 (by omega), hk 0 (by omega),
      hk 1 (by omega), htk 0 (by omega), htk 1 (by omega), htk 2 (by omega), htk 3 (by omega), htk 4 (by omega),
      htk 5 (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, ?_, ?_, ?_, hc1, ?_, hc2, ?_, ?_, hn⟩ <;> trivial

/-- **`sp_forest_key__L{t}`'s body holds over the model** (`fkBody_holds`), of canonical values at
a canonical address whose chains and leaf the model answers. -/
theorem fkBody_holdsB (t : Nat) {pp ka : E} (hpp : IsCanonical128 pp) (hka : IsCanonical128 ka)
    (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) (hans : FkAnsC CM t pp ka vals) :
    ∃ σ : Val, σ (.n 0) = ka ∧ σ (.n 1) = pp ∧
      Stmt.HoldsListB CM.sem C rd σ (fkBody t) False
        (fun rs => rs = [fkLeafC CM t pp ka vals, word t 0 0]) := by
  set σ0 : Val := fun v => if v = .n 0 then ka else if v = .n 1 then pp else 0
  have h00 : σ0 (.n 0) = ka := by simp [σ0]
  have h01 : σ0 (.n 1) = pp := by simp [σ0]
  have hB := fkChains_snd t 6 0 2
  have htipB : ∀ i < 6, NB (fkChains t 6 0 2).2.1 (V.n ((fkChains t 6 0 2).2.2.getD i 0)) :=
    fun i hi => ⟨_, fkChains_tip_lt t 6 0 2 i hi, rfl⟩
  have hc : CompletesB CM.sem C rd 2 ((fkChains t 6 0 2).2.1 + 12) ((fkChains t 6 0 2).1 ++
      fkTail t (fkChains t 6 0 2).2.1 (fun i => .n ((fkChains t 6 0 2).2.2.getD i 0))) σ0 (fun σ' =>
        σ' (.n ((fkChains t 6 0 2).2.1 + 10)) = fkLeafC CM t pp ka vals ∧
        σ' (.n ((fkChains t 6 0 2).2.1 + 11)) = word t 0 0) :=
    CompletesB.append (m := (fkChains t 6 0 2).2.1) (by omega) (by omega) (fkChains_below t 6 0 2 le_rfl)
      (fkChains_comp t hpp hka vals hvals 6 0 2 σ0 le_rfl h01 h00 (fun r hr => by simpa using hans.1 r hr))
    (fun σ1 _ ⟨htips, hag⟩ => by
      have hmap : ((List.range 6).map fun i => σ1 (V.n ((fkChains t 6 0 2).2.2.getD i 0))) =
          (List.range 6).map fun k => fChainC CM pp ka k (4 - spCode t k) (vals k) (spCode t k) := by
        refine List.map_congr_left fun k hk => ?_
        rw [List.mem_range] at hk
        rw [htips k hk, Nat.zero_add]
      exact (fkTail_comp (CM := CM) (C := C) (rd := rd) t htipB
        (by rw [← hag 1 (by omega), h01]; exact hpp) (by rw [← hag 0 (by omega), h00]; exact hka) (by omega)
        (fun i hi => by rw [htips i hi]; exact canonical_fChainC _ _ _ _ (hvals _) _)
        (by rw [← hag 0 (by omega), ← hag 1 (by omega), h00, h01, hmap]; exact hans.2)).mono le_rfl le_rfl
        fun σ2 h => ⟨by rw [h.1, ← hag 0 (by omega), ← hag 1 (by omega), h00, h01, hmap, fkLeafC], h.2⟩)
  obtain ⟨σ', he, ⟨hlf, hw⟩, hh⟩ := hc
  refine ⟨σ', (he.apply (Or.inl (by omega))).trans h00, (he.apply (Or.inl (by omega))).trans h01, ?_⟩
  rw [fkBody_split, holdsListB_append]
  refine hh _ _ ?_
  simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil, hlf, hw]

/-- **`sp_forest_key__L{t}` is complete over the model** (`sp_forest_key_complete`): at a canonical
address and parameter, for canonical values whose chains and leaf the model answers, it returns the
model's child leaf and `t`. -/
theorem sp_forest_key_comp {t : Nat} (ht : t < 256) {ka pp : E} (hka : IsCanonical128 ka)
    (hpp : IsCanonical128 pp) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k))
    (hans : FkAnsC CM t pp ka vals) :
    coreProgram.RelB CM.sem rd (fkNames.getD t "") [ka, pp] [fkLeafC CM t pp ka vals, word t 0 0] := by
  obtain ⟨σ, h0, h1, hb⟩ := fkBody_holdsB (C := coreProgram.RelB CM.sem rd) (rd := rd) t hpp hka vals hvals hans
  exact (relB_iff_sem (find_fk ht) _ _).mpr ⟨σ, by simp [fkFn, h0, h1], hb⟩

/-- `sp_forest_key__L{t}` over the model, from the soundness side's answered leaf. -/
theorem sp_forest_key_rel_comp {t : Nat} (ht : t < 256) {ka pp : E} (hka : IsCanonical128 ka)
    (hpp : IsCanonical128 pp) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) {leaf : E}
    (h : FkLeafWith CM.H t pp ka vals leaf) :
    coreProgram.RelB CM.sem rd (fkNames.getD t "") [ka, pp] [leaf, word t 0 0] := by
  obtain ⟨hans, rfl⟩ := fkLeafWith_iff_C.mp h
  exact sp_forest_key_comp ht hka hpp vals hvals hans

/-- The deployed `sp_forest_key_complete`, from the model's at `CompModel.deployed`. -/
theorem sp_forest_key_of_comp {t : Nat} (ht : t < 256) {ka pp : E} (hka : IsCanonical128 ka)
    (hpp : IsCanonical128 pp) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) :
    coreProgram.Rel rd (fkNames.getD t "") [ka, pp] [fkLeaf t pp ka vals, word t 0 0] := by
  have := sp_forest_key_comp (CM := CompModel.deployed) (rd := rd) ht hka hpp vals hvals
    (fkAnsC_deployed t pp ka vals)
  rwa [fkLeafC_deployed, show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed] at this

/-- The forest keys are complete under `C` over the model (`FkComplete`). -/
def FkCompleteC (CM : CompModel) (C : CallRel) : Prop :=
  ∀ t < 256, ∀ ka pp : E, IsCanonical128 ka → IsCanonical128 pp → ∀ vals : Nat → E,
    (∀ k, IsCanonical128 (vals k)) → FkAnsC CM t pp ka vals →
    C (fkNames.getD t "") [ka, pp] [fkLeafC CM t pp ka vals, word t 0 0]

theorem fkCompleteC_relB : FkCompleteC CM (coreProgram.RelB CM.sem rd) :=
  fun _ ht _ _ hka hpp vals hvals hans => sp_forest_key_comp ht hka hpp vals hvals hans

end
end LeanVM.Guest.B1.Sig
