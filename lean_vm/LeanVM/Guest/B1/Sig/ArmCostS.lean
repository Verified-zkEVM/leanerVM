/-
  LeanVM.Guest.B1.Sig.ArmCostS

  `ArmCost.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Sig.ArmCost
public import LeanVM.Guest.MemoryB
public import LeanVM.Guest.Memory.EvalB
public import LeanVM.Guest.B1.Sig.Model.Xmss

/-!
# `ArmCost.lean` under any `BLAKE2S` semantics

Each definition and lemma of `ArmCost.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value

@[expose] public section

variable {S : BlakeSem}

open Classical

/-! ## The arms a valid run picks -/

section Sel

variable {C : CallRel} {rd : Reader}

theorem holdsListS_onlyAtoms {σ : Val} {next : Prop} {kret : List E → Prop} :
    ∀ ss : List Stmt, onlyAtoms ss = true → Stmt.HoldsListB S C rd σ ss next kret → next
  | [], _, h => h
  | s :: ss, hs, h => by
      simp only [onlyAtoms, List.all_cons, Bool.and_eq_true] at hs
      match s, hs.1 with
      | .atom a, _ => exact holdsListS_onlyAtoms ss hs.2 ((holdsListB_cons_atom a ss next kret σ).mp h).2

/-! ### A chain's walks are atoms -/

theorem onlyAtoms_append (a b : List Stmt) : onlyAtoms (a ++ b) = (onlyAtoms a && onlyAtoms b) := by
  simp only [onlyAtoms, List.all_append]

theorem onlyAtoms_cons_atom (a : Atom) (l : List Stmt) : onlyAtoms (.atom a :: l) = onlyAtoms l := rfl

theorem onlyAtoms_cStep (w : Wots) (i s b : Nat) (v o0 o1 : V) :
    onlyAtoms (cStep w i s b v o0 o1) = true := by
  unfold cStep; split <;> rfl

theorem onlyAtoms_cSteps (w : Wots) (i : Nat) (t0 t1 : V) :
    ∀ m s b v, onlyAtoms (cSteps w i t0 t1 m s b v) = true
  | 0, s, b, v => onlyAtoms_cStep w i s b v t0 t1
  | m + 1, s, b, v => by
      rw [cSteps, onlyAtoms_append, onlyAtoms_cStep, onlyAtoms_cSteps w i t0 t1 m]; rfl

theorem onlyAtoms_cWalk (w : Wots) (i d b : Nat) (t0 t1 : V) : onlyAtoms (cWalk w i d b t0 t1) = true := by
  unfold cWalk; split
  · rfl
  · rw [hintW, onlyAtoms_cons_atom]; exact onlyAtoms_cSteps w i t0 t1 _ _ _ _

theorem onlyAtoms_cWalks (w : Wots) (tips : Nat → V × V) (first k : Nat) (fresh : Bool) :
    ∀ m r b, onlyAtoms (cWalks w tips first k fresh m r b).1 = true
  | 0, _, _ => rfl
  | m + 1, r, b => by
      simp only [cWalks]
      rw [onlyAtoms_append, onlyAtoms_cWalk, onlyAtoms_cWalks w tips first k fresh m]; rfl

/-! ### An arm's and a group's selection, under `S` -/

/-- **The fold of the arm a run takes** under `S` (`cArm_sound`'s fold, the walks skipped). -/
theorem cArmS_sel {w : Wots} {σ : Val} {tips : Nat → V × V} {power : Nat → V}
    {prodIn encIn prodOut encOut : V} {first n k : Nat} {fold fresh : Bool} {b : Nat} {next : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1
      next kret) :
    ArmFold σ power prodIn encIn prodOut encOut first n k fold ∧ next := by
  have hw : ∀ {X : Prop} (b0 : Nat),
      Stmt.HoldsListB S C rd σ (cWalks w tips first k fresh n 0 b0).1 X kret → X :=
    fun b0 h => holdsListS_onlyAtoms _ (onlyAtoms_cWalks w tips first k fresh n 0 b0) h
  have hlit : k = 0 → lit (k * 4 ^ first) = 0 := fun hk => by rw [hk, Nat.zero_mul, lit_zero]
  unfold cArm at h
  by_cases hk : k = 0
  · have hl := hlit hk
    subst hk
    simp only [↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsListB_append, cst,
        holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, mulS] at h
    · obtain ⟨h1, h2, hn⟩ := hw _ h
      exact ⟨⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h2, hl, add_zero]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨h1, h2, hn⟩ := hw _ h
      exact ⟨⟨by simp [h1], by simp only [↓reduceIte]; rw [h2, h0, hl, word_zero, add_zero]⟩, hn⟩
  · simp only [hk, ↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsListB_append, cst, addS,
        holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, mulS] at h
    · obtain ⟨h1, h2, h3, hn⟩ := hw _ h
      exact ⟨⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h3, h2]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨h1, h2, h3, hn⟩ := hw _ h
      exact ⟨⟨by simp [h1], by simp only [↓reduceIte]; rw [h3, h2, h0, word_zero]⟩, hn⟩

theorem holdsListS_match_single (x : V) (arms : List (List Stmt)) (next : Prop) (kret : List E → Prop)
    (σ : Val) :
    Stmt.HoldsListB S C rd σ [.match_ x arms] next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧ Stmt.HoldsListB S C rd σ arms[j] next kret := by
  simp only [Stmt.HoldsListB]
  exact holdsB_match_iff x arms next kret

/-- **The arm a run of a group takes** under `S` (`cGroup_sound`, the walks skipped): its hint is
`g^k` for a digit value `k < 4^n`, and the arm's folds. -/
theorem cGroupS_sel {w : Wots} {σ : Val} {power : Nat → V} {prodIn encIn : V} {first n : Nat}
    {fold : Bool} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ (cGroup w power prodIn encIn first n fold b).1 next kret) :
    (∃ k < 4 ^ n, σ (.n b) = ofK (gpow k) ∧
      ArmFold σ power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n k fold) ∧
      next := by
  simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsListB_cons_atom,
    Atom.HoldsB, true_and] at h
  obtain ⟨_, _, h⟩ := h
  obtain ⟨j, hj, hx, ha⟩ := (holdsListS_match_single _ _ _ _ _).mp h
  have hj' := hj
  rw [cArms_length] at hj'
  have hget := cArms_get_w w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) j hj'
  rw [List.getElem?_eq_getElem hj, Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  obtain ⟨h2, hn⟩ := cArmS_sel ha
  exact ⟨⟨j, hj', hx, h2⟩, hn⟩

/-! ### Groups and codewords -/

theorem cGroupsS_sel {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) {next : Prop} {kret : List E → Prop}, (p = 0 → 0 < m) →
      Stmt.HoldsListB S C rd σ (cGroups w power m p prod enc b).1 next kret →
      (∃ ks : Nat → Nat, (∀ q < m, ks q < 64 ∧
          σ (.n ((cgBases w power m p prod enc b).getD q 0)) = ofK (gpow (ks q))) ∧
        σ (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks q) 3)) ∧ next
  | 0, p, prod, enc, b, next, kret, hm, h => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨⟨fun _ => 0, fun q h => absurd h (by omega), by simp [cGroups, hp]⟩, h⟩
  | m + 1, p, prod, enc, b, next, kret, _, h => by
      simp only [cGroups, cgBases] at h ⊢
      rw [holdsListB_append] at h
      obtain ⟨⟨k, hk, hsel, hfold⟩, h⟩ := cGroupS_sel h
      obtain ⟨⟨ks, hks, hprod⟩, hn⟩ := cGroupsS_sel hmd hpow m (p + 1) _ _ _ (by omega) h
      refine ⟨⟨fun q => if q = 0 then k else ks (q - 1), fun q hq => ?_, ?_⟩, hn⟩
      · by_cases hq0 : q = 0
        · subst hq0
          exact ⟨by simpa using hk, by simpa using hsel⟩
        · obtain ⟨h1, h2⟩ := hks (q - 1) (by omega)
          refine ⟨by simpa [hq0] using h1, ?_⟩
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simpa using h2
      · unfold ArmFold groupProd at hfold
        rw [hprod, Finset.sum_range_succ']
        simp only [groupProd, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rw [hfold.1, hpow _ (pow_digitSum_lt k), pow_add]
        by_cases hp : p = 0 <;> simp [hp] <;> ring

/-- **A codeword's picked arms**: its groups' digit groups and the last digit, adding up to the
target's exponent. -/
theorem cCodewordS_sel {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) {G : Nat} (hG : 0 < G) {target : E}
    {d0 : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ (cCodeword w power G target d0 b).1 next kret) :
    ∃ (ks : Nat → Nat) (kl : Nat), (∀ q < G, ks q < 64 ∧
        σ (.n ((cgBases w power G 0 (.n 0) (.n 0) b).getD q 0)) = ofK (gpow (ks q))) ∧ kl < 4 ∧
      σ (.n (cGroups w power G 0 (.n 0) (.n 0) b).2.1) = ofK (gpow kl) ∧
      target = gen ^ (∑ q ∈ Finset.range G, digitSum (ks q) 3 + kl) ∧ next := by
  simp only [cCodeword] at h
  rw [holdsListB_append, holdsListB_append] at h
  obtain ⟨⟨ks, hks, hprod⟩, h⟩ := cGroupsS_sel hmd hpow G 0 _ _ _ (fun _ => hG) h
  obtain ⟨⟨kl, hkl, hsel, hfold⟩, h⟩ := cGroupS_sel h
  simp only [cst, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
  obtain ⟨hc, hp, -, hn⟩ := h
  rw [e_add_eq_zero_iff] at hp
  simp only [pow_one] at hkl
  refine ⟨ks, kl, hks, hkl, hsel, ?_, hn⟩
  unfold ArmFold at hfold
  rw [← hc, ← hp, hfold.1, hprod, hpow _ (by rw [digitSum_one hkl]; omega), digitSum_one hkl, pow_add]
  simp

theorem holdsListS_skip {σ : Val} {ss rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (hs : onlyAtoms ss = true) (h : Stmt.HoldsListB S C rd σ (ss ++ rest) next kret) :
    Stmt.HoldsListB S C rd σ rest next kret := by
  rw [holdsListB_append] at h
  exact holdsListS_onlyAtoms ss hs h

theorem layerSelS_of {σ : Val} {L : Nat} (hpre : XPre σ L) {a : Nat} {idx d0 : V} {next : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ (cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6)).1 next kret) :
    LayerSel σ (xW a idx) (a + 6) ∧ next := by
  obtain ⟨ks, kl, hks, hkl, hsel, ht, hn⟩ := cCodewordS_sel (S := S) (w := xW a idx) hpre.md (fun s hs => hpre.pow s hs)
    (by norm_num) h
  refine ⟨⟨ks, kl, hks, hkl, hsel, ?_⟩, hn⟩
  rw [xTarget_eq] at ht
  have hle : ∑ q ∈ Finset.range 19, digitSum (ks q) 3 ≤ 3 * 57 := by
    have := Finset.sum_le_sum fun q (_ : q ∈ Finset.range 19) => digitSum_le (ks q) 3
    simpa using this
  exact (gen_pow_inj (by norm_num) (by omega) ht).symm

/-- **The picked arms of a run of `verify_lean_xmss`**, in both layers. -/
theorem xBodyS_sel {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB S C rd σ xBody next kret) :
    LayerSel σ (xW (139 + 16) (.n 128)) (139 + 16 + 6) ∧
      LayerSel σ (xW ((xLayer 0 139 (.n 0)).2.1 + 10) (.n ((xLayer 0 139 (.n 0)).2.1 + 1)))
        ((xLayer 0 139 (.n 0)).2.1 + 10 + 6) := by
  rw [xBody_split, holdsListB_append, holdsListB_append] at h
  obtain ⟨-, ⟨L, hpre⟩, h⟩ := xPrologue_sound ((holdsListB_free xPrologue_free σ _ _).mp h)
  have e0 : (xLayer 0 139 (.n 0)).1 = xDigest0 139 ++ (xTail 0 (139 + 16) (.n 128) (.n (139 + 14))).1 := by
    rw [xLayer_zero]
  have e1 : (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).1 =
      xDigest1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 ++
        (xTail 1 ((xLayer 0 139 (.n 0)).2.1 + 10) (.n ((xLayer 0 139 (.n 0)).2.1 + 1))
          (.n ((xLayer 0 139 (.n 0)).2.1 + 8))).1 := by
    rw [xLayer_one]
  rw [holdsListB_append, e0] at h
  have h := holdsListS_skip (by decide +kernel) h
  simp only [xTail, List.append_assoc] at h
  have h := holdsListS_skip (by decide +kernel) h
  rw [holdsListB_append] at h
  obtain ⟨hs0, h⟩ := layerSelS_of hpre h
  have h := holdsListS_onlyAtoms _ (by decide +kernel) h
  rw [holdsListB_append, e1] at h
  have h := holdsListS_skip (by decide +kernel) h
  simp only [xTail, List.append_assoc] at h
  have h := holdsListS_skip (by decide +kernel) h
  rw [holdsListB_append] at h
  exact ⟨hs0, (layerSelS_of hpre h).1⟩

/-! ## The bound -/

/-- **The arms a valid run of `verify_lean_xmss` picks cost the matches' bases plus `136` steps**,
against any table bounded per arm by a base per match and `B` per chain step. -/
theorem xmssS_cw_le (tab : ℕ → Option (List ℕ)) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2, ((tab q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {σ : Val} {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsListB S C rd σ xBody next kret) :
    cwList tab σ Data.core16.body ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  rw [cwList_shaped _ _ _ xBody_shapeOk, xBody_matches]
  obtain ⟨h0, h1⟩ := xBodyS_sel h
  unfold xMatches at hA ⊢
  simp only [List.map_append, List.sum_append]
  have l0 := layer_cost_le tab A B h0 fun q hq => hA q (List.mem_append_left _ hq)
  have l1 := layer_cost_le tab A B h1 fun q hq => hA q (List.mem_append_right _ hq)
  omega

end Sel

/-- **On a valid instance of `verify_lean_xmss`**, at its valuation. -/
theorem xmssS_cw_valid (tab : ℕ → Option (List ℕ)) (A : ℕ → ℕ) (B : ℕ)
    (hA : ∀ q ∈ xMatches, ∀ k < q.2, ((tab q.1.idx).map fun l => l.getD k 0).getD 0 ≤ A q.1.idx + B * armSteps q.2 k)
    {rd : Reader} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs kids).ValidB S coreProgram rd args rets) (hf : f = "verify_lean_xmss") :
    cwList tab σ Data.core16.body ≤ (xMatches.map fun q => A q.1.idx).sum + 136 * B := by
  obtain ⟨fn, hfind, -, es, vs, hw, -, hev, -⟩ := hv
  subst hf
  rw [find_verify_lean_xmss, Option.some.injEq] at hfind
  subst hfind
  have hw' : walk σ xBody = .ret es vs := hw
  refine xmssS_cw_le (S := S) (C := fun _ _ _ => True) (rd := rd) (next := False) (kret := fun _ => True) tab A B hA ?_
  apply holdsListB_of_walk
  generalize xBody = Bd at hw' ⊢
  rw [hw']
  exact ⟨fun e he => ⟨hev e he, fun _ _ _ _ => trivial⟩, trivial⟩

end
end LeanVM.Guest.B1.Sig
