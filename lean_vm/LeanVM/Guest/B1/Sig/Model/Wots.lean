/-
  LeanVM.Guest.B1.Sig.Model.Wots

  The WOTS+C chains and codeword of the signature verifiers under a hash model: a chain step, the
  steps of a chain, a walk, an arm, a digit group, groups in sequence and the codeword
  (`Chain`, `Walk`, `Arm`, `Group`, `Codeword`, `WotsW` over `M.sem`), each chain's end the
  answered hashes of its steps.
-/

module

public import LeanVM.Guest.B1.Sig.WotsW
public import LeanVM.Guest.B1.Sig.Model.Hashing

/-!
# WOTS+C chains under a hash model

`chainFromWith H` and `tipPairWith H` are `chainFrom` and `tipPair` with every step's hash the one
`H` answers (`none` if any step is unanswered); at the deployed hash they are `some` of the
deployed ones (`chainFromWith_deployed`, `tipPairWith_deployed`). `TipSetWith H` is `TipSet` over
them. The soundness lemmas are those of the deployed files, read forward over `M.sem`, for the
hinted starts the valuation names (`walkX`, `armX`, `groupX`, `codeX` of `WotsW`):

| deployed | here |
|---|---|
| `cStep_sound`, `cSteps_sound` | `cStep_model`, `cSteps_model` |
| `cWalk_sound_w`, `cWalks_sound_w` | `cWalk_model`, `cWalks_model` |
| `cArm_sound`, `cArm_sound_w` | `cArm_model` |
| `cGroup_sound`, `cGroup_sound_w` | `cGroup_model` |
| `cGroups_sound_w`, `cCodeword_sound_w` | `cGroups_model`, `cCodeword_model` |
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Chains with an answered hash -/

/-- `m + 1` steps of chain `i` from position `s`, every step's hash answered by `H`. -/
def chainFromWith (H : List UInt8 → Option Digest) (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    Nat → Nat → E → Option (E × E)
  | 0, s, v => hcellWith H (stepCells lx pp adr idx i s v)
  | m + 1, s, v => (hcellWith H (stepCells lx pp adr idx i s v)).bind fun h =>
      chainFromWith H lx pp adr idx i m (s + 1) h.1

/-- The end of chain `i` revealed at digit `d < 4` with the value `x`, its hashes answered by
`H`. -/
def tipPairWith (H : List UInt8 → Option Digest) (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat)
    (x : E) : Option (E × E) :=
  if d = 3 then some (x, 0) else chainFromWith H lx pp adr idx i (2 - d) d x

theorem chainFromWith_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFromWith HashModel.deployed.H lx pp adr idx i m s v = some (chainFrom lx pp adr idx i m s v)
  | 0, _, _ => rfl
  | m + 1, s, v => by
      simp only [chainFromWith, hcellWith_deployed, Option.bind_some, chainFrom]
      exact chainFromWith_deployed lx pp adr idx i m (s + 1) _

theorem tipPairWith_deployed (lx : Bool) (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipPairWith HashModel.deployed.H lx pp adr idx i d x = some (tipPair lx pp adr idx i d x) := by
  unfold tipPairWith tipPair
  split
  · rfl
  · exact chainFromWith_deployed lx pp adr idx i _ _ _

/-- The tips `t` hold chain `i`'s end at digit `d` from the value `x`, its hashes answered by
`H`. -/
def TipSetWith (H : List UInt8 → Option Digest) (w : Wots) (σ : Val) (i d : Nat) (x : E) (t : V × V) : Prop :=
  ∃ p, tipPairWith H w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i d x = some p ∧ σ t.1 = p.1 ∧
    (d ≠ 3 → σ t.2 = p.2)

theorem tipSetWith_deployed {w : Wots} {σ : Val} {i d : Nat} {x : E} {t : V × V} :
    TipSetWith HashModel.deployed.H w σ i d x t ↔ TipSet w σ i d x t := by
  rw [TipSetWith, tipPairWith_deployed, TipSet]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    cases hp
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, rfl, h1, h2⟩

variable {M : HashModel} {C : CallRel} {rd : Reader}

/-! ## A step, the steps, a walk -/

/-- **A chain step under a model** (`cStep_sound`): its outputs are the answered hash of its
cells. -/
theorem cStep_model {w : Wots} {σ : Val} {i s b : Nat} {v o0 o1 : V}
    (hmd : σ w.md = mdw (stepCount w.lx) true) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (cStep w i s b v o0 o1) next kret) :
    hcellWith M.H (stepCells w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i s (σ v)) = some (σ o0, σ o1) ∧ next := by
  unfold cStep at h
  cases hlx : w.lx
  · rw [hlx] at hmd
    simp only [hlx, Bool.false_eq_true, ↓reduceIte, cst, addS, b2s, holdsListB_cons_atom, holdsListB_nil,
      Atom.HoldsB, stepCount, word_zero] at hmd h
    obtain ⟨h0, h1, h2, h3, h4, h5, hn⟩ := h
    rw [h3, h4, hmd, h2, h1, h0, word_eq_eOfNat] at h5
    exact ⟨(compress3_model h5).2, hn⟩
  · rw [hlx] at hmd
    simp only [hlx, ↓reduceIte, cst, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB,
      stepCount] at hmd h
    obtain ⟨h0, h1, h2, h3, hn⟩ := h
    rw [h1, h2, hmd, h0, word_eq_eOfNat] at h3
    exact ⟨(compress4_model h3).2, hn⟩

theorem chainFromWith_succ (H : List UInt8 → Option Digest) (lx : Bool) (pp : E) (adr : Nat → E) (idx : E)
    (i m s : Nat) (v : E) {h : E × E} (hh : hcellWith H (stepCells lx pp adr idx i s v) = some h) :
    chainFromWith H lx pp adr idx i (m + 1) s v = chainFromWith H lx pp adr idx i m (s + 1) h.1 := by
  rw [chainFromWith, hh, Option.bind_some]

/-- **The steps of a chain under a model** (`cSteps_sound`). -/
theorem cSteps_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true) {i : Nat}
    {t0 t1 : V} : ∀ (m s b : Nat) (v : V) {next : Prop} {kret : List E → Prop},
    Stmt.HoldsListB M.sem C rd σ (cSteps w i t0 t1 m s b v) next kret →
      chainFromWith M.H w.lx (w.pp' σ) (w.adr' σ) (w.idx' σ) i m s (σ v) = some (σ t0, σ t1) ∧ next
  | 0, s, b, v, _, _, h => cStep_model hmd h
  | m + 1, s, b, v, next, kret, h => by
      rw [cSteps, holdsListB_append] at h
      obtain ⟨h1, h2⟩ := cStep_model hmd h
      obtain ⟨h3, hn⟩ := cSteps_model hmd m (s + 1) _ _ h2
      exact ⟨by rw [chainFromWith_succ _ _ _ _ _ _ _ _ _ h1]; exact h3, hn⟩

theorem holdsB_hint_cons (h : Hint) (ss : List Stmt) (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsListB M.sem C rd σ (.atom (.hint h) :: ss) next kret ↔ Stmt.HoldsListB M.sem C rd σ ss next kret := by
  simp [Atom.HoldsB]

/-- **A walk under a model, for its hinted start** (`cWalk_sound_w`). -/
theorem cWalk_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true) {i d b : Nat}
    {t0 t1 : V} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (cWalk w i d b t0 t1) next kret) :
    TipSetWith M.H w σ i d (walkX σ d b t0) (t0, t1) ∧ next := by
  unfold cWalk at h
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, hintW, holdsB_hint_cons] at h
    exact ⟨⟨(σ t0, 0), by simp [tipPairWith, walkX, hd], rfl, fun h' => absurd hd h'⟩, h⟩
  · simp only [hd, ↓reduceIte, hintW, holdsB_hint_cons] at h
    obtain ⟨ho, hn⟩ := cSteps_model hmd _ _ _ _ h
    refine ⟨⟨(σ t0, σ t1), ?_, rfl, fun _ => rfl⟩, hn⟩
    simp only [tipPairWith, walkX, hd, ↓reduceIte]
    exact ho

/-- **The walks of an arm under a model** (`cWalks_sound_w`). -/
theorem cWalks_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {first k : Nat} {fresh : Bool} :
    ∀ (m r b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsListB M.sem C rd σ (cWalks w tips first k fresh m r b).1 next kret →
        (∀ r', r ≤ r' → r' < r + m →
          TipSetWith M.H w σ (first + r') (armDigit k r') (walksX w.lx fresh tips k σ m r b r') (tips r')) ∧ next
  | 0, _, _, _, _, h => ⟨fun r' h1 h2 => absurd h2 (by omega), h⟩
  | m + 1, r, b, next, kret, h => by
      rw [cWalks_eq, holdsListB_append] at h
      obtain ⟨hx, h⟩ := cWalk_model hmd h
      obtain ⟨hr, hn⟩ := cWalks_model hmd m (r + 1) _ h
      refine ⟨fun r' h1 h2 => ?_, hn⟩
      by_cases e : r' = r
      · subst e
        rw [walksX, ite_eq_left rfl]
        exact hx
      · rw [walksX, ite_eq_right e]
        exact hr r' (by omega) (by omega)

/-! ## An arm, a group -/

/-- **An arm under a model** (`cArm_sound`, `cArm_sound_w`): every chain's end at its digit from
its hinted start, and the values it folds. -/
theorem cArm_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold fresh : Bool} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1
      next kret) :
    (∀ r < n, TipSetWith M.H w σ (first + r) (armDigit k r) (armX w.lx tips n k fold fresh b σ r) (tips r)) ∧
      ArmFold σ power prodIn encIn prodOut encOut first n k fold ∧ next := by
  have hw : ∀ {X : Prop} (b0 : Nat), b0 = armStart fold b →
      Stmt.HoldsListB M.sem C rd σ (cWalks w tips first k fresh n 0 b0).1 X kret →
      (∀ r < n, TipSetWith M.H w σ (first + r) (armDigit k r) (armX w.lx tips n k fold fresh b σ r) (tips r)) ∧ X :=
    fun b0 hb0 h => by
      subst hb0
      obtain ⟨h1, h2⟩ := cWalks_model hmd n 0 _ h
      exact ⟨fun r hr => h1 r (Nat.zero_le r) (by omega), h2⟩
  have hlit : k = 0 → lit (k * 4 ^ first) = 0 := fun hk => by rw [hk, Nat.zero_mul, lit_zero]
  unfold cArm at h
  by_cases hk : k = 0
  · have hl := hlit hk
    subst hk
    simp only [↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsListB_append, cst,
        holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, mulS] at h
    · obtain ⟨ha, h1, h2, hn⟩ := hw _ (by simp [armStart]) h
      exact ⟨ha, ⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h2, hl, add_zero]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨ha, h1, h2, hn⟩ := hw _ (by simp [armStart]) h
      exact ⟨ha, ⟨by simp [h1], by simp only [↓reduceIte]; rw [h2, h0, hl, word_zero, add_zero]⟩, hn⟩
  · simp only [hk, ↓reduceIte] at h
    cases fold <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, holdsListB_append, cst, addS,
        holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB, mulS] at h
    · obtain ⟨ha, h1, h2, h3, hn⟩ := hw _ (by simp [armStart]) h
      exact ⟨ha, ⟨h1, by simp only [Bool.false_eq_true, ↓reduceIte]; rw [h3, h2]⟩, hn⟩
    · obtain ⟨h0, h⟩ := h
      obtain ⟨ha, h1, h2, h3, hn⟩ := hw _ (by simp [armStart]) h
      exact ⟨ha, ⟨by simp [h1], by simp only [↓reduceIte]; rw [h3, h2, h0, word_zero]⟩, hn⟩

theorem holdsListB_match_single (x : V) (arms : List (List Stmt)) (next : Prop) (kret : List E → Prop)
    (σ : Val) :
    Stmt.HoldsListB M.sem C rd σ [.match_ x arms] next kret ↔
      ∃ (j : Nat) (h : j < arms.length), σ x = ofK (gpow j) ∧ Stmt.HoldsListB M.sem C rd σ arms[j] next kret := by
  simp only [Stmt.HoldsListB]
  exact holdsB_match_iff x arms next kret

/-- **A group under a model** (`cGroup_sound`, `cGroup_sound_w`): its hint is `g^k` for a digit
value `k < 4^n`, its chains end at `k`'s digits from the hinted starts, and its arm's folds. -/
theorem cGroup_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool} {b : Nat} {next : Prop}
    {kret : List E → Prop} (hN : 4 ^ n ≤ 2 ^ 64 - 1)
    (h : Stmt.HoldsListB M.sem C rd σ (cGroup w power prodIn encIn first n fold b).1 next kret) :
    (∃ k < 4 ^ n, σ (.n b) = ofK (gpow k) ∧ gLog (σ (.n b)) (4 ^ n) = k ∧
      (∀ r < n, TipSetWith M.H w σ (first + r) (armDigit k r)
        (groupX w power prodIn encIn first n fold b σ r) (groupTips w.lx fold b r)) ∧
      ArmFold σ power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b) first n k fold) ∧
      next := by
  simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsListB_cons_atom,
    Atom.HoldsB, true_and] at h
  obtain ⟨_, _, h⟩ := h
  obtain ⟨j, hj, hx, ha⟩ := (holdsListB_match_single _ _ _ _ _).mp h
  have hj' := hj
  rw [cArms_length] at hj'
  have hk : gLog (σ (.n b)) (4 ^ n) = j := gLog_eq hx hj' hN
  have hget := cArms_get_w w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) j hj'
  rw [List.getElem?_eq_getElem hj, Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  obtain ⟨h1, h2, hn⟩ := cArm_model hmd ha
  refine ⟨⟨j, hj', hx, hk, fun r hr => ?_, h2⟩, hn⟩
  rw [groupX, hk]
  exact h1 r hr

/-! ## Groups in sequence and the codeword -/

/-- **Groups in sequence under a model** (`cGroups_sound_w`). -/
theorem cGroups_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) {next : Prop} {kret : List E → Prop}, (p = 0 → 0 < m) →
      Stmt.HoldsListB M.sem C rd σ (cGroups w power m p prod enc b).1 next kret →
      (∃ ks : Nat → Nat, (∀ q < m, ks q < 64) ∧
        (∀ q < m, ∀ r < 3, TipSetWith M.H w σ (3 * (p + q) + r) (armDigit (ks q) r)
          (groupsX w power σ m p prod enc b (3 * q + r))
          ((cGroups w power m p prod enc b).2.2.1.getD (3 * q + r) (.n 0, .n 0))) ∧
        σ (cGroups w power m p prod enc b).2.2.2.1 =
          (if p = 0 then 1 else σ prod) * gen ^ (∑ q ∈ Finset.range m, digitSum (ks q) 3) ∧
        σ (cGroups w power m p prod enc b).2.2.2.2 =
          (if p = 0 then 0 else σ enc) + ∑ q ∈ Finset.range m, lit (ks q * 4 ^ (3 * (p + q)))) ∧ next
  | 0, p, prod, enc, b, next, kret, hm, h => by
      have hp : p ≠ 0 := fun h => absurd (hm h) (by omega)
      exact ⟨⟨fun _ => 0, fun q h => absurd h (by omega), fun q h => absurd h (by omega),
        by simp [cGroups, hp], by simp [cGroups, hp]⟩, h⟩
  | m + 1, p, prod, enc, b, next, kret, _, h => by
      simp only [cGroups] at h ⊢
      rw [holdsListB_append] at h
      obtain ⟨⟨k, hk, -, -, htip0, hfold⟩, h⟩ := cGroup_model hmd (by norm_num) h
      obtain ⟨⟨ks, hks, htips, hprod, henc⟩, hn⟩ := cGroups_model hmd hpow m (p + 1) _ _ _ (by omega) h
      refine ⟨⟨fun q => if q = 0 then k else ks (q - 1), fun q hq => ?_, fun q hq r hr => ?_, ?_, ?_⟩, hn⟩
      · by_cases hq0 : q = 0
        · subst hq0; simpa using hk
        · simp only [hq0, ↓reduceIte]; exact hks _ (by omega)
      · by_cases hq0 : q = 0
        · subst hq0
          have hx := htip0 r hr
          rw [List.getD_append _ _ _ _ (by simpa using hr), groupsX, ite_eq_left (by omega)]
          simpa [hr] using hx
        · have hx := htips (q - 1) (by omega) r hr
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [hq0, ↓reduceIte, List.length_map, List.length_range]
          rw [groupsX, ite_eq_right (by omega), show 3 * q + r - 3 = 3 * (q - 1) + r by omega,
            show 3 * (p + q) + r = 3 * (p + 1 + (q - 1)) + r by omega]
          exact hx
      · unfold ArmFold groupProd at hfold
        rw [hprod, Finset.sum_range_succ']
        simp only [groupProd, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rw [hfold.1, hpow _ (pow_digitSum_lt k), pow_add]
        by_cases hp : p = 0 <;> simp [hp] <;> ring
      · unfold ArmFold groupEnc at hfold
        rw [henc, Finset.sum_range_succ']
        simp only [groupEnc, ↓reduceIte, Nat.add_sub_cancel, Nat.add_one_ne_zero, Nat.add_zero]
        rw [hfold.2]
        by_cases hp : p = 0 <;> simp [hp] <;> ring_nf

/-- **The codeword under a model** (`cCodeword_sound_w`): digits below 4, every chain's end at its
digit from its hinted start, the digits summing to the target's exponent and encoding the
digest's cell `d0`. -/
theorem cCodeword_model {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) {G : Nat} (hG : 0 < G) {target : E}
    {d0 : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (cCodeword w power G target d0 b).1 next kret) :
    (∃ dig : Nat → Nat, (∀ i, dig i < 4) ∧
      (∀ i < 3 * G + 1, TipSetWith M.H w σ i (dig i) (codeX w power G b σ i)
        ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0))) ∧
      target = gen ^ (∑ i ∈ Finset.range (3 * G + 1), dig i) ∧
      σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i)) ∧ next := by
  simp only [cCodeword] at h ⊢
  rw [holdsListB_append, holdsListB_append] at h
  obtain ⟨⟨ks, hks, htips, hprod, henc⟩, h⟩ := cGroups_model hmd hpow G 0 _ _ _ (fun _ => hG) h
  obtain ⟨⟨kl, hkl, -, hkg, hlast, hfold⟩, h⟩ := cGroup_model hmd (by norm_num) h
  simp only [cst, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
  obtain ⟨hc, hp, he, hn⟩ := h
  rw [e_add_eq_zero_iff] at hp he
  simp only [pow_one] at hkl
  have hlen := cGroups_tips_length w power G 0 (.n 0) (.n 0) b
  refine ⟨⟨codeDigit G ks kl, codeDigit_lt hkl, fun i hi => ?_, ?_, ?_⟩, hn⟩
  · by_cases hi' : i < 3 * G
    · have hx := htips (i / 3) (by omega) (i % 3) (Nat.mod_lt _ (by norm_num))
      rw [List.getD_append _ _ _ _ (by omega), codeX, ite_eq_left hi']
      rw [show i = 3 * (i / 3) + i % 3 by omega, codeDigit_group (by omega) (Nat.mod_lt _ (by norm_num))]
      simpa using hx
    · have hi3 : i = 3 * G := by omega
      subst hi3
      have hx := hlast 0 (by norm_num)
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, codeX, ite_eq_right (lt_irrefl _)]
      simp only [codeDigit, lt_irrefl, ↓reduceIte, List.getD_cons_zero]
      simpa [armDigit, Nat.mod_eq_of_lt hkl] using hx
  · unfold ArmFold at hfold
    rw [codeDigit_sum, ← hc, ← hp, hfold.1, hprod, hpow _ (by rw [digitSum_one hkl]; omega), digitSum_one hkl,
      pow_add]
    simp
  · unfold ArmFold at hfold
    rw [← he, hfold.2, henc]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [codeDigit_enc G ks kl hks, (lit_sum_groups ks G hks).1]
    have h2 := (lit_sum_groups ks G hks).2
    have e : kl * 4 ^ (3 * G) = 2 ^ (6 * G) * kl := by
      have h4 : (4 : Nat) ^ (3 * G) = 2 ^ (6 * G) := by
        rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
      rw [Nat.mul_comm, h4]
    rw [e, add_comm (∑ q ∈ Finset.range G, ks q * 4 ^ (3 * q)), lit_add_of_lt h2, add_comm]

end
end LeanVM.Guest.B1.Sig
