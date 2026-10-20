/-
  LeanVM.Guest.B1.Sig.WotsW

  The values a WOTS+C codeword and a Merkle path hint, as functions of the valuation: the chain
  starts of the arm each digit group's hint selects, and the siblings of each level. The
  codeword and the path are sound for these values.
-/

module

public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Merkle

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## A digit hint's value -/

/-- The index of `e` among `g^0, …, g^(N-1)`, `0` if none: the value a `match` on `e` takes. -/
def gLog (e : E) (N : Nat) : Nat :=
  ((List.range N).find? fun j => decide (e = ofK (Parameters.gpow j))).getD 0

theorem gLog_eq {e : E} {N j : Nat} (h : e = ofK (Parameters.gpow j)) (hj : j < N) (hN : N ≤ 2 ^ 64 - 1) :
    gLog e N = j := by
  unfold gLog
  have hex : ((List.range N).find? fun j => decide (e = ofK (Parameters.gpow j))).isSome := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_range.mpr hj, by simp [h]⟩
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hex
  have hm := List.mem_range.mp (List.mem_of_find?_eq_some hj')
  have hp := List.find?_some hj'
  simp only [decide_eq_true_eq] at hp
  rw [hj', Option.getD_some]
  apply gen_pow_inj (by omega) (by omega)
  rw [gen_pow_eq_ofK, gen_pow_eq_ofK, ← hp, h]

/-! ## Walks -/

/-- The value a walk of digit `d` from base `b` starts from: its `chain_starts` hint, at digit 3
the tip `t0` itself. -/
def walkX (σ : Val) (d b : Nat) (t0 : V) : E := if d = 3 then σ t0 else σ (.n b)

/-- **A walk is sound for its hinted start.** -/
theorem cWalk_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true) {i d b : Nat}
    {t0 t1 : V} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cWalk w i d b t0 t1) next kret) :
    TipSet w σ i d (walkX σ d b t0) (t0, t1) ∧ next := by
  unfold cWalk at h
  by_cases hd : d = 3
  · simp only [hd, ↓reduceIte, hintW, holds_hint_cons] at h
    exact ⟨⟨by simp [walkX, tipPair, hd], fun h' => absurd hd h'⟩, h⟩
  · simp only [hd, ↓reduceIte, hintW, holds_hint_cons] at h
    obtain ⟨ho, hn⟩ := cSteps_sound hmd _ _ _ _ h
    refine ⟨⟨?_, fun _ => ?_⟩, hn⟩ <;> simp only [walkX, tipPair, hd, ↓reduceIte, ← ho]

/-- The values the walks of chains `r ..< r + m` from base `b` start from, by chain. -/
def walksX (lx fresh : Bool) (tips : Nat → V × V) (k : Nat) (σ : Val) : Nat → Nat → Nat → Nat → E
  | 0, _, _, _ => 0
  | m + 1, r, b, r' => if r' = r then walkX σ (armDigit k r) b (tips r).1
      else walksX lx fresh tips k σ m (r + 1) (walkNext lx fresh k r b) r'

theorem cWalks_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {first k : Nat} {fresh : Bool} :
    ∀ (m r b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsList C rd σ (cWalks w tips first k fresh m r b).1 next kret →
        (∀ r', r ≤ r' → r' < r + m →
          TipSet w σ (first + r') (armDigit k r') (walksX w.lx fresh tips k σ m r b r') (tips r')) ∧ next
  | 0, _, _, _, _, h => ⟨fun r' h1 h2 => absurd h2 (by omega), h⟩
  | m + 1, r, b, next, kret, h => by
      rw [cWalks_eq, holdsList_append] at h
      obtain ⟨hx, h⟩ := cWalk_sound_w hmd h
      obtain ⟨hr, hn⟩ := cWalks_sound_w hmd m (r + 1) _ h
      refine ⟨fun r' h1 h2 => ?_, hn⟩
      by_cases e : r' = r
      · subst e
        rw [walksX, ite_eq_left rfl]
        exact hx
      · rw [walksX, ite_eq_right e]
        exact hr r' (by omega) (by omega)

/-! ## Arms and groups -/

/-- The values an arm's walks start from. -/
def armX (lx : Bool) (tips : Nat → V × V) (n k : Nat) (fold fresh : Bool) (b : Nat) (σ : Val) : Nat → E :=
  walksX lx fresh tips k σ n 0 (armStart fold b)

/-- **An arm is sound for its walks' hinted starts.** -/
theorem cArm_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {tips : Nat → V × V} {power : Nat → V} {prodIn encIn prodOut encOut : V} {first n k : Nat}
    {fold fresh : Bool} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cArm w tips power prodIn encIn prodOut encOut first n k fold fresh b).1
      next kret) :
    ∀ r < n, TipSet w σ (first + r) (armDigit k r) (armX w.lx tips n k fold fresh b σ r) (tips r) := by
  have hw : ∀ {X : Prop}, Stmt.HoldsList C rd σ (cWalks w tips first k fresh n 0 (armStart fold b)).1 X kret →
      ∀ r < n, TipSet w σ (first + r) (armDigit k r) (armX w.lx tips n k fold fresh b σ r) (tips r) :=
    fun h r hr => (cWalks_sound_w hmd n 0 _ h).1 r (Nat.zero_le r) (by omega)
  rw [cArm_fst, holdsList_append, holdsList_append] at h
  cases fold
  · simp only [Bool.false_eq_true, ↓reduceIte, holdsList_nil] at h
    exact hw h
  · simp only [↓reduceIte, cst, holdsList_cons_atom, holdsList_nil] at h
    exact hw h.2

/-- The base of arm `k + j` among the arms `k ..< k + m` from base `b`. -/
def armsBase (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n : Nat) (fold : Bool) : Nat → Nat → Nat → Nat → Nat
  | 0, _, b, _ => b
  | _ + 1, _, b, 0 => b
  | m + 1, k, b, j + 1 => armsBase w tips power prodIn encIn prodOut encOut first n fold m (k + 1)
      (cArm w tips power prodIn encIn prodOut encOut first n k fold (k == 0) b).2 j

theorem cArms_get_w (w : Wots) (tips : Nat → V × V) (power : Nat → V) (prodIn encIn prodOut encOut : V)
    (first n : Nat) (fold : Bool) : ∀ (m k b j : Nat), j < m →
    (cArms w tips power prodIn encIn prodOut encOut first n fold m k b).1[j]? =
      some (cArm w tips power prodIn encIn prodOut encOut first n (k + j) fold ((k + j) == 0)
        (armsBase w tips power prodIn encIn prodOut encOut first n fold m k b j)).1
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, k, b, 0, _ => by simp [cArms, armsBase]
  | m + 1, k, b, j + 1, h => by
      simp only [cArms, armsBase, List.getElem?_cons_succ]
      rw [cArms_get_w w tips power prodIn encIn prodOut encOut first n fold m (k + 1) _ j (by omega),
        show k + 1 + j = k + (j + 1) by omega]

/-- The values a group's chains start from: those of the arm its digit hint selects. -/
def groupX (w : Wots) (power : Nat → V) (prodIn encIn : V) (first n : Nat) (fold : Bool) (b : Nat)
    (σ : Val) : Nat → E :=
  armX w.lx (groupTips w.lx fold b) n (gLog (σ (.n b)) (4 ^ n)) fold (gLog (σ (.n b)) (4 ^ n) == 0)
    (armsBase w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b) (groupEnc w.lx fold n b)
      first n fold (4 ^ n) 0 (b + 5) (gLog (σ (.n b)) (4 ^ n))) σ

/-- **A group is sound for its arm's hinted starts**, at the digits of its hint's value. -/
theorem cGroup_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} {prodIn encIn : V} {first n : Nat} {fold : Bool} {b : Nat} {next : Prop}
    {kret : List E → Prop} (hN : 4 ^ n ≤ 2 ^ 64 - 1)
    (h : Stmt.HoldsList C rd σ (cGroup w power prodIn encIn first n fold b).1 next kret) :
    ∀ r < n, TipSet w σ (first + r) (armDigit (gLog (σ (.n b)) (4 ^ n)) r)
      (groupX w power prodIn encIn first n fold b σ r) (groupTips w.lx fold b r) := by
  simp only [cGroup, hintW, rangeS, cst, List.cons_append, List.nil_append, holdsList_cons_atom,
    Atom.Holds, true_and] at h
  obtain ⟨_, _, h⟩ := h
  obtain ⟨j, hj, hx, ha⟩ := (holdsList_match_single _ _ _ _ _).mp h
  have hj' := hj
  rw [cArms_length] at hj'
  have hk : gLog (σ (.n b)) (4 ^ n) = j := gLog_eq hx hj' hN
  have hget := cArms_get_w w (groupTips w.lx fold b) power prodIn encIn (groupProd w.lx fold n b)
    (groupEnc w.lx fold n b) first n fold (4 ^ n) 0 (b + 5) j hj'
  rw [List.getElem?_eq_getElem hj, Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  intro r hr
  rw [groupX, hk]
  exact cArm_sound_w hmd ha r hr

/-! ## Groups in sequence and the codeword -/

/-- The values the chains of groups `p ..< p + m` from base `b` start from, chain `3q + r` of
group `q`. -/
def groupsX (w : Wots) (power : Nat → V) (σ : Val) : Nat → Nat → V → V → Nat → Nat → E
  | 0, _, _, _, _, _ => 0
  | m + 1, p, prod, enc, b, i =>
      if i < 3 then groupX w power prod enc (3 * p) 3 (p == 0) b σ i
      else groupsX w power σ m (p + 1) (groupProd w.lx (p == 0) 3 b) (groupEnc w.lx (p == 0) 3 b)
        (cGroup w power prod enc (3 * p) 3 (p == 0) b).2 (i - 3)

/-- **Groups in sequence are sound** for their hinted starts (`cGroups_sound`, the values named). -/
theorem cGroups_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) :
    ∀ (m p : Nat) (prod enc : V) (b : Nat) {next : Prop} {kret : List E → Prop}, (p = 0 → 0 < m) →
      Stmt.HoldsList C rd σ (cGroups w power m p prod enc b).1 next kret →
      (∃ ks : Nat → Nat, (∀ q < m, ks q < 64) ∧
        (∀ q < m, ∀ r < 3, TipSet w σ (3 * (p + q) + r) (armDigit (ks q) r)
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
      rw [holdsList_append] at h
      have htip0 := cGroup_sound_w hmd (by norm_num) h
      obtain ⟨⟨k, hk, hkx, -, hfold⟩, h⟩ := cGroup_sound hmd h
      rw [gLog_eq hkx hk (by norm_num)] at htip0
      obtain ⟨⟨ks, hks, htips, hprod, henc⟩, hn⟩ := cGroups_sound_w hmd hpow m (p + 1) _ _ _ (by omega) h
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

/-- The values the chains of a codeword of `3G + 1` chains from base `b` start from. -/
def codeX (w : Wots) (power : Nat → V) (G : Nat) (b : Nat) (σ : Val) (i : Nat) : E :=
  if i < 3 * G then groupsX w power σ G 0 (.n 0) (.n 0) b i
  else groupX w power (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.1 (cGroups w power G 0 (.n 0) (.n 0) b).2.2.2.2
    (3 * G) 1 false (cGroups w power G 0 (.n 0) (.n 0) b).2.1 σ 0

/-- **The codeword is sound** for its hinted starts (`cCodeword_sound`, the values named). -/
theorem cCodeword_sound_w {w : Wots} {σ : Val} (hmd : σ w.md = mdw (stepCount w.lx) true)
    {power : Nat → V} (hpow : ∀ s < 10, σ (power s) = gen ^ s) {G : Nat} (hG : 0 < G) {target : E}
    {d0 : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (cCodeword w power G target d0 b).1 next kret) :
    (∃ dig : Nat → Nat, (∀ i, dig i < 4) ∧
      (∀ i < 3 * G + 1, TipSet w σ i (dig i) (codeX w power G b σ i)
        ((cCodeword w power G target d0 b).2.2.getD i (.n 0, .n 0))) ∧
      target = gen ^ (∑ i ∈ Finset.range (3 * G + 1), dig i) ∧
      σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), dig i * 4 ^ i)) ∧ next := by
  simp only [cCodeword] at h ⊢
  rw [holdsList_append, holdsList_append] at h
  obtain ⟨⟨ks, hks, htips, hprod, henc⟩, h⟩ := cGroups_sound_w hmd hpow G 0 _ _ _ (fun _ => hG) h
  have hlast := cGroup_sound_w hmd (by norm_num) h
  obtain ⟨⟨kl, hkl, hklx, -, hfold⟩, h⟩ := cGroup_sound hmd h
  rw [gLog_eq hklx hkl (by norm_num)] at hlast
  simp only [cst, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
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

/-! ## Merkle paths -/

/-- The siblings a Merkle path of levels `l ..< l + m` from base `b` hints, by level: of each
level's two hinted children, the one its bit does not name. -/
def mSibs (isEnd β : Nat → Bool) (σ : Val) : Nat → Nat → Nat → Nat → E
  | 0, _, _, _ => 0
  | m + 1, l, b, l' => if l' = l then (if β l then σ (.n b) else σ (.n (b + 1)))
      else mSibs isEnd β σ m (l + 1) ((if isEnd l then b + 4 else b + 5) + 6) l'

/-- **A Merkle path is sound** for its hinted siblings (`merkle_sound`, the siblings named). -/
theorem merkle_sound_w {σ : Val} {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} : ∀ (m l : Nat) (cur : V) (b : Nat) {next : Prop} {kret : List E → Prop},
      (∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l')) →
      Stmt.HoldsList C rd σ (merkle pp bit node addr isEnd m l cur b).1 next kret →
      σ (merkle pp bit node addr isEnd m l cur b).2.1 =
        mFold (σ pp) (mAddr σ node addr isEnd) β (mSibs isEnd β σ m l b) m l (σ cur) ∧ next
  | 0, _, _, _, _, _, _, h => ⟨rfl, h⟩
  | m + 1, l, cur, b, next, kret, hβ, h => by
      rw [merkle_eq] at h ⊢
      dsimp only at h ⊢
      rw [holdsList_append] at h
      obtain ⟨-, hord, -, hh, h⟩ := (merkleLevel_iff (hβ l le_rfl (by omega))).mp h
      obtain ⟨hs, hn⟩ := merkle_sound_w m (l + 1) _ _ (fun l' h1 h2 => hβ l' (by omega) (by omega)) h
      refine ⟨?_, hn⟩
      have hc := mFold_congr (σ pp) (mAddr σ node addr isEnd) β
        (sibs := mSibs isEnd β σ (m + 1) l b)
        (sibs' := mSibs isEnd β σ m (l + 1) ((if isEnd l then b + 4 else b + 5) + 6)) m (l + 1)
        (fun l' h1 _ => by rw [mSibs, ite_eq_right (by omega)])
      rw [hs, mFold, hc]
      congr 1
      have h1 := congrArg Prod.fst hh
      simp only at h1
      rw [h1, mSibs, ite_eq_left rfl]
      cases hb : β l <;> simp [hb] at hord ⊢ <;> rw [hord]

end
end LeanVM.Guest.B1.Sig
