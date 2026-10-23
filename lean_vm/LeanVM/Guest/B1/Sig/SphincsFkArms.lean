/-
  LeanVM.Guest.B1.Sig.SphincsFkArms

  The forest keys' dispatch of `verify_sig_lean_sphincs` completes: arm `t`, its chains' values
  loaded, on canonical cells.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFkComplete

/-!
# The forest keys' dispatch, complete

* `fkArm_split`: an arm is its sequential prefix and its two writes;
* `fkArm0_complete`, `fkArmN_complete`: the first arm (allocating the leaf's and the weight's cells)
  and a later one, their chains' values `vals` loaded: kept, the leaf canonical, the weight written;
* `fkAB_*`: the arms' bases; `fkArms_complete`: the dispatch on `t`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The sequential prefix of key `t`'s arm from base `b`. -/
def fkPre (t : Nat) (keyAt : V) (b : Nat) : List Stmt :=
  (fkChains t keyAt 6 0 b).1 ++ [addS (.n (fkChains t keyAt 6 0 b).2.1) keyAt (sTws 24),
    cst ((fkChains t keyAt 6 0 b).2.1 + 1) (word (2 ^ 63 + 1) 0 0),
    kecS [sPP, .n (fkChains t keyAt 6 0 b).2.1, (fkChains t keyAt 6 0 b).2.2.getD 0 (.n 0),
      (fkChains t keyAt 6 0 b).2.2.getD 1 (.n 0), (fkChains t keyAt 6 0 b).2.2.getD 2 (.n 0),
      (fkChains t keyAt 6 0 b).2.2.getD 3 (.n 0), (fkChains t keyAt 6 0 b).2.2.getD 4 (.n 0),
      (fkChains t keyAt 6 0 b).2.2.getD 5 (.n 0), .n ((fkChains t keyAt 6 0 b).2.1 + 1),
      .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
      (runV ((fkChains t keyAt 6 0 b).2.1 + 2) 13) false false]

theorem fkArm_split (t w : Nat) (keyAt retN retW : V) (fresh : Bool) (b : Nat) :
    (fkArm t w keyAt retN retW fresh b).1 = fkPre t keyAt b ++
      [copyS (if fresh then .n ((fkChains t keyAt 6 0 b).2.1 + 15) else retN)
        (.n ((fkChains t keyAt 6 0 b).2.1 + 2)),
        .atom (.const (if fresh then .n ((fkChains t keyAt 6 0 b).2.1 + 16) else retW) (fkWeight t w))] := by
  simp [fkArm, fkPre]

theorem fkArm_snd (t w : Nat) (keyAt retN retW : V) (fresh : Bool) (b : Nat) :
    (fkArm t w keyAt retN retW fresh b).2 =
      if fresh then (fkChains t keyAt 6 0 b).2.1 + 17 else (fkChains t keyAt 6 0 b).2.1 + 15 := rfl

theorem fkPre_hints {t : Nat} {keyAt : V} {b : Nat} : ∀ s vs,
    Stmt.atom (.hint (.witness s (.stack vs))) ∈ fkPre t keyAt b → ∃ k < 6, vs = [.n (fkCB t keyAt 0 b k)] := by
  intro s vs h
  simp only [fkPre, List.mem_append] at h
  rcases h with h | h
  · exact fkChains_hints 6 0 b s vs h
  · simp [addS, cst, kecS] at h

theorem fkWeight_canon (t w : Nat) : IsCanonical128 (fkWeight t w) := by
  unfold fkWeight; split <;> exact canon_word _ _

theorem fkChain_hint_mem (t i : Nat) (keyAt : V) (b : Nat) :
    hintW "sp_forest_values" [.n b] ∈ (fkChain t i keyAt b).1 := by
  unfold fkChain
  simp only
  split
  · simp
  · split <;> simp

theorem fkChains_hint_mem {t : Nat} {keyAt : V} : ∀ (m i b k : Nat), k < m →
    hintW "sp_forest_values" [.n (fkCB t keyAt i b k)] ∈ (fkChains t keyAt m i b).1
  | 0, _, _, _, hk => absurd hk (by omega)
  | m + 1, i, b, 0, _ => List.mem_append_left _ (fkChain_hint_mem t i keyAt b)
  | m + 1, i, b, k + 1, hk =>
      List.mem_append_right _ (fkChains_hint_mem m (i + 1) (fkChain t i keyAt b).2.1 k (by omega))

/-- The chains' values loaded. -/
def fkLoad (t : Nat) (keyAt : V) (b : Nat) (vals : Nat → E) (σ : Val) : Val :=
  sLoad (fun i => .n (fkCB t keyAt 0 b i)) vals σ 6

variable {lo : Nat}

theorem sx_nb {keyAt : V} (hlo : 206 ≤ lo) (hk : NBv lo keyAt) {v : V} (hv : SX keyAt keyAt v) : NBv lo v := by
  rcases hv with rfl | rfl | rfl | ⟨k, hk', rfl⟩ | ⟨k, hk', rfl⟩
  · exact hk
  · exact hk
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨165 + k, by omega, rfl⟩
  · exact ⟨sPad + k, by simp only [sPad]; omega, rfl⟩

theorem fkLoad_spec {t : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ b) (hk : NBv lo keyAt)
    (vals : Nat → E) (σ : Val) :
    Ext b (fkChains t keyAt 6 0 b).2.1 σ (fkLoad t keyAt b vals σ) ∧
      ∀ i < 6, fkLoad t keyAt b vals σ (.n (fkCB t keyAt 0 b i)) = vals i := by
  have hlt := fkCB_lt (t := t) (keyAt := keyAt) hlo hb hk
  refine ⟨fun v hv => sLoad_other _ _ σ 6 fun i hi e => ?_, fun i hi => sLoad_at _ vals σ 6
    (fun a c h1 h2 e => by simp only [V.mk.injEq, true_and] at e; have := hlt a c h1 (by omega); omega) i hi⟩
  have h1 : b ≤ fkCB t keyAt 0 b i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · exact le_of_lt (lt_of_le_of_lt (le_refl _) (hlt 0 i hpos (by omega)))
  have h2 := hlt i 6 hi le_rfl
  exact hv _ h1 h2 e

/-- **The first arm completes**, allocating the leaf's and the weight's cells. -/
theorem fkArm0_complete {t w : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ b) (hk : NBv b keyAt)
    (vals : Nat → E) (hv : ∀ i < 6, IsCanonical128 (vals i)) (σ : Val)
    (hX : ∀ v, SX keyAt keyAt v → NBv b v → IsCanonical128 (σ v)) :
    Completes C rd b ((fkChains t keyAt 6 0 b).2.1 + 17) (fkArm t w keyAt (.n 0) (.n 0) true b).1 σ
      (fun σ' => (∀ i < 6, σ' (.n (fkCB t keyAt 0 b i)) = vals i) ∧
        IsCanonical128 (σ' (.n ((fkChains t keyAt 6 0 b).2.1 + 15))) ∧
        σ' (.n ((fkChains t keyAt 6 0 b).2.1 + 16)) = fkWeight t w) := by
  have hpre := fkArmPre_kseq (t := t) (lo := b) hlo le_rfl hk
  have hB : b ≤ (fkChains t keyAt 6 0 b).2.1 :=
    KSeq.le (fkChains_kseq (t := t) (lo := b) hlo hk 6 0 b (by omega) le_rfl).1
  have hks : KSeq b (SX keyAt keyAt) b (fkArm t w keyAt (.n 0) (.n 0) true b).1
      ((fkChains t keyAt 6 0 b).2.1 + 17) := by
    rw [fkArm_split]
    simp only [↓reduceIte]
    exact KSeq.append hpre ⟨_, ⟨rfl, krd_in (by omega) (by omega), rfl⟩, _,
      ⟨rfl, fkWeight_canon t w, rfl⟩, rfl⟩
  obtain ⟨hext, hval⟩ := fkLoad_spec (t := t) (keyAt := keyAt) (lo := b) hlo le_rfl hk vals σ
  have hcl := KSeq.le hpre
  refine Completes.reload (hext.mono le_rfl (by omega)) ?_
  refine (kseq_completes (C := C) (rd := rd) hks _ (fun v hx hn => ?_) (fun s vs hm v hvs => ?_)).mono
    le_rfl le_rfl (fun σ' ⟨ha, hc, hk'⟩ => ⟨fun i hi => ?_, hc _ (by omega) (by omega), ?_⟩)
  · obtain ⟨j, hj, rfl⟩ := hn
    rw [hext.apply (Or.inl hj)]
    exact hX _ hx ⟨j, hj, rfl⟩
  · rw [fkArm_split] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨k, hk6, rfl⟩ := fkPre_hints s vs hm
      simp only [List.mem_singleton] at hvs
      subst hvs
      rw [hval k hk6]
      exact hv k hk6
    · simp [copyS] at hm
  · have hmem : Stmt.atom (.hint (.witness "sp_forest_values" (.stack [.n (fkCB t keyAt 0 b i)]))) ∈
        (fkArm t w keyAt (.n 0) (.n 0) true b).1 := by
      rw [fkArm_split]
      exact List.mem_append_left _ (List.mem_append_left _ (fkChains_hint_mem 6 0 b i hi))
    rw [hk' _ _ hmem _ (List.mem_singleton_self _), hval i hi]
  · have := ha.atom (a := .const (.n ((fkChains t keyAt 6 0 b).2.1 + 16)) (fkWeight t w)) (by
      rw [fkArm_split]; simp)
    exact this

/-- **A later arm completes**, writing the first arm's leaf and weight cells `rn`, `rw`. -/
theorem fkArmN_complete {t w : Nat} {keyAt : V} {b hi rn rw : Nat} (hlo : 206 ≤ lo) (hb : lo ≤ b)
    (hk : NBv lo keyAt) (hrn : lo ≤ rn ∧ rn < b) (hrw : lo ≤ rw ∧ rw < b) (hne : rn ≠ rw)
    (hhi : (fkChains t keyAt 6 0 b).2.1 + 15 ≤ hi) (vals : Nat → E) (hv : ∀ i < 6, IsCanonical128 (vals i))
    (σ : Val) (hX : ∀ v, SX keyAt keyAt v → NBv lo v → IsCanonical128 (σ v)) :
    Completes C rd lo hi (fkArm t w keyAt (.n rn) (.n rw) false b).1 σ
      (fun σ' => (∀ i < 6, σ' (.n (fkCB t keyAt 0 b i)) = vals i) ∧ IsCanonical128 (σ' (.n rn)) ∧
        σ' (.n rw) = fkWeight t w) := by
  have hkb : NBv b keyAt := hk.mono' hb
  have hpre := fkArmPre_kseq (t := t) (lo := b) (by omega) le_rfl hkb
  have hB : b ≤ (fkChains t keyAt 6 0 b).2.1 :=
    KSeq.le (fkChains_kseq (t := t) (lo := b) (by omega) hkb 6 0 b (by omega) le_rfl).1
  obtain ⟨hext, hval⟩ := fkLoad_spec (t := t) (keyAt := keyAt) (lo := b) (by omega) le_rfl hkb vals σ
  set B := (fkChains t keyAt 6 0 b).2.1 with hBdef
  obtain ⟨σ1, he1, ha1, hc1, hk1⟩ := kseq_complete (rd := rd) (lo := b) le_rfl hpre
    (fkLoad t keyAt b vals σ) (fun v hx hn => by
      obtain ⟨j, hj, rfl⟩ := sx_nb (lo := lo) hlo hk hx
      rw [hext.apply (Or.inl (by omega))]
      exact hX _ hx ⟨j, hj, rfl⟩)
    (fun j h1 h2 => by omega)
    (fun s vs hm v hvs => by
      obtain ⟨k, hk6, rfl⟩ := fkPre_hints s vs hm
      simp only [List.mem_singleton] at hvs
      subst hvs
      rw [hval k hk6]
      exact hv k hk6)
  set σ2 := Function.update (Function.update σ1 (.n rn) (σ1 (.n (B + 2)))) (.n rw) (fkWeight t w) with hσ2
  have he2 : ∀ k, k ≠ rn → k ≠ rw → σ2 (.n k) = σ1 (.n k) := fun k h1 h2 => by
    rw [hσ2, Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp; omega)]
  have hext2 : Ext lo hi σ σ2 := by
    refine ((hext.mono hb (by omega)).comp (he1.mono hb hhi)).comp fun v hv => ?_
    rw [hσ2, Function.update_of_ne (hv rw hrw.1 (by omega)), Function.update_of_ne (hv rn hrn.1 (by omega))]
  have hrw2 : σ2 (.n rw) = fkWeight t w := by rw [hσ2, Function.update_self]
  have hrn2 : σ2 (.n rn) = σ1 (.n (B + 2)) := by
    rw [hσ2, Function.update_of_ne (by simp; omega), Function.update_self]
  refine completes_atoms (by
      rw [fkArm_split, atomsOnly_append, show atomsOnly (fkPre t keyAt b) = true from hpre.atoms]; rfl) hext2
    ⟨fun i hi => ?_, by rw [hrn2]; exact hc1 _ (by omega) (by omega), hrw2⟩ (fun a ha => ?_)
  · have hp : b ≤ fkCB t keyAt 0 b i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact le_rfl
      · exact le_of_lt (fkCB_lt (lo := b) (by omega) le_rfl hkb 0 i hpos (by omega))
    rw [he2 _ (by omega) (by omega),
      hk1 _ _ (List.mem_append_left _ (fkChains_hint_mem 6 0 b i hi)) _ (List.mem_singleton_self _), hval i hi]
  · rw [fkArm_split] at ha
    simp only [Bool.false_eq_true, ↓reduceIte] at ha
    rcases List.mem_append.mp ha with ha | ha
    · refine (atom_congr a fun v hv => ?_).mp (ha1 a ha)
      rcases KSeq.vals_rd le_rfl hpre v (mem_valsList_of_mem ha hv) with ⟨k, h1, h2, rfl⟩ | ⟨hx, -⟩
      · exact (he2 k (by omega) (by omega)).symm
      · obtain ⟨k, hk', rfl⟩ := sx_nb (lo := lo) hlo hk hx
        exact (he2 k (by omega) (by omega)).symm
    · simp only [copyS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · show σ2 (.n rn) = σ2 (.n (B + 2))
        rw [hrn2, he2 _ (by omega) (by omega)]
      · exact hrw2

/-! ## The arms' bases -/

theorem fkArmsRest_snd_succ (w : Nat) (keyAt rN rW : V) : ∀ (m t b : Nat),
    (fkArmsRest w keyAt rN rW (m + 1) t b).2 =
      (fkArm (t + m) w keyAt rN rW false (fkArmsRest w keyAt rN rW m t b).2).2
  | 0, t, b => by simp [fkArmsRest]
  | m + 1, t, b => by
      have := fkArmsRest_snd_succ w keyAt rN rW m (t + 1) (fkArm t w keyAt rN rW false b).2
      simp only [fkArmsRest] at this ⊢
      rw [this, show t + 1 + m = t + (m + 1) by omega]

theorem fkAB_one (w : Nat) (keyAt : V) (b : Nat) :
    fkAB w keyAt b 1 = (fkArm 0 w keyAt (.n 0) (.n 0) true b).2 := rfl

theorem fkAB_succ {w : Nat} {keyAt : V} {b t : Nat} (ht : 1 ≤ t) :
    fkAB w keyAt b (t + 1) = (fkArm t w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 false
      (fkAB w keyAt b t)).2 := by
  unfold fkAB
  simp only [Nat.add_one_ne_zero, ↓reduceIte, show t ≠ 0 by omega, Nat.add_sub_cancel]
  rw [show t = t - 1 + 1 by omega, fkArmsRest_snd_succ, show 1 + (t - 1) = t - 1 + 1 by omega,
    Nat.add_sub_cancel]

theorem fkArms_end (w : Nat) (keyAt : V) (b : Nat) : (fkArms w keyAt b).2.1 = fkAB w keyAt b 256 := by
  unfold fkAB fkArms
  simp only [show (256 : Nat) ≠ 0 by norm_num, ↓reduceIte]

theorem fkArms_outs (w : Nat) (keyAt : V) (b : Nat) :
    (fkArms w keyAt b).2.2.1 = .n ((fkChains 0 keyAt 6 0 b).2.1 + 15) ∧
      (fkArms w keyAt b).2.2.2 = .n ((fkChains 0 keyAt 6 0 b).2.1 + 16) := by
  simp only [fkArms, fkArm, ↓reduceIte]
  constructor <;> congr 1

theorem fkArms_getN {w : Nat} {keyAt : V} {b t : Nat} (ht : 1 ≤ t) (ht' : t < 256) :
    (fkArms w keyAt b).1[t]'(by rw [fkArms_length]; exact ht') =
      (fkArm t w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 false (fkAB w keyAt b t)).1 := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have := fkArmsRest_getElem w keyAt (fkArms w keyAt b).2.2.1 (fkArms w keyAt b).2.2.2 255 1
    (fkArm 0 w keyAt (.n 0) (.n 0) true b).2 t' (by rw [fkArmsRest_length]; omega)
  rw [show 1 + t' = t' + 1 by omega] at this
  exact this

theorem fkAB_mono {w : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ b) (hk : NBv b keyAt) :
    ∀ t, b ≤ fkAB w keyAt b t ∧ ∀ t', t ≤ t' → fkAB w keyAt b t ≤ fkAB w keyAt b t' := by
  have step : ∀ t, b ≤ fkAB w keyAt b t → fkAB w keyAt b t < fkAB w keyAt b (t + 1) := by
    intro t ht
    have hc := fun (t0 : Nat) (b0 : Nat) (h : b ≤ b0) =>
      KSeq.le (fkChains_kseq (t := t0) (lo := b) hlo hk 6 0 b0 (by omega) h).1
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [fkAB_one, fkArm_snd]
      have := hc 0 b le_rfl
      simp only [↓reduceIte]
      unfold fkAB; simp only [↓reduceIte]
      omega
    · rw [fkAB_succ hpos, fkArm_snd]
      have := hc t (fkAB w keyAt b t) ht
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
  have hge : ∀ t, b ≤ fkAB w keyAt b t := by
    intro t
    induction t with
    | zero => unfold fkAB; simp
    | succ t ih => exact le_of_lt (lt_of_le_of_lt ih (step t ih))
  refine fun t => ⟨hge t, fun t' htt' => ?_⟩
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact le_rfl
  | succ t' ih =>
      rcases Nat.lt_or_ge t (t' + 1) with h | h
      · exact le_trans (ih (by omega)) (le_of_lt (step t' (hge t')))
      · have : t = t' + 1 := by omega
        subst this; exact le_rfl

/-- **The forest keys' dispatch completes** on the digest's byte `t`, its chains' values loaded. -/
theorem fkArms_complete {w t : Nat} {keyAt x : V} {b : Nat} (ht : t < 256) (hlo : 206 ≤ b)
    (hk : NBv b keyAt) (hx : NBv b x) (vals : Nat → E) (hv : ∀ i < 6, IsCanonical128 (vals i))
    (σ : Val) (hX : ∀ v, SX keyAt keyAt v → NBv b v → IsCanonical128 (σ v)) (hxv : σ x = ofK (gpow t)) :
    Completes C rd b (fkArms w keyAt b).2.1 [.match_ x (fkArms w keyAt b).1] σ
      (fun σ' => (∀ i < 6, σ' (.n (fkCB t keyAt 0 (fkAB w keyAt b t) i)) = vals i) ∧
        IsCanonical128 (σ' (fkArms w keyAt b).2.2.1) ∧ σ' (fkArms w keyAt b).2.2.2 = fkWeight t w) := by
  have hm := fkAB_mono (w := w) hlo hk
  obtain ⟨o1, o2⟩ := fkArms_outs w keyAt b
  have hB0 : b ≤ (fkChains 0 keyAt 6 0 b).2.1 :=
    KSeq.le (fkChains_kseq (t := 0) (lo := b) hlo hk 6 0 b (by omega) le_rfl).1
  have h1 : fkAB w keyAt b 1 = (fkChains 0 keyAt 6 0 b).2.1 + 17 := by rw [fkAB_one, fkArm_snd]; rfl
  have hend1 : fkAB w keyAt b 1 ≤ (fkArms w keyAt b).2.1 := by rw [fkArms_end]; exact (hm 1).2 256 (by omega)
  refine match_complete (by rw [fkArms_length]; exact ht) hx hxv ?_
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · refine (fkArm0_complete (C := C) (rd := rd) (t := 0) (w := w) hlo hk vals hv σ hX).mono le_rfl
      (by omega) (fun σ' ⟨p1, p2, p3⟩ => ⟨p1, by rw [o1]; exact p2, by rw [o2]; exact p3⟩)
  · rw [fkArms_getN hpos ht, o1, o2]
    have hbt := (hm 1).2 t hpos
    have hnext := fkAB_succ (w := w) (keyAt := keyAt) (b := b) hpos
    rw [fkArm_snd] at hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hnext
    have hend : fkAB w keyAt b (t + 1) ≤ (fkArms w keyAt b).2.1 := by
      rw [fkArms_end]; exact (hm (t + 1)).2 256 (by omega)
    exact fkArmN_complete (C := C) (rd := rd) (lo := b) hlo (hm t).1 hk ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega) vals hv σ hX

/-- **The forest keys' values lie below their end.** -/
theorem fkArms_numBelow {w : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ b) (hk : NBv b keyAt) :
    NumBelow (fkArms w keyAt b).2.1 (Stmt.valsArms (fkArms w keyAt b).1) := by
  have hm := fkAB_mono (w := w) hlo hk
  obtain ⟨o1, o2⟩ := fkArms_outs w keyAt b
  have hB0 : b ≤ (fkChains 0 keyAt 6 0 b).2.1 :=
    KSeq.le (fkChains_kseq (t := 0) (lo := b) hlo hk 6 0 b (by omega) le_rfl).1
  have h1 : fkAB w keyAt b 1 = (fkChains 0 keyAt 6 0 b).2.1 + 17 := by rw [fkAB_one, fkArm_snd]; rfl
  have hend1 : fkAB w keyAt b 1 ≤ (fkArms w keyAt b).2.1 := by rw [fkArms_end]; exact (hm 1).2 256 (by omega)
  refine numBelow_valsArms _ fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  rw [fkArms_length] at ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · have e : (fkArms w keyAt b).1[0]'(by rw [fkArms_length]; norm_num) =
        (fkArm 0 w keyAt (.n 0) (.n 0) true b).1 := rfl
    rw [e, fkArm_split]
    simp only [↓reduceIte]
    have hpre := fkArmPre_kseq (t := 0) (lo := b) hlo le_rfl hk
    rw [valsList_append]
    refine ((KSeq.numBelow le_rfl hpre).mono (by omega)).append ?_
    simp only [copyS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
      List.nil_append]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
  · rw [fkArms_getN hpos ht, fkArm_split, o1, o2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hbt := (hm t).1
    have hpre := fkArmPre_kseq (t := t) (lo := fkAB w keyAt b t) (by omega) le_rfl (hk.mono' hbt)
    have hBt : fkAB w keyAt b t ≤ (fkChains t keyAt 6 0 (fkAB w keyAt b t)).2.1 :=
      KSeq.le (fkChains_kseq (t := t) (lo := fkAB w keyAt b t) (by omega) (hk.mono' hbt) 6 0 _ (by omega)
        le_rfl).1
    have hnext := fkAB_succ (w := w) (keyAt := keyAt) (b := b) hpos
    rw [fkArm_snd] at hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hnext
    have hend : fkAB w keyAt b (t + 1) ≤ (fkArms w keyAt b).2.1 := by
      rw [fkArms_end]; exact (hm (t + 1)).2 256 (by omega)
    have hb1 := (hm 1).2 t hpos
    rw [valsList_append]
    refine ((KSeq.numBelow le_rfl hpre).mono (by omega)).append ?_
    simp only [copyS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
      List.nil_append]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))

/-- **Arm `t`'s chains' values lie below the dispatch's end.** -/
theorem fkCB_lt_end {w t : Nat} {keyAt : V} {b : Nat} (hlo : 206 ≤ b) (hk : NBv b keyAt) (ht : t < 256)
    {i : Nat} (hi : i < 6) : b ≤ fkCB t keyAt 0 (fkAB w keyAt b t) i ∧
      fkCB t keyAt 0 (fkAB w keyAt b t) i < (fkArms w keyAt b).2.1 := by
  have hm := fkAB_mono (w := w) hlo hk
  have hbt := (hm t).1
  have hkt : NBv (fkAB w keyAt b t) keyAt := hk.mono' hbt
  have h6 : fkCB t keyAt 0 (fkAB w keyAt b t) i < (fkChains t keyAt 6 0 (fkAB w keyAt b t)).2.1 :=
    fkCB_lt (lo := fkAB w keyAt b t) (by omega) le_rfl hkt i 6 hi le_rfl
  have hge : fkAB w keyAt b t ≤ fkCB t keyAt 0 (fkAB w keyAt b t) i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · exact le_of_lt (fkCB_lt (lo := fkAB w keyAt b t) (by omega) le_rfl hkt 0 i hpos (by omega))
  have hnext : (fkChains t keyAt 6 0 (fkAB w keyAt b t)).2.1 ≤ fkAB w keyAt b (t + 1) := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [fkAB_one, fkArm_snd]
      simp only [↓reduceIte]
      unfold fkAB; simp only [↓reduceIte]
      omega
    · rw [fkAB_succ hpos, fkArm_snd]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
  have hend : fkAB w keyAt b (t + 1) ≤ (fkArms w keyAt b).2.1 := by
    rw [fkArms_end]; exact (hm (t + 1)).2 256 (by omega)
  exact ⟨by omega, by omega⟩

end
end LeanVM.Guest.B1.Sig
