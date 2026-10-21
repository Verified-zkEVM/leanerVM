/-
  LeanVM.Guest.B1.Comp.Whir.OsCapC

  The honest Merkle cap of a level over a total hash, its hashed nodes the model's answers.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OpenAns
public import LeanVM.Guest.B1.Comp.Whir.StackedDataW
public import LeanVM.Guest.B1.Whir.OsCapRun

/-!
# The honest cap over a completeness model (TRIAGE #29, #30)

`Whir/OsCap.lean` and `OsCapRun.lean` over a total hash `Ht`: the openings agree at the cap under
`Ht` (`NodeIsW`, `BatchAgreesW`, `CapsAgreeWith`'s `NodeIsWith`, `BatchAgreesWith`), node `v`'s
digest `osCapDW`, the cap's cells `osCapCellsW` (the flags `osCapFlags` read no hash),
`OsCapOkW`. Its hashed nodes are the model's answers when every level of every opening's climb is
(`OsCapAns`, from `openAll_answered`): `os_cap_hashedC`, and `verify_merkle_cap` on the honest cap
means the root over the model (`osCap_meaningC`, `MeaningVerifyMerkleCapComp`), what
`verify_merkle_cap_comp` takes. `osCap_leafW`, `osCap_parentW`: what `opening_queries` reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

/-- **The opening `a` gives the heap node `v` the digest `d`, over `Ht`** (`NodeIs`). -/
def NodeIsW (Ht : Bytes → Digest) (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧ d = climbAtW Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path l) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one step agree wherever they meet, over `Ht` (`BatchAgrees`). -/
def BatchAgreesW (Ht : Bytes → Digest) (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIsW Ht depth a v d → NodeIsW Ht depth b v d' → d = d'

theorem batchAgreesW_blake (depth : ℕ) (qs : List (ℕ × Opening)) :
    BatchAgreesW blake2sBytes depth qs ↔ BatchAgrees depth qs := Iff.rfl

/-- Node `v`'s digest: one an opening gives it, `default` if none does. -/
noncomputable def osCapDW (Ht : Bytes → Digest) (depth : ℕ) (qs : List (ℕ × Opening)) (v : ℕ) : Digest := by
  classical
  exact if h : ∃ d, ∃ a ∈ qs, NodeIsW Ht depth a v d then Classical.choose h else default

/-- The cap's cells: node `v`'s two scalars at `2v`, `2v + 1`, for `v < 2^(cd + 1)`. -/
noncomputable def osCapCellsW (Ht : Bytes → Digest) (depth cd : ℕ) (qs : List (ℕ × Opening)) : List E :=
  (List.range (2 ^ (cd + 1))).flatMap fun v =>
    [(digestScalars (osCapDW Ht depth qs v)).1, (digestScalars (osCapDW Ht depth qs v)).2]

/-- What the level's openings satisfy: each climbs to `rt` from below `2^depth`, at least one. -/
structure OsCapOkW (Ht : Bytes → Digest) (depth cd : ℕ) (rt : Digest) (qs : List (ℕ × Opening)) : Prop where
  agree : BatchAgreesW Ht depth qs
  pos : ∀ a ∈ qs, a.1 < 2 ^ depth
  len : ∀ a ∈ qs, a.2.path.length = depth
  root : ∀ a ∈ qs, climb (m := Id) Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path = rt
  ne : qs ≠ []
  cd1 : 1 ≤ cd
  cdd : cd ≤ depth

variable {Ht : Bytes → Digest} {depth cd : ℕ} {rt : Digest} {qs : List (ℕ × Opening)}

theorem osCapD_eqW (h : OsCapOkW Ht depth cd rt qs) {a : ℕ × Opening} (ha : a ∈ qs) {v : ℕ} {d : Digest}
    (hv : NodeIsW Ht depth a v d) : osCapDW Ht depth qs v = d := by
  classical
  have hex : ∃ d, ∃ a ∈ qs, NodeIsW Ht depth a v d := ⟨d, a, ha, hv⟩
  unfold osCapDW
  simp only [hex, ↓reduceDIte]
  obtain ⟨b, hb, hbv⟩ := Classical.choose_spec hex
  exact h.agree b hb a ha v _ d hbv hv

/-- What the model answers of a level's openings: each level of each climb (`OpeningAns`). -/
def OsCapAns (CM : CompModel) (Ht : Bytes → Digest) (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ l < depth, CM.H (climbLvlBytes Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path l) =
    some (climbAtW Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path (l + 1))

/-- **A hashed node of the cap is the model's answer** for its children's bytes. -/
theorem os_cap_hashedC {CM : CompModel} (h : OsCapOkW Ht depth cd rt qs) (hA : OsCapAns CM Ht depth qs)
    {a : ℕ × Opening} (ha : a ∈ qs) {l : ℕ} (hl : l < depth) :
    CM.H (digestBytes (osCapDW Ht depth qs (2 * heapNode depth a.1 (l + 1))) ++
      digestBytes (osCapDW Ht depth qs (2 * heapNode depth a.1 (l + 1) + 1))) =
      some (osCapDW Ht depth qs (heapNode depth a.1 (l + 1))) := by
  have hc : osCapDW Ht depth qs (heapNode depth a.1 (l + 1)) =
      climbAtW Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path (l + 1) :=
    osCapD_eqW h ha (Or.inl ⟨l + 1, hl, rfl, rfl⟩)
  have hcl : osCapDW Ht depth qs (heapNode depth a.1 l) = climbAtW Ht (hashWordsW Ht a.2.leaf) a.1 a.2.path l :=
    osCapD_eqW h ha (Or.inl ⟨l, hl.le, rfl, rfl⟩)
  have hsb : osCapDW Ht depth qs (sibNode depth a.1 l) = a.2.path.getD l default :=
    osCapD_eqW h ha (Or.inr ⟨l, hl, rfl, rfl⟩)
  have hans := hA a ha l hl
  rw [hc]
  have hn := heapNode_succ (q := a.1) hl
  unfold sibNode at hsb
  unfold climbLvlBytes at hans
  cases hb : a.1.testBit l
  · simp only [hb, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, Bool.false_eq_true,
      ↓reduceIte] at hn hsb hans
    rw [hn] at hcl
    rw [hcl, hsb]
    exact hans
  · simp only [hb, Bool.not_true, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, ↓reduceIte] at hn hsb hans
    rw [hn] at hcl
    rw [hcl, hsb]
    exact hans

theorem os_capCells_getDW (v : ℕ) (hv : v < 2 ^ (cd + 1)) (i : ℕ) (hi : i < 2) :
    (osCapCellsW Ht depth cd qs).getD (2 * v + i) 0 =
      [(digestScalars (osCapDW Ht depth qs v)).1, (digestScalars (osCapDW Ht depth qs v)).2].getD i 0 := by
  unfold osCapCellsW
  rw [List.flatMap, oq_getD_flatten_uniform _ 2 (fun _ => rfl) _ v i hv hi]

theorem os_capCells_lengthW : (osCapCellsW Ht depth cd qs).length = 2 * 2 ^ (cd + 1) := by
  unfold osCapCellsW
  rw [List.flatMap, oq_length_flatten_uniform _ 2 (fun _ => rfl)]

theorem os_capCellW {rd : Reader} {cap : E} (hr : ReadsAt rd cap (osCapCellsW Ht depth cd qs)) {v : ℕ}
    (hv : v < 2 ^ (cd + 1)) : CapCell rd cap v (osCapDW Ht depth qs v) := by
  have hl := (os_capCells_lengthW (Ht := Ht) (depth := depth) (cd := cd) (qs := qs))
  have g := fun i (hi : i < 2) => by
    have := hr (2 * v + i) (by rw [hl]; omega)
    rwa [← List.getD_eq_getElem _ 0, os_capCells_getDW v hv i hi] at this
  exact ⟨by simpa using g 0 (by omega), by simpa using g 1 (by omega)⟩

/-- **`verify_merkle_cap` on the honest cap** means the level's root. -/
theorem osCap_meaningC {CM : CompModel} (h : OsCapOkW Ht depth cd rt qs) (hA : OsCapAns CM Ht depth qs)
    {rd : Reader} {cap flags : E}
    (hcap : ReadsAt rd cap (osCapCellsW Ht depth cd qs)) (hfl : ReadsAt rd flags (osCapFlags depth cd qs)) :
    MeaningVerifyMerkleCapComp CM cd rd [cap, flags] [(digestScalars rt).1, (digestScalars rt).2] := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, a ∈ qs := by
    cases hq : qs with
    | nil => exact absurd hq h.ne
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  have hq := h.pos a ha
  have hcd1 := h.cd1
  have hcdd := h.cdd
  have h2 : 4 ≤ 2 ^ (cd + 1) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (cd + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have htop := os_heapNode_top (depth := depth) hq
  have hroot : osCapDW Ht depth qs 1 = rt := by
    rw [← htop, osCapD_eqW h ha (Or.inl ⟨depth, le_rfl, rfl, rfl⟩), ← h.len a ha, climbAtW_length, h.root a ha]
  have hh1 := os_cap_hashedC h hA ha (l := depth - 1) (by omega)
  rw [show depth - 1 + 1 = depth by omega, htop] at hh1
  refine ⟨os_onClimb_flag hfl (by
      calc 1 < 2 := by decide
        _ ≤ 2 ^ cd := by calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ cd := Nat.pow_le_pow_right (by decide) hcd1)
      ⟨a, ha, depth, by omega, le_rfl, htop.symm⟩,
    ⟨osCapDW Ht depth qs 2, osCapDW Ht depth qs 3, osCapDW Ht depth qs 1, os_capCellW hcap (by omega),
      os_capCellW hcap (by omega), hh1, os_capCellW hcap (by omega)⟩, fun c hc2 hc => ?_,
    rt, by rw [← hroot]; exact os_capCellW hcap (by omega), rfl⟩
  have hfc := os_capFlag hfl hc
  by_cases hon : OsOnClimb depth cd qs c
  · simp only [hon, ↓reduceIte] at hfc
    refine ⟨1, hfc, (isInK_iff _).mpr ⟨1, by simp⟩, fun _ => ?_⟩
    obtain ⟨b, hb, l, hl1, hl2, rfl⟩ := hon
    have hqb := h.pos b hb
    have hlt : l < depth := by
      rcases Nat.lt_or_ge l depth with h' | h'
      · exact h'
      · obtain rfl : l = depth := by omega
        rw [os_heapNode_top hqb] at hc2; omega
    refine ⟨?_, ?_⟩
    · rw [os_heapNode_half hlt]
      exact os_onClimb_flag hfl (os_heapNode_cap hqb (by omega) (by omega)) ⟨b, hb, l + 1, by omega, by omega, rfl⟩
    · have hl0 : l = l - 1 + 1 := by omega
      have hhb := os_cap_hashedC h hA hb (l := l - 1) (by omega)
      rw [← hl0] at hhb
      have hcl := os_heapNode_cap (cd := cd) hqb hl1 hl2
      exact ⟨osCapDW Ht depth qs (2 * heapNode depth b.1 l), osCapDW Ht depth qs (2 * heapNode depth b.1 l + 1),
        osCapDW Ht depth qs (heapNode depth b.1 l),
        os_capCellW hcap (by rw [pow_succ]; omega), os_capCellW hcap (by rw [pow_succ]; omega), hhb,
        os_capCellW hcap (by rw [pow_succ]; omega)⟩
  · simp only [hon, ↓reduceIte] at hfc
    exact ⟨0, hfc, (isInK_iff _).mpr ⟨0, by simp⟩, fun h0 => absurd rfl h0⟩

/-- **An opening's cap leaf** holds its climb below the cap. -/
theorem osCap_leafW (h : OsCapOkW Ht depth cd rt qs) {rd : Reader} {cap : E}
    (hcap : ReadsAt rd cap (osCapCellsW Ht depth cd qs)) {a : ℕ × Opening} (ha : a ∈ qs) :
    CapCell rd cap (2 ^ cd + a.1 / 2 ^ (depth - cd))
      (climb (m := Id) Ht (hashWordsW Ht a.2.leaf) a.1 (a.2.path.take (depth - cd))) := by
  have hq := h.pos a ha
  have e : 2 ^ cd + a.1 / 2 ^ (depth - cd) = heapNode depth a.1 (depth - cd) := by
    rw [heapNode, show depth - (depth - cd) = cd by have := h.cdd; omega]
  have hlt := os_heapNode_lt (depth := depth) hq (l := depth - cd) (by omega)
  rw [show depth - (depth - cd) + 1 = cd + 1 by have := h.cdd; omega] at hlt
  have hd := osCapD_eqW h ha (Or.inl ⟨depth - cd, by omega, rfl, rfl⟩)
  have hc := os_capCellW hcap hlt
  rw [hd] at hc
  rw [e]; exact hc

/-- **An opening's cap leaf's parent** is flagged. -/
theorem osCap_parentW (h : OsCapOkW Ht depth cd rt qs) {rd : Reader} {flags : E}
    (hfl : ReadsAt rd flags (osCapFlags depth cd qs)) {a : ℕ × Opening} (ha : a ∈ qs) :
    LoadHolds rd flags (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) 1 := by
  have hq := h.pos a ha
  have hcd1 := h.cd1
  have hcdd := h.cdd
  have e : 2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1) = heapNode depth a.1 (depth - cd + 1) := by
    rw [heapNode, show depth - (depth - cd + 1) = cd - 1 by omega]
  rw [e]
  exact os_onClimb_flag hfl (os_heapNode_cap hq (by omega) (by omega)) ⟨a, ha, depth - cd + 1, by omega, by omega, rfl⟩


/-- **`openAll`, inverted**: one opening per position, each of the shape and climbing to the root. -/
theorem os_openAll_invW {root : Digest} {hh ww : ℕ} : ∀ (ps : List ℕ) (os : List Opening) (rows : List (List K))
    (rest : List Opening), openAll (m := Id) Ht root hh ww ps os = some (rows, rest) →
    ∃ os1, os = os1 ++ rest ∧ os1.length = ps.length ∧ rows = os1.map (·.leaf) ∧
      ∀ j (hj : j < os1.length), (os1[j]).leaf.length = ww ∧ (os1[j]).path.length = hh ∧
        climb (m := Id) Ht (hashWordsW Ht (os1[j]).leaf) (ps.getD j 0) (os1[j]).path = root
  | [], os, rows, rest, h => by
    simp only [openAll] at h
    cases h
    exact ⟨[], rfl, rfl, rfl, fun j hj => absurd hj (by simp)⟩
  | _ :: _, [], _, _, h => by simp [openAll] at h
  | q :: ps, o :: os, rows, rest, h => by
    simp only [openAll, bind] at h
    split at h
    · rename_i hok
      match hr : openAll (m := Id) Ht root hh ww ps os, h with
      | some (rows', rest'), h =>
        simp only [Option.map_some, pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨os1, rfl, hl, rfl, hj⟩ := os_openAll_invW ps os _ _ hr
        simp only [openOne] at hok
        split at hok
        · rename_i hsh
          have htop : climb (m := Id) Ht (hashWordsW Ht o.leaf) q o.path = root := by
            have := of_decide_eq_true hok
            exact Vector.toList_inj.mp this
          refine ⟨o :: os1, rfl, by simp [hl], by simp, fun j hj' => ?_⟩
          rcases j with _ | j
          · exact ⟨hsh.1, hsh.2, by simpa using htop⟩
          · simpa using hj j (by simpa using hj')
        · cases hok
    · cases h

/-- **A level's openings fill its cap**: its positions, below `2^depth`, zipped with its openings. -/
theorem os_capOk_ofW {cfg : OsCfg} {lvl : ℕ} {xs : List E} {p : ℕ} {cv1 : Digest} {osp osq : List Opening}
    {rt : Digest} {hh ww : ℕ} {rows : List (List K)}
    (hoa : openAll (m := Id) Ht rt hh ww (osHQsW Ht cfg lvl xs p cv1) osp = some (rows, osq))
    (hag : BatchAgreesW Ht hh ((osHQsW Ht cfg lvl xs p cv1).zip osp)) (hhd : hh = (cfg.lv lvl).depth)
    (hq : 0 < (cfg.lv lvl).queries) (hcd1 : 1 ≤ (cfg.lv lvl).capDepth)
    (hcd2 : (cfg.lv lvl).capDepth ≤ (cfg.lv lvl).depth) :
    OsCapOkW Ht (cfg.lv lvl).depth (cfg.lv lvl).capDepth rt ((osHQsW Ht cfg lvl xs p cv1).zip osp) := by
  subst hhd
  obtain ⟨os1, rfl, hl, -, hj⟩ := os_openAll_invW _ _ _ _ hoa
  have hql : (osHQsW Ht cfg lvl xs p cv1).length = (cfg.lv lvl).queries := by simp [osHQsW]
  have hmem : ∀ a ∈ (osHQsW Ht cfg lvl xs p cv1).zip (os1 ++ osq), ∃ j, ∃ hj : j < os1.length,
      a = ((osHQsW Ht cfg lvl xs p cv1).getD j 0, os1[j]) := by
    intro a ha
    obtain ⟨j, hj1, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_zip, List.length_append] at hj1
    refine ⟨j, by omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨hag, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, ?_, hcd1, hcd2⟩
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    simp only [osHQsW]
    rw [os_getD_map_range _ (by omega), osPosOfW]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    exact (hj j hj').2.1
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    exact (hj j hj').2.2
  · intro h0
    have := congrArg List.length h0
    simp only [List.length_zip, List.length_append, List.length_nil] at this
    omega


end
end LeanVM.Guest.B1
