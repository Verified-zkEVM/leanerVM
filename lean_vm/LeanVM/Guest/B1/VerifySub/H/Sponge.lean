/-
  LeanVM.Guest.B1.VerifySub.H.Sponge

  `verify_sub`'s sponge on its honest valuation: the seed's capacity, the announced words and the
  root absorbed, every squeeze's challenge, from the evaluation alone (no store).
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Body
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Back

/-!
# The sponge, honestly

The honest valuation `vsσ rd w args` carries the Spec's sponge as the soundness proof reads it
(`Front.lean`, `Tail.lean`), with no store of `verify_sub` involved: the stores only check what the
evaluation computed. So the challenges are known before the memory's own buffers are.

* `vs_zero`: the zero cells `10 .. 13`;
* `vs_kecOut`: a `KECCAK` atom's outputs are canonical;
* `vs_sqz`: a squeeze (`vsSqzT`) on canonical capacity cells: its challenge and capacity;
* `vsH_front`: from the stream's first ten words in memory, the seed's capacity, the announced
  words and the root absorbed, the four bus challenges, `β` (`VsFrontS`);
* `vsH_maps`: the ring map's five squeezed challenges; `vsH_lam`: the batching challenge.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The zero cells.** -/
theorem vs_zero (hl : args.length = 7) : ∀ i ∈ [10, 11, 12, 13], vsσ rd w args (.n i) = 0 := by
  intro i hi
  have hmc : ∀ i ∈ [10, 11, 12, 13], vsConst i (word 0 0 0) ∈ vsCPre := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact vs_mem_slice (n := 3) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 4) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 5) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 6) (blk := [_]) (by decide +kernel) List.mem_cons_self
  have h := vs_goodS (rd := rd) (w := w) hl (hmc i hi)
  simp only [vsConst, fixNe, GoodS, Good] at h
  rw [h, word_zero]

set_option maxRecDepth 100000 in
/-- **A `KECCAK` atom's outputs are canonical.** -/
theorem vs_kecOut (hl : args.length = 7) {ins : List V} {o : ℕ}
    (hm : keccakA ins (vsRun o 13) ∈ vsCPre) :
    ∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k))) := by
  have hg := vs_goodS (rd := rd) (w := w) hl hm
  rw [fixNe_of_noNe (s := keccakA ins (vsRun o 13)) (by simp [keccakA, noNeB])] at hg
  simp only [keccakA, GoodS] at hg
  intro k hk13
  have := hg.2.2 ⟨k, hk13⟩
  simp [cells13, vsRun, List.getD_eq_getElem?_getD, hk13] at this
  rw [this]
  exact canon_cellsOfState _ _ _

/-- **A `KECCAK` atom on canonical inputs holds.** -/
theorem vs_kecHolds (hl : args.length = 7) {ins : List V} {o : ℕ}
    (hm : keccakA ins (vsRun o 13) ∈ vsCPre) (hc : AllCanonical (ins.map (vsσ rd w args))) :
    (Atom.keccak ins (vsRun o 13) false false).Holds rd (vsσ rd w args) := by
  have hg := vs_goodS (rd := rd) (w := w) hl hm
  rw [fixNe_of_noNe (s := keccakA ins (vsRun o 13)) (by simp [keccakA, noNeB])] at hg
  exact keccakA_complete (S := vsSL) (w := w) hg hc

/-- A squeeze's inputs: the zero cells and a canonical capacity. -/
theorem vs_sqzIn (hl : args.length = 7) {capb : ℕ}
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) :
    AllCanonical (([V.n 10, V.n 10, V.n 10, V.n 10, V.n 10, V.n 11, V.n 12, V.n 13] ++
      vsRun capb 5).map (vsσ rd w args)) := by
  have hz := vs_zero (rd := rd) (w := w) hl
  have hz' : ∀ i ∈ [10, 11, 12, 13], IsCanonical128 (vsσ rd w args (.n i)) :=
    fun i hi ↦ by rw [hz i hi]; exact canonical_zero
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  simp only [vsRun, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
    List.mem_range] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact hz' 10 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 11 (by simp)
  · exact hz' 12 (by simp)
  · exact hz' 13 (by simp)
  · exact hc i hi

/-- **A squeeze, honestly**: on canonical capacity cells, its challenge and capacity, its outputs
canonical. -/
theorem vs_sqz (hl : args.length = 7) {capb o : ℕ} (hmem : ∀ s ∈ vsSqzT capb o, s ∈ vsCPre)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) :
    (⟨(vsRun capb 5).map (vsσ rd w args), []⟩ : Fs).squeeze =
        (vsσ rd w args (.n (o + 19)), ⟨[vsσ rd w args (.n (o + 8)), vsσ rd w args (.n (o + 9)),
          vsσ rd w args (.n (o + 10)), vsσ rd w args (.n (o + 11)), vsσ rd w args (.n (o + 12))],
          []⟩) ∧ ∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k))) := by
  have hz := vs_zero (rd := rd) (w := w) hl
  have h := vsSqzT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl hmem
    hz hc trivial
  refine ⟨(vsSqzT_holds (hz 10 (by simp)) (hz 11 (by simp)) (hz 12 (by simp)) (hz 13 (by simp))
    h).1, ?_⟩
  exact (kc_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl hmem
    (vs_sqzIn hl hc) trivial).1

/-! ## The front -/

/-- **What the honest valuation's front computes**, the stream's first ten words `ws` in memory. -/
structure VsFrontS (rd : Reader) (σ : Val) (ws : List E) : Prop where
  hz : ∀ i ∈ [10, 11, 12, 13], σ (.n i) = 0
  hseed : vsSeedAtom.Holds rd σ
  hcap22 : ∀ i ∈ [22, 23, 24, 25, 26], IsCanonical128 (σ (.n i))
  hx : ∀ i < 8, σ (.n (vsX i)) = ws.getD i 0
  hw : ∀ i < 8, WordAt rd σ i (vsX i)
  e537 : σ (.n 537) = ws.getD 8 0
  e547 : σ (.n 547) = ws.getD 9 0
  hin : ∀ i ∈ [89, 91, 99, 101, 109, 111, 119, 121, 77, 78, 79, 80, 81],
    IsCanonical128 (σ (.n i))
  hc532 : ∀ i < 5, IsCanonical128 (σ (.n (532 + i)))
  hc628 : ∀ i < 5, IsCanonical128 (σ (.n (628 + i)))
  hab8 : (⟨[σ (.n 22), σ (.n 23), σ (.n 24), σ (.n 25), σ (.n 26)], []⟩ : Fs).absorbAll
      (vsWords σ) dsObserve =
    ⟨[σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)],
      [(σ (.n 82), dsObserve), (σ (.n 92), dsObserve), (σ (.n 102), dsObserve),
        (σ (.n 112), dsObserve)]⟩
  habR : (((⟨[σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)],
      [(σ (.n 82), dsObserve), (σ (.n 92), dsObserve), (σ (.n 102), dsObserve),
        (σ (.n 112), dsObserve)]⟩ : Fs).absorb (σ (.n 537)) dsObserve).absorb (σ (.n 547))
      dsObserve) =
    ⟨[σ (.n 532), σ (.n 533), σ (.n 534), σ (.n 535), σ (.n 536)],
      [(σ (.n 537), dsObserve), (σ (.n 547), dsObserve)]⟩
  halpha : (⟨[σ (.n 532), σ (.n 533), σ (.n 534), σ (.n 535), σ (.n 536)],
      [(σ (.n 537), dsObserve), (σ (.n 547), dsObserve)]⟩ : Fs).squeezeN 4 =
    (vsAlphas σ, ⟨[σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632)], []⟩)
  hbeta : (⟨[σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632)], []⟩ : Fs).squeeze =
    (σ (.n 836), ⟨[σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829)], []⟩)
  hc825 : ∀ i < 5, IsCanonical128 (σ (.n (825 + i)))

set_option maxRecDepth 100000 in
/-- **The front, honestly**: with the statement's and the seed's cells canonical and the stream's
first ten words in memory. -/
theorem vsH_front (hl : args.length = 7) (hc4 : ∀ i < 4, IsCanonical128 (args.getD i 0))
    {ws : List E} (hws : ∀ i < 10, LoadHolds rd (vsσ rd w args (.n 27)) i (ws.getD i 0)) :
    VsFrontS rd (vsσ rd w args) ws := by
  have hz := vs_zero (rd := rd) (w := w) hl
  -- the seed
  have hseed : vsSeedAtom.Holds rd (vsσ rd w args) := by
    have h := vsHeadT_complete (rd := rd) (w := w) hl hc4 (keccakA [.n 2, .n 3, .n 0, .n 1, .n 10,
      .n 11, .n 12, .n 13, .n 10, .n 10, .n 11, .n 12, .n 13] (vsRun 14 13)) (by simp [vsHeadT])
    exact h
  have hc14 := vs_kecOut (rd := rd) (w := w) hl (ins := [.n 2, .n 3, .n 0, .n 1, .n 10, .n 11,
    .n 12, .n 13, .n 10, .n 10, .n 11, .n 12, .n 13]) (o := 14)
    (vs_mem_slice (n := 7) (blk := [_]) (by decide +kernel) List.mem_cons_self)
  have hcap22 : ∀ i ∈ [22, 23, 24, 25, 26], IsCanonical128 (vsσ rd w args (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact hc14 8 (by norm_num)
    · exact hc14 9 (by norm_num)
    · exact hc14 10 (by norm_num)
    · exact hc14 11 (by norm_num)
    · exact hc14 12 (by norm_num)
  -- the announced words
  have hws8 : ∀ i < 8, LoadHolds rd (vsσ rd w args (.n 27)) i (ws.getD i 0) :=
    fun i hi ↦ hws i (by omega)
  have W := fun i (hi : i < 8) ↦ vs_word (rd := rd) (w := w) hl hws8 hi
  have hx : ∀ i < 8, vsσ rd w args (.n (vsX i)) = ws.getD i 0 := fun i hi ↦ (W i hi).1
  have hw : ∀ i < 8, WordAt rd (vsσ rd w args) i (vsX i) := fun i hi ↦
    ((holds_fsNextT (C := fun _ _ _ ↦ True) _ _ _ True (fun _ ↦ True)).1
      ((W i hi).2.2.2 trivial)).1
  have mR : ∀ s ∈ vsReadsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 11) (blk := vsReadsT) (by decide +kernel) hs
  have m50 : keccakA [.n 36, .n 38, .n 46, .n 48, .n 56, .n 58, .n 66, .n 68, .n 22, .n 23, .n 24,
      .n 25, .n 26] (vsRun 69 13) ∈ vsCPre := mR _ (by
    simp only [vsReadsT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have hc69 := vs_kecOut (rd := rd) (w := w) hl m50
  have hk50 : vsAtom50.Holds rd (vsσ rd w args) := by
    refine vs_kecHolds hl m50 ?_
    intro x hx'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (W 0 (by norm_num)).2.1
    · exact (W 0 (by norm_num)).2.2.1
    · exact (W 1 (by norm_num)).2.1
    · exact (W 1 (by norm_num)).2.2.1
    · exact (W 2 (by norm_num)).2.1
    · exact (W 2 (by norm_num)).2.2.1
    · exact (W 3 (by norm_num)).2.1
    · exact (W 3 (by norm_num)).2.2.1
    · exact hcap22 22 (by simp)
    · exact hcap22 23 (by simp)
    · exact hcap22 24 (by simp)
    · exact hcap22 25 (by simp)
    · exact hcap22 26 (by simp)
  have hin : ∀ i ∈ [89, 91, 99, 101, 109, 111, 119, 121, 77, 78, 79, 80, 81],
      IsCanonical128 (vsσ rd w args (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (W 4 (by norm_num)).2.1
    · exact (W 4 (by norm_num)).2.2.1
    · exact (W 5 (by norm_num)).2.1
    · exact (W 5 (by norm_num)).2.2.1
    · exact (W 6 (by norm_num)).2.1
    · exact (W 6 (by norm_num)).2.2.1
    · exact (W 7 (by norm_num)).2.1
    · exact (W 7 (by norm_num)).2.2.1
    · exact hc69 8 (by norm_num)
    · exact hc69 9 (by norm_num)
    · exact hc69 10 (by norm_num)
    · exact hc69 11 (by norm_num)
    · exact hc69 12 (by norm_num)
  -- the root
  have hRo := vsRootsT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    (rd := rd) (w := w) hl hin (hws 8 (by norm_num)) (hws 9 (by norm_num)) trivial trivial trivial
  obtain ⟨e537, e547, hcR, hRoH⟩ := hRo
  obtain ⟨hk649, w8, w9, -, -, -⟩ := vsRootsT_holds hRoH
  have mRo : ∀ s ∈ vsRootsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 649) (blk := vsRootsT) (by decide +kernel) hs
  have hc524 := vs_kecOut (rd := rd) (w := w) hl (ins := [V.n 89, V.n 91, V.n 99, V.n 101, V.n 109,
    V.n 111, V.n 119, V.n 121, V.n 77, V.n 78, V.n 79, V.n 80, V.n 81]) (o := 524)
    (mRo _ (by simp [vsRootsT]))
  have hc532 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (532 + i))) := fun i hi ↦ by
    have := hc524 (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  -- the bus challenges
  have mA : ∀ s ∈ vsAlphasT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 671) (blk := vsAlphasT) (by decide +kernel) hs
  have hc1 : AllCanonical ([V.n 544, V.n 546, V.n 554, V.n 556, V.n 10, V.n 11, V.n 12, V.n 13,
      V.n 532, V.n 533, V.n 534, V.n 535, V.n 536].map (vsσ rd w args)) := by
    have hz' : ∀ i ∈ [10, 11, 12, 13], IsCanonical128 (vsσ rd w args (.n i)) :=
      fun i hi ↦ by rw [hz i hi]; exact canonical_zero
    intro x hx'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcR 544 (by simp)
    · exact hcR 546 (by simp)
    · exact hcR 554 (by simp)
    · exact hcR 556 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hz' 12 (by simp)
    · exact hz' 13 (by simp)
    · exact hc532 0 (by norm_num)
    · exact hc532 1 (by norm_num)
    · exact hc532 2 (by norm_num)
    · exact hc532 3 (by norm_num)
    · exact hc532 4 (by norm_num)
  obtain ⟨o1, h1⟩ := kc_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    (rd := rd) (w := w) hl (ins := [V.n 544, V.n 546, V.n 554, V.n 556, V.n 10, V.n 11, V.n 12,
      V.n 13, V.n 532, V.n 533, V.n 534, V.n 535, V.n 536]) (o := 560)
    (fun s hs ↦ mA s (by rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hs)))))))) hc1 trivial
  simp only [Stmt.HoldsList, Stmt.Holds, keccakA] at h1
  obtain ⟨hk1, hch1⟩ := h1
  have hch1' := ((holds_challengeT (C := fun _ _ _ ↦ True) _ _ _ True (fun _ ↦ True)).1 hch1).1
  have c8 := wordAt_cells w8 (hcR 544 (by simp))
  have c9 := wordAt_cells w9 (hcR 554 (by simp))
  have hs := squeeze_atom (s := ⟨[vsσ rd w args (.n 532), vsσ rd w args (.n 533),
    vsσ rd w args (.n 534), vsσ rd w args (.n 535), vsσ rd w args (.n 536)],
    [(vsσ rd w args (.n 537), dsObserve), (vsσ rd w args (.n 547), dsObserve)]⟩) (b := 573) hk1
    (by simp only [List.map_cons, List.map_nil, hz 10 (by simp), hz 11 (by simp),
      hz 12 (by simp), hz 13 (by simp), rateOf_two, ← c8, ← c9]; rfl) hch1'
  rw [vsRun_drop8] at hs
  have sub : ∀ capb o, vsSqzT capb o ⊆ vsAlphasT → ∀ s ∈ vsSqzT capb o, s ∈ vsCPre :=
    fun capb o hsub s hs ↦ mA s (hsub hs)
  have q1 := vs_sqz (rd := rd) (w := w) hl (capb := 568) (o := 580)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))))
    (fun i hi ↦ by have := o1 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q2 := vs_sqz (rd := rd) (w := w) hl (capb := 588) (o := 600)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))
    (fun i hi ↦ by have := q1.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q3 := vs_sqz (rd := rd) (w := w) hl (capb := 608) (o := 620)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_right _ hs)))
    (fun i hi ↦ by have := q2.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have hc628 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (628 + i))) := fun i hi ↦ by
    have := q3.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  -- `β`
  have qb := vs_sqz (rd := rd) (w := w) hl (capb := 628) (o := 817)
    (fun s hs ↦ vs_mem_slice (n := 711) (blk := vsFpwT) (by decide +kernel)
      (by rw [vsFpwT]; exact List.mem_append_right _ hs)) hc628
  refine ⟨hz, hseed, hcap22, hx, hw, by rw [e537], by rw [e547], hin, hc532, hc628,
    vs_absorb8 hw hk50, vs_absorbRoot hw hk649, ?_, qb.1, fun i hi ↦ by
      have := qb.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this⟩
  generalize vsσ rd w args = σ at hs q1 q2 q3 ⊢
  have e0 : (⟨[σ (.n 532), σ (.n 533), σ (.n 534),
      σ (.n 535), σ (.n 536)],
      [(σ (.n 537), dsObserve), (σ (.n 547), dsObserve)]⟩ : Fs).squeeze =
      (σ (.n 579), ⟨[σ (.n 568), σ (.n 569),
        σ (.n 570), σ (.n 571), σ (.n 572)], []⟩) :=
    Prod.ext hs.1.symm (congrArg (Fs.mk · []) hs.2.symm)
  have e1 : (⟨[σ (.n 568), σ (.n 569), σ (.n 570),
      σ (.n 571), σ (.n 572)], []⟩ : Fs).squeeze =
      (σ (.n 599), ⟨[σ (.n 588), σ (.n 589),
        σ (.n 590), σ (.n 591), σ (.n 592)], []⟩) := q1.1
  have e2 : (⟨[σ (.n 588), σ (.n 589), σ (.n 590),
      σ (.n 591), σ (.n 592)], []⟩ : Fs).squeeze =
      (σ (.n 619), ⟨[σ (.n 608), σ (.n 609),
        σ (.n 610), σ (.n 611), σ (.n 612)], []⟩) := q2.1
  have e3 : (⟨[σ (.n 608), σ (.n 609), σ (.n 610),
      σ (.n 611), σ (.n 612)], []⟩ : Fs).squeeze =
      (σ (.n 639), ⟨[σ (.n 628), σ (.n 629),
        σ (.n 630), σ (.n 631), σ (.n 632)], []⟩) := q3.1
  simp only [Fs.squeezeN, vsAlphas, e0, e1, e2, e3]

/-! ## The ring map and the batching -/

theorem vsMaps_sub (capb o : ℕ)
    (h : (capb, o) ∈ [(871, 878), (886, 898), (906, 918), (926, 938), (946, 958)]) :
    ∀ s ∈ vsSqzT capb o, s ∈ vsCPre := by
  intro s hs
  refine vs_mem_slice (n := 929) (blk := vsMapsT) (by decide +kernel) ?_
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rw [vsMapsT]
  simp only [List.mem_append]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

set_option maxRecDepth 100000 in
/-- **The ring map's five squeezed challenges, honestly**, from canonical capacity cells. -/
theorem vsH_maps (hl : args.length = 7)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (871 + i)))) :
    (⟨[vsσ rd w args (.n 871), vsσ rd w args (.n 872), vsσ rd w args (.n 873),
        vsσ rd w args (.n 874), vsσ rd w args (.n 875)], []⟩ : Fs).squeezeN 5 =
      (vsChs (vsσ rd w args), ⟨[vsσ rd w args (.n 966), vsσ rd w args (.n 967),
        vsσ rd w args (.n 968), vsσ rd w args (.n 969), vsσ rd w args (.n 970)], []⟩) ∧
      ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (966 + i))) := by
  have q1 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 871 878 (by simp)) hc
  have q2 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 886 898 (by simp))
    (fun i hi ↦ by have := q1.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q3 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 906 918 (by simp))
    (fun i hi ↦ by have := q2.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q4 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 926 938 (by simp))
    (fun i hi ↦ by have := q3.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q5 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 946 958 (by simp))
    (fun i hi ↦ by have := q4.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  generalize vsσ rd w args = σ at q1 q2 q3 q4 q5 ⊢
  have e1 : (⟨[σ (.n 871), σ (.n 872), σ (.n 873), σ (.n 874), σ (.n 875)], []⟩ : Fs).squeeze =
      (σ (.n 897), ⟨[σ (.n 886), σ (.n 887), σ (.n 888), σ (.n 889), σ (.n 890)], []⟩) := q1.1
  have e2 : (⟨[σ (.n 886), σ (.n 887), σ (.n 888), σ (.n 889), σ (.n 890)], []⟩ : Fs).squeeze =
      (σ (.n 917), ⟨[σ (.n 906), σ (.n 907), σ (.n 908), σ (.n 909), σ (.n 910)], []⟩) := q2.1
  have e3 : (⟨[σ (.n 906), σ (.n 907), σ (.n 908), σ (.n 909), σ (.n 910)], []⟩ : Fs).squeeze =
      (σ (.n 937), ⟨[σ (.n 926), σ (.n 927), σ (.n 928), σ (.n 929), σ (.n 930)], []⟩) := q3.1
  have e4 : (⟨[σ (.n 926), σ (.n 927), σ (.n 928), σ (.n 929), σ (.n 930)], []⟩ : Fs).squeeze =
      (σ (.n 957), ⟨[σ (.n 946), σ (.n 947), σ (.n 948), σ (.n 949), σ (.n 950)], []⟩) := q4.1
  have e5 : (⟨[σ (.n 946), σ (.n 947), σ (.n 948), σ (.n 949), σ (.n 950)], []⟩ : Fs).squeeze =
      (σ (.n 977), ⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩) := q5.1
  refine ⟨by simp only [Fs.squeezeN, vsChs, e1, e2, e3, e4, e5], fun i hi ↦ ?_⟩
  have := q5.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this

/-- **The batching challenge, honestly**, from canonical capacity cells. -/
theorem vsH_lam (hl : args.length = 7)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (966 + i)))) :
    (⟨[vsσ rd w args (.n 966), vsσ rd w args (.n 967), vsσ rd w args (.n 968),
        vsσ rd w args (.n 969), vsσ rd w args (.n 970)], []⟩ : Fs).squeeze =
      (vsσ rd w args (.n 1323), ⟨[vsσ rd w args (.n 1312), vsσ rd w args (.n 1313),
        vsσ rd w args (.n 1314), vsσ rd w args (.n 1315), vsσ rd w args (.n 1316)], []⟩) := by
  have q := vs_sqz (rd := rd) (w := w) hl (capb := 966) (o := 1304)
    (fun s hs ↦ vs_mem_slice (n := 1372) (blk := vsLamT) (by decide +kernel)
      (by rw [vsLamT]; simp only [List.mem_append]; tauto)) hc
  generalize vsσ rd w args = σ at q ⊢
  exact q.1

end
end LeanVM.Guest.B1.VerifySub
