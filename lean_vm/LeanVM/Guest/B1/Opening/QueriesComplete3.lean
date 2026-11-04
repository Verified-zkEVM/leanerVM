/-
  LeanVM.Guest.B1.Opening.QueriesComplete3

  The completeness of a query's Merkle path and cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# A query's path and cap leaf, completeness

The honest nodes are the climb's (`arm_nodes`: each step's pair hash, `level_out`); with the
memory holding the position's windows, the cap leaf and the parent's flag (what `QueryOpens` and
the windows say, `MemOk`), every statement of the path (`oqPath_complete`: each window's match
takes arm `v`, the window's value) and every atom of the cap leaf (`oqCap_complete`) holds at the
honest values.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-! ## The path's values -/

theorem pc_canonical (k : ℕ) : IsCanonical128 (d.pc k) := by
  unfold pc pathCell
  dsimp only
  split <;> exact canonical_ofLimbs _ _

/-- A level's pair hash is the climb's step. -/
theorem level_out {l : ℕ} (hl : l < d.sibs.length) {o0 o1 : E}
    (h : HashesPair (d.pc (4 * l)) (d.pc (4 * l + 1)) (d.pc (4 * l + 2)) (d.pc (4 * l + 3)) o0 o1) :
    (o0, o1) = digestHalves (climbNode d.leaf d.q d.sibs (l + 1)) := by
  obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests h
  have hcs : climbNode d.leaf d.q d.sibs (l + 1) =
      if d.q / 2 ^ l % 2 = 0 then hashPair (climbNode d.leaf d.q d.sibs l) (d.sibs.getD l (Vector.replicate 4 0))
      else hashPair (d.sibs.getD l (Vector.replicate 4 0)) (climbNode d.leaf d.q d.sibs l) := by
    rw [climbNode, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climbD_snoc,
      List.length_take, min_eq_left (by omega)]
    simp [climbNode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have i0 : (4 * l) / 4 = l ∧ (4 * l) % 4 = 0 ∧ (4 * l) % 2 = 0 := by omega
  have i1 : (4 * l + 1) / 4 = l ∧ (4 * l + 1) % 4 = 1 ∧ (4 * l + 1) % 2 = 1 := by omega
  have i2 : (4 * l + 2) / 4 = l ∧ (4 * l + 2) % 4 = 2 ∧ (4 * l + 2) % 2 = 0 := by omega
  have i3 : (4 * l + 3) / 4 = l ∧ (4 * l + 3) % 4 = 3 ∧ (4 * l + 3) % 2 = 1 := by omega
  rw [hp, hcs]
  by_cases hb : d.q.testBit l
  · have hb' : d.q / 2 ^ l % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simpa using hb
    have c0 : d.pc (4 * l) = (digestHalves (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestHalves (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestHalves (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestHalves (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']
  · have hb' : d.q / 2 ^ l % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simp at hb; omega
    have c0 : d.pc (4 * l) = (digestHalves (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestHalves (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestHalves (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestHalves (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']


/-! ## The path -/

/-- What the memory holds of an honest query: its windows at `bpv`, its cap leaf and its flag. -/
structure MemOk (d : QD) (rd : Reader) (bpv : E) : Prop where
  wins : ∀ i < qwN (d.s.pd + d.s.cd) d.s.cd, LoadHolds rd bpv i (gen ^ d.wv i)
  cap0 : LoadHolds rd d.capv (2 * (2 ^ d.s.cd + d.q / 2 ^ d.s.pd))
    (digestHalves (climbD d.leaf d.q d.sibs)).1
  cap1 : LoadHolds rd d.capv (2 * (2 ^ d.s.cd + d.q / 2 ^ d.s.pd) + 1)
    (digestHalves (climbD d.leaf d.q d.sibs)).2
  flag : LoadHolds rd d.flagsv (2 ^ (d.s.cd - 1) + d.q / 2 ^ (d.s.pd + 1)) 1

/-- The children on the walk's side are the node's cells. -/
theorem pc_walk (l : ℕ) :
    d.pc (4 * l + (if d.q.testBit l then 2 else 0)) = (digestHalves (d.node l)).1 ∧
      d.pc (4 * l + (if d.q.testBit l then 2 else 0) + 1) = (digestHalves (d.node l)).2 := by
  unfold pc pathCell node
  cases hb : d.q.testBit l
  · simp [show 4 * l / 4 = l by omega, show (4 * l + 1) / 4 = l by omega, hb,
      show 4 * l % 2 = 0 by omega, show (4 * l + 1) % 2 = 1 by omega]
  · simp [show (4 * l + 2) / 4 = l by omega,
      show (4 * l + 2 + 1) % 4 / 2 = 1 by omega, show (4 * l + 2 + 1) / 4 = l by omega, hb,
      show (4 * l + 2) % 2 = 0 by omega, show (4 * l + 2 + 1) % 2 = 1 by omega]

/-- A step's four cells, either order, are the level's children. -/
theorem step_cells {l n0 n1 : ℕ} {ch : ℕ}
    (hc : ∀ j < 4, σ (.n (ch + 4 * l + j)) = d.pc (4 * l + j))
    (hn : (σ (.n n0), σ (.n n1)) = digestHalves (d.node l)) :
    ((if d.q.testBit l then [V.n (ch + 4 * l), .n (ch + 4 * l + 1), .n n0, .n n1]
      else [.n n0, .n n1, .n (ch + 4 * l + 2), .n (ch + 4 * l + 3)]).map σ) =
      [d.pc (4 * l), d.pc (4 * l + 1), d.pc (4 * l + 2), d.pc (4 * l + 3)] := by
  obtain ⟨w0, w1⟩ := d.pc_walk l
  have e0 := congrArg Prod.fst hn
  have e1 := congrArg Prod.snd hn
  simp only at e0 e1
  have c0 := hc 0 (by omega); have c1 := hc 1 (by omega); have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega)
  simp only [Nat.add_zero] at c0
  cases hb : d.q.testBit l
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at w0 w1 ⊢
    simp [c2, c3, e0, e1, w0, w1]
  · simp only [hb, ↓reduceIte] at w0 w1 ⊢
    simp [c0, c1, e0, e1, ← w0, ← w1]

/-- The step's permutation holds at the honest values. -/
theorem step_keccak {l K : ℕ} {ins : List V} (hins : ins.map σ = d.levelIns l)
    (hout : ∀ c < 13, σ (.n (K + 1 + c)) = d.stepV l (1 + c)) :
    (Atom.keccak ins ((List.range 13).map fun c ↦ .n (K + 1 + c)) false false).Holds rd σ := by
  have hl : ins.length = 13 := by
    have := congrArg List.length hins; simpa [levelIns] using this
  refine ⟨hl, by simp, ?_, fun c => ?_⟩
  · rw [hins]
    intro c
    fin_cases c <;> simp [cells13, levelIns] <;> first | exact d.pc_canonical _ | exact canonical_word _ _
  · rw [hins, cells13_outs, hout _ c.isLt, stepV]
    simp only [show 1 + c.val ≠ 0 by omega, ↓reduceIte, show 1 + c.val - 1 = c.val by omega,
      fin13_ofNat c.isLt]
    rfl

variable {bp : V}

/-- The honest valuation on a query's values. -/
abbrev Hv (d : QD) (σ : Val) : Prop := ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i

theorem armOff_bound {w v r o : ℕ} (hv : v < 2 ^ w) (hr : r < w) (ho : o < 14) :
    armOff w v + 14 * r + o < 4 + 14 * w * 2 ^ w ∧ 2 ≤ armOff w v + 14 * r + o ∧
      armOff w v + 14 * r + o ≠ 2 + 14 * w ∧ armOff w v + 14 * r + o ≠ 3 + 14 * w := by
  unfold armOff
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  split
  · have : 14 * w ≤ 14 * w * 2 ^ w := Nat.le_mul_of_pos_right _ h1
    omega
  · have hm : 14 * w * v + 14 * w ≤ 14 * w * 2 ^ w := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hv
    have hm2 : 14 * w ≤ 14 * w * v := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem oqArmK_eq (s : Oq) (ch i a : ℕ) : oqArmK s ch i a = oqWk s ch i + armOff (oqWw s i) a := by
  unfold oqArmK armOff; split
  · rfl
  · rw [Nat.add_assoc]

/-- The honest values of window `i`'s taken arm: its steps. -/
theorem arm_val (hv : Hv d σ) {i r o : ℕ} (hi : i < oqNpw d.s) (hr : r < oqWw d.s i) (ho : o < 14) :
    σ (.n (oqArmK d.s d.ch i (d.wv i) + 14 * r + o)) = d.stepV (6 * i + r) o := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hvl : d.wv i < 2 ^ oqWw d.s i := (qwVal_path hi d.q).1
  obtain ⟨b1, b2, b3, b4⟩ := armOff_bound (o := o) hvl hr ho
  have hw := d.win_le_Cq hi
  have hW := oqWk_mono (s := d.s) (ch := d.ch) (Nat.zero_le i)
  simp only [oqWk] at hW
  rw [oqArmK_eq, show oqWk d.s d.ch i + armOff (oqWw d.s i) (d.wv i) + 14 * r + o =
      oqWk d.s d.ch i + (armOff (oqWw d.s i) (d.wv i) + 14 * r + o) by omega,
    hv _ (by omega) (by unfold winSz at hw; omega), val_win d hi (by unfold winSz; omega), winV]
  simp only [show armOff (oqWw d.s i) (d.wv i) + 14 * r + o ≠ 0 by omega,
    show armOff (oqWw d.s i) (d.wv i) + 14 * r + o ≠ 1 by omega, b3, b4, ↓reduceIte,
    show armOff (oqWw d.s i) (d.wv i) ≤ armOff (oqWw d.s i) (d.wv i) + 14 * r + o by omega,
    show armOff (oqWw d.s i) (d.wv i) + 14 * r + o < armOff (oqWw d.s i) (d.wv i) + 14 * oqWw d.s i
      by omega, and_self]
  rw [show (armOff (oqWw d.s i) (d.wv i) + 14 * r + o - armOff (oqWw d.s i) (d.wv i)) / 14 = r by
      omega,
    show (armOff (oqWw d.s i) (d.wv i) + 14 * r + o - armOff (oqWw d.s i) (d.wv i)) % 14 = o by
      omega]

/-- The window's targets hold the node after it. -/
theorem target_val (hv : Hv d σ) {i c : ℕ} (hi : i < oqNpw d.s) (hc : c < 2) :
    σ (.n (oqWT d.s d.ch i + c)) =
      if c = 0 then (digestHalves (d.node (6 * i + oqWw d.s i))).1
      else (digestHalves (d.node (6 * i + oqWw d.s i))).2 := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hw := d.win_le_Cq hi
  have hW := oqWk_mono (s := d.s) (ch := d.ch) (Nat.zero_le i)
  simp only [oqWk] at hW
  have h1 : 1 ≤ 2 ^ oqWw d.s i := Nat.one_le_two_pow
  have hm : 14 * oqWw d.s i ≤ 14 * oqWw d.s i * 2 ^ oqWw d.s i := Nat.le_mul_of_pos_right _ h1
  unfold winSz at hw
  rw [oqWT, show oqWk d.s d.ch i + 2 + 14 * oqWw d.s i + c = oqWk d.s d.ch i + (2 + 14 * oqWw d.s i + c)
    by omega, hv _ (by omega) (by omega), val_win d hi (by unfold winSz; omega), winV]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  all_goals split_ifs <;> first | rfl | (exfalso; omega)

/-- The node window `i` starts from: the leaf's digest, then the previous window's targets. -/
theorem nd_val (hs : d.s.RowShape) (hrow : d.row.length = d.s.R) (hv : Hv d σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    {i : ℕ} (hi : i ≤ oqNpw d.s) :
    (σ (.n (oqNd d.s d.kL d.ch i 0)), σ (.n (oqNd d.s d.kL d.ch i 1))) =
      digestHalves (d.node (min (6 * i) d.s.pd)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have hz' : ∀ i < 4, σ (.n (d.prV + 1 + i)) = 0 := fun i hi => by rw [hz i hi, word_zero]
    have hnc : d.s.ncells = d.s.R / 2 := rfl
    have hleaf := oqLeaf_sound (rd := fun _ => none) hs (d.oqLeaf_complete hs hv hpad hz) hpad hz'
      (row := d.row) (by rw [hrow, hnc]; rcases shape_nums hs with h | h <;> omega) (fun j hj => by
        rw [show oqPk d.b d.s.R j = d.b + d.s.R + 3 * j + 2 by simp [oqPk],
          hv _ (by have := k1_eq d; omega) (by have := k1_eq d; omega),
          val_pack d (by omega) (by omega)]
        exact d.pk_eq j)
    simp only [oqNd, ↓reduceIte, Nat.mul_zero, Nat.zero_min]
    rw [hleaf]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have t0 := d.target_val hv (i := j) (c := 0) (by omega) (by omega)
    have t1 := d.target_val hv (i := j) (c := 1) (by omega) (by omega)
    simp only [↓reduceIte, one_ne_zero, Nat.add_zero] at t0 t1
    have hm : 6 * j + oqWw d.s j = min (6 * (j + 1)) d.s.pd := by
      unfold oqWw; unfold oqNpw at hi ⊢; split <;> omega
    simp only [oqNd, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [t0, t1, hm]

/-- **The taken arm's nodes are the climb's.** -/
theorem arm_nodes (hsl : d.sibs.length = d.s.pd) (hv : Hv d σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    {i : ℕ} (hi : i < oqNpw d.s)
    (h0 : (σ (.n (oqNd d.s d.kL d.ch i 0)), σ (.n (oqNd d.s d.kL d.ch i 1))) =
      digestHalves (d.node (6 * i))) :
    ∀ r ≤ oqWw d.s i, (σ (.n (oqArmN d.s d.kL d.ch i (d.wv i) r 0)),
      σ (.n (oqArmN d.s d.kL d.ch i (d.wv i) r 1))) = digestHalves (d.node (6 * i + r)) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hz' : ∀ i < 4, σ (.n (d.prV + 1 + i)) = 0 := fun i hi => by rw [hz i hi, word_zero]
  intro r hr
  induction r with
  | zero => simpa [oqArmN] using h0
  | succ r ih =>
    have hn := ih (by omega)
    have hl : 6 * i + r < d.s.pd := by
      have hi' := hi; have hr' := hr
      unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
    set K := oqArmK d.s d.ch i (d.wv i) + 14 * r with hK
    have hk0 : σ (.n K) = word (2 ^ 63) 0 0 := by
      rw [hK, show oqArmK d.s d.ch i (d.wv i) + 14 * r = oqArmK d.s d.ch i (d.wv i) + 14 * r + 0
        from rfl, d.arm_val hv hi (by omega) (by omega), stepV]; rfl
    have hc : ∀ j < 4, σ (.n (d.ch + 4 * (6 * i + r) + j)) = d.pc (4 * (6 * i + r) + j) :=
      fun j hj => by rw [Nat.add_assoc, hv _ (by omega) (by omega), val_pc d (by omega)]
    have hcells := d.step_cells (l := 6 * i + r) hc hn
    have hout : ∀ c < 13, σ (.n (K + 1 + c)) = d.stepV (6 * i + r) (1 + c) := fun c hc => by
      rw [hK, Nat.add_assoc, d.arm_val hv hi (by omega) (by omega)]
    have hbit : (d.wv i).testBit r = d.q.testBit (6 * i + r) := (qwVal_path hi d.q).2 r (by omega)
    have hk := d.step_keccak (rd := fun _ => none) (l := 6 * i + r) (K := K)
      (ins := (if d.q.testBit (6 * i + r) then [V.n (d.ch + 4 * (6 * i + r)),
        .n (d.ch + 4 * (6 * i + r) + 1), .n (oqArmN d.s d.kL d.ch i (d.wv i) r 0),
        .n (oqArmN d.s d.kL d.ch i (d.wv i) r 1)]
        else [.n (oqArmN d.s d.kL d.ch i (d.wv i) r 0), .n (oqArmN d.s d.kL d.ch i (d.wv i) r 1),
          .n (d.ch + 4 * (6 * i + r) + 2), .n (d.ch + 4 * (6 * i + r) + 3)]) ++
        [.n d.prV, .n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3), .n K, .n (d.prV + 1),
          .n (d.prV + 2), .n (d.prV + 3), .n (d.prV + 4)]) (by
      rw [List.map_append, hcells]
      have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
      have z4 := hz 3 (by omega)
      simp only [Nat.add_zero] at z1
      rw [show d.prV + 1 + 1 = d.prV + 2 by omega] at z2
      rw [show d.prV + 1 + 2 = d.prV + 3 by omega] at z3
      rw [show d.prV + 1 + 3 = d.prV + 4 by omega] at z4
      simp [hpad, z1, z2, z3, z4, hk0, levelIns]) hout
    have hpair : HashesPair (d.pc (4 * (6 * i + r))) (d.pc (4 * (6 * i + r) + 1))
        (d.pc (4 * (6 * i + r) + 2)) (d.pc (4 * (6 * i + r) + 3)) (σ (.n (K + 1)))
        (σ (.n (K + 2))) := by
      have e := hcells
      cases hb : d.q.testBit (6 * i + r)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at hk e
        have := oqPair_hash hpad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
      · simp only [hb, ↓reduceIte, List.cons_append, List.nil_append] at hk e
        have := oqPair_hash hpad hz' hk0 hk
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at e
        obtain ⟨e0, e1, e2, e3, -⟩ := e
        rw [e0, e1, e2, e3] at this
        simpa [List.getD_eq_getElem?_getD] using this
    have := d.level_out (l := 6 * i + r) (by omega) hpair
    simp only [oqArmN, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.add_zero]
    rw [← hK, show K + 1 + 1 = K + 2 by omega, this]
    rfl

theorem gen_pow_ofK (v : ℕ) : gen ^ v = ofK (Parameters.addressOfIndex v) := gen_pow_eq_ofK v

/-- **A window holds at the honest values**: its word read, `0x80`, its match taking arm `v`. -/
theorem oqWin_complete (hs : d.s.RowShape) (hpd : 1 ≤ d.s.pd) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R) {bpv : E} (hbp : σ bp = bpv) (hv : Hv d σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hm : d.MemOk rd bpv) {i : ℕ} (hi : i < oqNpw d.s) :
    BlockOk rd σ (oqWinT d.s bp d.prV d.kL d.ch i) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hw := d.win_le_Cq hi
  have hW := oqWk_mono (s := d.s) (ch := d.ch) (Nat.zero_le i)
  simp only [oqWk] at hW
  unfold winSz at hw
  have s0 : σ (.n (oqWk d.s d.ch i)) = gen ^ d.wv i := by
    rw [show oqWk d.s d.ch i = oqWk d.s d.ch i + 0 from rfl, hv _ (by omega) (by omega),
      val_win d hi (by unfold winSz; omega), winV]; simp
  have s1 : σ (.n (oqWk d.s d.ch i + 1)) = word (2 ^ 63) 0 0 := by
    rw [hv _ (by omega) (by omega), val_win d hi (by unfold winSz; omega), winV]; simp
  have hn0 : (σ (.n (oqNd d.s d.kL d.ch i 0)), σ (.n (oqNd d.s d.kL d.ch i 1))) =
      digestHalves (d.node (6 * i)) := by
    rw [d.nd_val hs hrow hv hpad hz (le_of_lt hi)]
    congr 2; unfold oqNpw at hi; omega
  have hnodes := d.arm_nodes hsl hv hpad hz hi hn0
  have hvl : d.wv i < 2 ^ oqWw d.s i := (qwVal_path hi d.q).1
  intro st hst
  simp only [oqWinT, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [s0, hbp]; exact hm.wins i (by rw [qwN_eq]; omega)
  · exact s1
  · refine ⟨d.wv i, by simpa using hvl, by rw [s0, gen_pow_ofK], fun a ha => ?_⟩
    simp only [List.getElem_map, List.getElem_range] at ha
    simp only [oqArmT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with ⟨_, ⟨r, hr, rfl⟩, ha⟩ | rfl | rfl
    · simp only [oqStepT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · show σ _ = _
        rw [show oqArmK d.s d.ch i (d.wv i) + 14 * r = oqArmK d.s d.ch i (d.wv i) + 14 * r + 0
          from rfl, d.arm_val hv hi hr (by omega), stepV]; rfl
      · have hn := hnodes r (by omega)
        have hl : 6 * i + r < d.s.pd := by
          have hi' := hi; have hr' := hr
          unfold oqWw oqNpw at hr'; unfold oqNpw at hi'; split at hr' <;> omega
        have hc : ∀ j < 4, σ (.n (d.ch + 4 * (6 * i + r) + j)) = d.pc (4 * (6 * i + r) + j) :=
          fun j hj => by rw [Nat.add_assoc, hv _ (by omega) (by omega), val_pc d (by omega)]
        have hb : (d.wv i).testBit r = d.q.testBit (6 * i + r) := (qwVal_path hi d.q).2 r hr
        rw [hb]
        exact d.step_keccak (l := 6 * i + r) (by
          rw [List.map_append, d.step_cells hc hn]
          have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
          have z4 := hz 3 (by omega)
          simp only [Nat.add_zero] at z1
          rw [show d.prV + 1 + 1 = d.prV + 2 by omega] at z2
          rw [show d.prV + 1 + 2 = d.prV + 3 by omega] at z3
          rw [show d.prV + 1 + 3 = d.prV + 4 by omega] at z4
          have hk0 : σ (.n (oqArmK d.s d.ch i (d.wv i) + 14 * r)) = word (2 ^ 63) 0 0 := by
            rw [show oqArmK d.s d.ch i (d.wv i) + 14 * r = oqArmK d.s d.ch i (d.wv i) + 14 * r + 0
              from rfl, d.arm_val hv hi hr (by omega), stepV]; rfl
          simp [hpad, z1, z2, z3, z4, hk0, levelIns]) (fun c hc => by
            rw [Nat.add_assoc, d.arm_val hv hi hr (by omega)])
    · show σ _ = σ _
      have t := d.target_val hv (c := 0) hi (by omega)
      rw [Nat.add_zero] at t
      rw [t, show σ (.n (oqArmN d.s d.kL d.ch i (d.wv i) (oqWw d.s i) 0)) =
        (digestHalves (d.node (6 * i + oqWw d.s i))).1 from
        congrArg Prod.fst (hnodes _ le_rfl)]
      rfl
    · show σ _ = σ _
      have t := d.target_val hv (c := 1) hi (by omega)
      rw [t, show σ (.n (oqArmN d.s d.kL d.ch i (d.wv i) (oqWw d.s i) 1)) =
        (digestHalves (d.node (6 * i + oqWw d.s i))).2 from
        congrArg Prod.snd (hnodes _ le_rfl)]
      rfl

/-- **The path holds at the honest values.** -/
theorem oqPath_complete (hs : d.s.RowShape) (hpd : 1 ≤ d.s.pd) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R) {bpv : E} (hbp : σ bp = bpv) (hv : Hv d σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hm : d.MemOk rd bpv) :
    BlockOk rd σ (oqPathT d.s bp d.prV d.kL d.ch) := by
  intro st hst
  simp only [oqPathT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range] at hst
  rcases hst with rfl | ⟨_, ⟨i, hi, rfl⟩, hst⟩
  · trivial
  · exact d.oqWin_complete hs hpd hsl hrow hbp hv hpad hz hm hi _ hst

/-! ## The cap leaf -/

theorem climbNode_length (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs sibs.length = climbD leaf q sibs := by
  simp [climbNode]

/-- **The cap leaf holds at the honest values.** -/
theorem oqCap_complete (hs : d.s.RowShape) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R) (hcd : 1 ≤ d.s.cd) (hq : d.q < 2 ^ (d.s.pd + d.s.cd))
    {cap flags : V} {bpv : E} (hbp : σ bp = bpv) (hv : Hv d σ)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hm : d.MemOk rd bpv) (hcap : σ cap = d.capv) (hflags : σ flags = d.flagsv) :
    ∀ a, Stmt.atom a ∈ oqCapT d.s bp cap flags d.kL d.ch → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hCq : oqCq d.s d.ch = d.Cq := rfl
  have t : ∀ o < 9, σ (.n (d.Cq + o)) = d.capV o := fun o ho => by
    rw [hv _ (by omega) (by omega), val_cap d]
  have t0 : σ (.n d.Cq) = d.wbV := by rw [show d.Cq = d.Cq + 0 from rfl, t 0 (by omega)]; rfl
  have t1 : σ (.n (d.Cq + 1)) = d.qV := by rw [t 1 (by omega)]; rfl
  have t2 : σ (.n (d.Cq + 2)) = d.flagsv * d.qV := by rw [t 2 (by omega)]; rfl
  have t3 : σ (.n (d.Cq + 3)) = word 1 0 0 := by rw [t 3 (by omega)]; rfl
  have t4 : σ (.n (d.Cq + 4)) = d.qV * d.qV := by rw [t 4 (by omega)]; rfl
  have t5 : σ (.n (d.Cq + 5)) = d.capv * (d.qV * d.qV) := by rw [t 5 (by omega)]; rfl
  have t6 : σ (.n (d.Cq + 6)) = d.capv * (d.qV * d.qV) * (d.qV * d.qV) := by rw [t 6 (by omega)]; rfl
  have t7 : σ (.n (d.Cq + 7)) = d.wbV * d.wbV := by rw [t 7 (by omega)]; rfl
  have t8 : σ (.n (d.Cq + 8)) = d.capv * (d.qV * d.qV) * (d.qV * d.qV) * (d.wbV * d.wbV) := by
    rw [t 8 (by omega)]; rfl
  have hN : oqNpw d.s + 1 < qwN (d.s.pd + d.s.cd) d.s.cd := by rw [qwN_eq]; omega
  have hwb : gen ^ d.wv (oqNpw d.s) = d.wbV := by
    rw [wbV, wv, oqNpw_eq, qwVal_capBit]
  have hqv : gen ^ d.wv (oqNpw d.s + 1) = d.qV := by
    rw [qV, wv, oqNpw_eq, qwVal_capIdx hcd hq]
  set Q := d.q / 2 ^ (d.s.pd + 1) with hQdef
  set bb : ℕ := if d.q.testBit d.s.pd then 1 else 0 with hbdef
  have h8 : d.capv * (d.qV * d.qV) * (d.qV * d.qV) * (d.wbV * d.wbV) =
      d.capv * gen ^ (4 * Q + 2 * bb) := by
    rw [qV, wbV, ← hQdef, ← hbdef, ← pow_add, ← pow_add, mul_assoc, mul_assoc,
      ← pow_add, ← pow_add]
    congr 2; ring
  have hsplit : d.q / 2 ^ d.s.pd = 2 * Q + bb := by
    rw [hQdef, hbdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : d.q / 2 ^ d.s.pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  have hnd := d.nd_val hs hrow hv hpad hz (i := oqNpw d.s) le_rfl
  have hmin : min (6 * oqNpw d.s) d.s.pd = d.s.pd := by unfold oqNpw; omega
  rw [hmin, node, ← hsl, climbNode_length] at hnd
  intro a ha
  simp only [oqCapT, hCq, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show LoadHolds _ _ _ _
    rw [t0, hbp, ← hwb]; exact hm.wins _ (by omega)
  · show LoadHolds _ _ _ _
    rw [t1, hbp, ← hqv]; exact hm.wins _ hN
  · show σ _ = σ _ * σ _
    rw [t2, hflags, t1]
  · exact t3
  · show LoadHolds _ _ _ _
    rw [t3, t2, word_one, qV, loadHolds_mul_gen_pow, add_comm]
    exact hm.flag
  · show σ _ = σ _ * σ _
    rw [t4, t1]
  · show σ _ = σ _ * σ _
    rw [t5, hcap, t4]
  · show σ _ = σ _ * σ _
    rw [t6, t5, t4]
  · show σ _ = σ _ * σ _
    rw [t7, t0]
  · show σ _ = σ _ * σ _
    rw [t8, t6, t7]
  · show LoadHolds _ _ _ _
    rw [t8, h8, show σ (.n (oqNd d.s d.kL d.ch (oqNpw d.s) 0)) =
      (digestHalves (climbD d.leaf d.q d.sibs)).1 from congrArg Prod.fst hnd, loadHolds_mul_gen_pow]
    have := hm.cap0
    rw [hsplit, show 2 * (2 ^ d.s.cd + (2 * Q + bb)) = 4 * Q + 2 * bb + 2 ^ (d.s.cd + 1) by
      rw [pow_succ]; ring] at this
    exact this
  · show LoadHolds _ _ _ _
    rw [t8, h8, show σ (.n (oqNd d.s d.kL d.ch (oqNpw d.s) 1)) =
      (digestHalves (climbD d.leaf d.q d.sibs)).2 from congrArg Prod.snd hnd, loadHolds_mul_gen_pow]
    have := hm.cap1
    rw [hsplit, show 2 * (2 ^ d.s.cd + (2 * Q + bb)) + 1 = 4 * Q + 2 * bb + (2 ^ (d.s.cd + 1) + 1)
      by rw [pow_succ]; ring] at this
    exact this

end QD

end
end LeanVM.Guest.B1
