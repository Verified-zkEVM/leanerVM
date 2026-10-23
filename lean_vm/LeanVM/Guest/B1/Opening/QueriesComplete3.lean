/-
  LeanVM.Guest.B1.Opening.QueriesComplete3

  The completeness of a query's Merkle path and cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# A query's path and cap leaf, completeness

The honest nodes are the climb's (`node_eq`: the leaf's digest, then each level's pair hash,
`climbD_snoc`); with the memory holding the path's frame run, the nodes stored at their bits'
sides, the cap leaf and the parent's flag (what `QueryOpens` says), every atom of the path
(`oqPath_complete`) and of the cap leaf (`oqCap_complete`) holds at the honest values.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-! ## The values of the path and of the cap -/

theorem capQ_eq : ∀ j, j < 7 → d.capQ j = gen ^ (d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1))
  | 0, _ => by
    rw [capQ, QD.bit, word_capFac (by decide), word_one, bit_factor,
      Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    by_cases h : d.q / 2 ^ (d.s.pd + 1) % 2 = 1 <;> simp [h]
    omega
  | j + 1, hj => by
    rw [capQ, QD.bit, capQ_eq j (by omega), word_capFac (by omega), word_one,
      bit_factor, ← pow_add,
      show d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1 + 1) = d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1) +
        2 ^ (j + 1) * (d.q / 2 ^ (d.s.pd + 1) / 2 ^ (j + 1) % 2) from Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add,
      show d.s.pd + 2 + j = d.s.pd + 1 + (j + 1) by omega]
    congr 1
    by_cases h : d.q / 2 ^ (d.s.pd + 1 + (j + 1)) % 2 = 1
    · simp [h]
    · simp [show d.q / 2 ^ (d.s.pd + 1 + (j + 1)) % 2 = 0 by omega]

theorem pc_canonical (k : ℕ) : IsCanonical128 (d.pc k) := by
  unfold pc pathCell
  dsimp only
  split <;> exact canonical_ofLimbs _ _

/-- A level's pair hash is the climb's step. -/
theorem level_out {l : ℕ} (hl : l < d.sibs.length) {o0 o1 : E}
    (h : HashesPair (d.pc (4 * l)) (d.pc (4 * l + 1)) (d.pc (4 * l + 2)) (d.pc (4 * l + 3)) o0 o1) :
    (o0, o1) = digestScalars (climbNode d.leaf d.q d.sibs (l + 1)) := by
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
    have c0 : d.pc (4 * l) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestScalars (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestScalars (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']
  · have hb' : d.q / 2 ^ l % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simp at hb; omega
    have c0 : d.pc (4 * l) = (digestScalars (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestScalars (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']


/-! ## The path -/

/-- What the memory holds of an honest query's path and cap leaf (`QueryOpens`). -/
structure MemOk (d : QD) (rd : Reader) : Prop where
  ppK : IsInK d.pp
  frame : ∀ k < 4 * d.s.pd, ∀ x, rd (d.pp.limb 0 * Parameters.gpow k) = some x → x = d.pc k
  nodes : ∀ l < d.s.pd,
    LoadHolds rd (d.pp * gen ^ (if d.q.testBit l then 2 else 0)) (4 * l)
      (digestScalars (climbNode d.leaf d.q d.sibs l)).1 ∧
    LoadHolds rd (d.pp * gen ^ (if d.q.testBit l then 2 else 0)) (4 * l + 1)
      (digestScalars (climbNode d.leaf d.q d.sibs l)).2
  cap0 : LoadHolds rd d.capv (2 * (2 ^ d.s.cd + d.q / 2 ^ d.s.pd))
    (digestScalars (climbD d.leaf d.q d.sibs)).1
  cap1 : LoadHolds rd d.capv (2 * (2 ^ d.s.cd + d.q / 2 ^ d.s.pd) + 1)
    (digestScalars (climbD d.leaf d.q d.sibs)).2
  flag : LoadHolds rd d.flagsv (2 ^ (d.s.cd - 1) + d.q / 2 ^ (d.s.pd + 1)) 1

theorem mem_oqPathT_level' {s : Oq} {bp : V} {pr kL ch l : ℕ} (hl : l < s.pd) {a : Atom}
    (ha : Stmt.atom a ∈ oqLevelT s bp pr kL ch l) : Stmt.atom a ∈ oqPathT s bp pr kL ch :=
  mem_oqPathT_level hl ha

/-- The level's permutation holds at the honest values. -/
theorem level_keccak (hpd : 4 * d.s.pd ≤ 80)
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    {l : ℕ} (hl : l < d.s.pd) :
    (Atom.keccak [.n (d.ch + 4 * l), .n (d.ch + 4 * l + 1), .n (d.ch + 4 * l + 2),
      .n (d.ch + 4 * l + 3), .n d.prV, .n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3),
      .n (oqL0 d.ch + 17 * l + 3), .n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3), .n (d.prV + 4)]
      ((List.range 13).map fun c ↦ .n (oqL0 d.ch + 17 * l + 4 + c)) false false).Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have sP : ∀ o < 83, σ (.n (d.ch + o)) = d.preV o := fun o ho => by
    rw [hv _ (by omega) (by omega), val_pre d ho]
  have sL : ∀ o < 17, σ (.n (oqL0 d.ch + 17 * l + o)) = d.levelV l o := fun o ho => by
    rw [show oqL0 d.ch + 17 * l + o = d.ch + 83 + 17 * l + o by simp [oqL0],
      hv _ (by omega) (by omega), val_level d hl ho]
  have pc' : ∀ t < 4, σ (.n (d.ch + 4 * l + t)) = d.pc (4 * l + t) := fun t ht => by
    rw [Nat.add_assoc, sP _ (by omega), preV]; simp [show 4 * l + t < 4 * d.s.pd by omega]
  have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
  have z4 := hz 3 (by omega)
  simp only [Nat.add_zero] at z1
  rw [show d.prV + 1 + 1 = d.prV + 2 by omega] at z2
  rw [show d.prV + 1 + 2 = d.prV + 3 by omega] at z3
  rw [show d.prV + 1 + 3 = d.prV + 4 by omega] at z4
  have h63 : σ (.n (oqL0 d.ch + 17 * l + 3)) = word (2 ^ 63) 0 0 := by rw [sL 3 (by omega)]; rfl
  have eI : ([.n (d.ch + 4 * l), .n (d.ch + 4 * l + 1), .n (d.ch + 4 * l + 2),
      .n (d.ch + 4 * l + 3), .n d.prV, .n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3),
      .n (oqL0 d.ch + 17 * l + 3), .n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3),
      .n (d.prV + 4)] : List V).map σ = d.levelIns l := by
    have q0 := pc' 0 (by omega); have q1 := pc' 1 (by omega); have q2 := pc' 2 (by omega)
    have q3 := pc' 3 (by omega)
    simp only [Nat.add_zero] at q0
    simp only [List.map_cons, List.map_nil, q0, q1, q2, q3, hpad, z1, z2, z3, z4, h63, levelIns]
  refine ⟨by simp, by simp, ?_, fun c => ?_⟩
  · rw [eI]
    intro c
    fin_cases c <;> simp [cells13, levelIns] <;> first | exact d.pc_canonical _ | exact canonical_word _ _
  · rw [eI, cells13_outs, show oqL0 d.ch + 17 * l + 4 + c.val = oqL0 d.ch + 17 * l + (4 + c.val) by
      omega, sL _ (by omega), levelV]
    simp only [show 4 + c.val ≠ 0 by omega, show 4 + c.val ≠ 1 by omega, show 4 + c.val ≠ 2 by omega,
      show 4 + c.val ≠ 3 by omega, ↓reduceIte, show 4 + c.val - 4 = c.val by omega,
      fin13_ofNat c.isLt]
    rfl

/-- **The honest nodes are the climb's.** -/
theorem nodes_eq (hs : d.s.RowShape) (hpd : 4 * d.s.pd ≤ 80) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R)
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0) :
    ∀ l ≤ d.s.pd, (σ (.n (oqNode d.s d.kL d.ch l 0)), σ (.n (oqNode d.s d.kL d.ch l 1))) =
      digestScalars (climbNode d.leaf d.q d.sibs l) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hz' : ∀ i < 4, σ (.n (d.prV + 1 + i)) = 0 := fun i hi => by rw [hz i hi, word_zero]
  intro l hl
  induction l with
  | zero =>
    have hnc : d.s.ncells = d.s.R / 2 := rfl
    have hleaf := oqLeaf_sound (rd := fun _ => none) hs (d.oqLeaf_complete hs hv hpad hz) hpad hz'
      (row := d.row) (by rw [hrow, hnc]; rcases shape_nums hs with h | h <;> omega) (fun j hj => by
        rw [show oqPk d.b d.s.R j = d.b + d.s.R + 3 * j + 2 by simp [oqPk],
          hv _ (by have := k1_eq d; omega) (by have := k1_eq d; omega),
          val_pack d (by omega) (by omega)]
        exact d.pk_eq j)
    simp only [oqNode, ↓reduceIte]
    rw [hleaf]
    rfl
  | succ l ih =>
    have hk := d.level_keccak (rd := fun _ => none) hpd hv hpad hz (l := l) (by omega)
    have hp := oqPair_hash hpad hz' (by
      rw [show oqL0 d.ch + 17 * l + 3 = d.ch + 83 + 17 * l + 3 by simp [oqL0],
        hv _ (by omega) (by omega), val_level d (by omega) (by omega)]; rfl) hk
    have pc' : ∀ t < 4, σ (.n (d.ch + 4 * l + t)) = d.pc (4 * l + t) := fun t ht => by
      rw [Nat.add_assoc, hv _ (by omega) (by omega), val_pre d (by omega), preV]
      simp [show 4 * l + t < 4 * d.s.pd by omega]
    have q0 := pc' 0 (by omega); have q1 := pc' 1 (by omega); have q2 := pc' 2 (by omega)
    have q3 := pc' 3 (by omega)
    simp only [Nat.add_zero] at q0
    rw [q0, q1, q2, q3] at hp
    have := d.level_out (l := l) (by omega) hp
    simp only [oqNode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    simpa [List.getD_eq_getElem?_getD] using this

/-- **The path holds at the honest values.** -/
theorem oqPath_complete (hs : d.s.RowShape) (hpd : 4 * d.s.pd ≤ 80) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R) {bp : V}
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hbits : ∀ l < d.s.pd + d.s.cd, LoadHolds rd (σ bp) l (d.bit l)) (hm : d.MemOk rd)
    (hrd : d.rd = rd) :
    ∀ a, Stmt.atom a ∈ oqPathT d.s bp d.prV d.kL d.ch → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have sP : ∀ o < 83, σ (.n (d.ch + o)) = d.preV o := fun o ho => by
    rw [hv _ (by omega) (by omega), val_pre d ho]
  have hnd := d.nodes_eq hs hpd hsl hrow hv hpad hz
  have spp : σ (.n (d.ch + 4 * d.s.pd)) = d.pp := by
    rw [sP _ (by omega), preV]; simp
  have s5 : σ (.n (d.ch + 81)) = word 5 0 0 := by
    rw [sP _ (by omega), preV]; simp [show ¬ 81 < 4 * d.s.pd by omega, show 81 ≠ 4 * d.s.pd by omega]
  have s82 : σ (.n (d.ch + 82)) = d.pp * word 5 0 0 := by
    rw [sP _ (by omega), preV]; simp [show ¬ 82 < 4 * d.s.pd by omega, show 82 ≠ 4 * d.s.pd by omega]
  intro a ha
  simp only [oqPathT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range, Stmt.atom.injEq] at ha
  rcases ha with (rfl | rfl | rfl | rfl) | ⟨_, ⟨l, hl, rfl⟩, ha⟩
  · trivial
  · refine ⟨by rw [spp]; exact hm.ppK, fun k hk w hw => ?_⟩
    simp only [List.length_append, List.length_map, List.length_range] at hk
    rw [spp] at hw
    by_cases hk' : k < 4 * d.s.pd
    · rw [List.getElem_append_left (by simpa using hk')]
      simp only [List.getElem_map, List.getElem_range]
      rw [sP _ (by omega), preV]
      simp only [hk', ↓reduceIte]
      exact hm.frame k hk' w hw
    · rw [List.getElem_append_right (by simpa using hk')]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [show d.ch + 4 * d.s.pd + 1 + (k - 4 * d.s.pd) = d.ch + (k + 1) by omega, sP _ (by omega),
        preV]
      simp only [show ¬ k + 1 < 4 * d.s.pd by omega, show k + 1 ≠ 4 * d.s.pd by omega,
        show k + 1 < 81 by omega, ↓reduceIte, Nat.add_sub_cancel]
      rw [hrd, hw]; rfl
  · exact s5
  · show σ _ = σ _ * σ _
    rw [s82, spp, s5]
  · set L := oqL0 d.ch + 17 * l with hL
    have sL : ∀ o < 17, σ (.n (L + o)) = d.levelV l o := fun o ho => by
      rw [hL, show oqL0 d.ch + 17 * l + o = d.ch + 83 + 17 * l + o by simp [oqL0],
        hv _ (by omega) (by omega), val_level d hl ho]
    have s0 := sL 0 (by omega); have s1 := sL 1 (by omega); have s2 := sL 2 (by omega)
    have s3 := sL 3 (by omega)
    simp only [Nat.add_zero, levelV, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 0 by decide,
      show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide] at s0 s1 s2 s3
    have hsel : σ (.n (L + 2)) = d.pp * gen ^ (if d.q.testBit l then 2 else 0) := by
      rw [s2, word_five, QD.bit, sel_eq]
    have nd := hnd l (by omega)
    simp only [oqLevelT, ← hL, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show LoadHolds _ _ _ _
      rw [s0]; exact hbits l (by omega)
    · show σ _ = σ _ * σ _
      rw [s1, s0, s82]
    · show σ _ = σ _ + σ _
      rw [s2, spp, s1]
    · show LoadHolds _ _ _ _
      rw [hsel, show σ (.n (oqNode d.s d.kL d.ch l 0)) = (digestScalars (climbNode d.leaf d.q d.sibs l)).1
        by rw [← nd]]
      exact (hm.nodes l hl).1
    · show LoadHolds _ _ _ _
      rw [hsel, show σ (.n (oqNode d.s d.kL d.ch l 1)) = (digestScalars (climbNode d.leaf d.q d.sibs l)).2
        by rw [← nd]]
      exact (hm.nodes l hl).2
    · exact s3
    · exact d.level_keccak hpd hv hpad hz hl


/-! ## The cap leaf -/

/-- **The cap leaf holds at the honest values.** -/
theorem oqCap_complete (hs : d.s.RowShape) (hpd : 4 * d.s.pd ≤ 80) (hsl : d.sibs.length = d.s.pd)
    (hrow : d.row.length = d.s.R) (hcd : 2 ≤ d.s.cd) (hcd8 : d.s.cd ≤ 8)
    (hq : d.q < 2 ^ (d.s.pd + d.s.cd)) {bp cap flags : V}
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hbits : ∀ l < d.s.pd + d.s.cd, LoadHolds rd (σ bp) l (d.bit l)) (hm : d.MemOk rd)
    (hcap : σ cap = d.capv) (hflags : σ flags = d.flagsv) :
    ∀ a, Stmt.atom a ∈ oqCapT d.s bp cap flags d.kL d.ch → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hCq : oqCq d.s d.ch = d.Cq := rfl
  have sH : ∀ o < 5, σ (.n (d.Cq + o)) = d.capHeadV o := fun o ho => by
    rw [hv _ (by omega) (by omega), val_capHead d ho]
  have sB : ∀ j, 1 ≤ j → j ≤ d.s.cd - 2 → ∀ o < 6,
      σ (.n (d.Cq + 5 + 6 * (j - 1) + o)) = d.capBitV j o := fun j hj1 hj o ho => by
    rw [hv _ (by omega) (by omega), val_capBit d hj1 hj ho]
  have sT : ∀ o < 11, σ (.n (d.z + o)) = d.capTailV o := fun o ho => by
    rw [hv _ (by omega) (by omega), val_capTail d ho]
  have sQ : ∀ j ≤ d.s.cd - 2, σ (.n (oqQ d.s d.ch j)) = d.capQ j := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [show oqQ d.s d.ch 0 = d.Cq + 4 by simp [oqQ, hCq], sH 4 (by omega)]; rfl
    · rw [show oqQ d.s d.ch j = d.Cq + 5 + 6 * (j - 1) + 5 by simp [oqQ, hCq]; omega,
        sB j hpos hj 5 (by omega)]; rfl
  set Q := d.q / 2 ^ (d.s.pd + 1) with hQdef
  have hQlt : Q < 2 ^ (d.s.cd - 1) := by
    rw [hQdef, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc d.q < 2 ^ (d.s.pd + d.s.cd) := hq
      _ = 2 ^ (d.s.cd - 1 + (d.s.pd + 1)) := by congr 1; omega
  have hqv : d.capQ (d.s.cd - 2) = gen ^ Q := by
    rw [capQ_eq d _ (by omega), show d.s.cd - 2 + 1 = d.s.cd - 1 by omega, Nat.mod_eq_of_lt hQlt]
  have hsplit : d.q / 2 ^ d.s.pd = 2 * Q + (if d.q.testBit d.s.pd then 1 else 0) := by
    rw [hQdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : d.q / 2 ^ d.s.pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  have hnd := d.nodes_eq hs hpd hsl hrow hv hpad hz d.s.pd le_rfl
  rw [← hsl, climbNode_length, hsl] at hnd
  have t := fun o (ho : o < 11) => sT o ho
  have hz10 : σ (.n (d.z + 10)) = d.capv * gen ^ (4 * Q + (if d.q.testBit d.s.pd then 2 else 0)) := by
    rw [t 10 (by omega)]
    simp only [capTailV, List.getD_cons_succ, List.getD_cons_zero]
    rw [hqv, word_one, word_five, QD.bit, bit_factor, ← pow_add, mul_assoc, ← pow_add, mul_assoc,
      ← pow_add]
    congr 2; ring
  intro a ha
  simp only [oqCapT, hCq, ← z_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatten, List.mem_map, List.mem_range, Stmt.atom.injEq] at ha
  rcases ha with ((rfl | rfl | rfl | rfl | rfl) | ⟨_, ⟨j, hj, rfl⟩, ha⟩) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · show σ _ = _
    have := sH 0 (by omega); simpa [capHeadV] using this
  · show LoadHolds _ _ _ _
    have := sH 1 (by omega); simp only [capHeadV, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact hbits _ (by omega)
  · show σ _ = _
    have := sH 2 (by omega); simpa [capHeadV] using this
  · show σ _ = σ _ * σ _
    rw [sH 3 (by omega), sH 1 (by omega), sH 2 (by omega)]; rfl
  · show σ _ = σ _ + σ _
    rw [sH 4 (by omega), show d.Cq = d.Cq + 0 from rfl, sH 0 (by omega), sH 3 (by omega)]; rfl
  · -- a cap bit
    have hj1 : 1 ≤ j + 1 := by omega
    have hjj : j + 1 ≤ d.s.cd - 2 := by omega
    have b := fun o (ho : o < 6) => sB (j + 1) hj1 hjj o ho
    simp only [oqCapBitT, hCq, Nat.add_sub_cancel, List.mem_cons, List.not_mem_nil, or_false,
      Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · show σ _ = _
      have := b 0 (by omega); simpa [capBitV] using this
    · show LoadHolds _ _ _ _
      have := b 1 (by omega); simp only [capBitV, List.getD_cons_succ, List.getD_cons_zero] at this
      rw [Nat.add_sub_cancel] at this
      rw [this]; exact hbits _ (by omega)
    · show σ _ = _
      have := b 2 (by omega); simpa [capBitV] using this
    · show σ _ = σ _ * σ _
      have b3 := b 3 (by omega); have b1 := b 1 (by omega); have b2 := b 2 (by omega)
      simp only [Nat.add_sub_cancel] at b3 b1 b2
      rw [b3, b1, b2]; rfl
    · show σ _ = σ _ + σ _
      have b4 := b 4 (by omega); have b0 := b 0 (by omega); have b3 := b 3 (by omega)
      simp only [Nat.add_sub_cancel, Nat.add_zero] at b4 b0 b3
      rw [b4, b0, b3]; rfl
    · show σ _ = σ _ * σ _
      have b5 := b 5 (by omega); have b4 := b 4 (by omega)
      simp only [Nat.add_sub_cancel] at b5 b4
      rw [b5, b4, sQ j (by omega)]
      simp [capBitV, capQ, show d.s.pd + 2 + j = d.s.pd + 1 + (j + 1) by omega]
  · show σ _ = σ _ * σ _
    rw [show d.z = d.z + 0 from rfl, t 0 (by omega), hflags, sQ _ le_rfl]; rfl
  · show σ _ = _
    have := t 1 (by omega); simpa [capTailV] using this
  · show LoadHolds _ _ _ _
    rw [t 1 (by omega), show d.z = d.z + 0 from rfl, t 0 (by omega)]
    simp only [capTailV, List.getD_cons_succ, List.getD_cons_zero, hqv, word_one]
    rw [loadHolds_mul_gen_pow, add_comm]
    exact hm.flag
  · show σ _ = σ _ * σ _
    rw [t 2 (by omega), sQ _ le_rfl]; rfl
  · show σ _ = σ _ * σ _
    rw [t 3 (by omega), hcap, t 2 (by omega)]; rfl
  · show σ _ = σ _ * σ _
    rw [t 4 (by omega), t 3 (by omega), t 2 (by omega)]; rfl
  · show σ _ = _
    have := t 5 (by omega); simpa [capTailV] using this
  · show LoadHolds _ _ _ _
    have := t 6 (by omega); simp only [capTailV, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact hbits _ (by omega)
  · show σ _ = _
    have := t 7 (by omega); simpa [capTailV] using this
  · show σ _ = σ _ * σ _
    rw [t 8 (by omega), t 6 (by omega), t 7 (by omega)]; rfl
  · show σ _ = σ _ + σ _
    rw [t 9 (by omega), t 5 (by omega), t 8 (by omega)]; rfl
  · show σ _ = σ _ * σ _
    rw [t 10 (by omega), t 4 (by omega), t 9 (by omega)]; rfl
  · show LoadHolds _ _ _ _
    rw [hz10, show σ (.n (oqNode d.s d.kL d.ch d.s.pd 0)) = (digestScalars (climbD d.leaf d.q d.sibs)).1
      by rw [← hnd], loadHolds_mul_gen_pow]
    have := hm.cap0
    rw [hsplit, show 2 * (2 ^ d.s.cd + (2 * Q + (if d.q.testBit d.s.pd then 1 else 0))) =
      4 * Q + (if d.q.testBit d.s.pd then 2 else 0) + 2 ^ (d.s.cd + 1) by
        rw [pow_succ]; split <;> ring] at this
    exact this
  · show LoadHolds _ _ _ _
    rw [hz10, show σ (.n (oqNode d.s d.kL d.ch d.s.pd 1)) = (digestScalars (climbD d.leaf d.q d.sibs)).2
      by rw [← hnd], loadHolds_mul_gen_pow]
    have := hm.cap1
    rw [hsplit, show 2 * (2 ^ d.s.cd + (2 * Q + (if d.q.testBit d.s.pd then 1 else 0))) + 1 =
      4 * Q + (if d.q.testBit d.s.pd then 2 else 0) + (2 ^ (d.s.cd + 1) + 1) by
        rw [pow_succ]; split <;> ring] at this
    exact this

end QD

end
end LeanVM.Guest.B1
