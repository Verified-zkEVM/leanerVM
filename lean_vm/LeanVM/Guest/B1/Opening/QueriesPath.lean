/-
  LeanVM.Guest.B1.Opening.QueriesPath

  One query's Merkle path below the cap: `verify_merkle_path` climbs the leaf by the hinted
  siblings, the position's bits choosing the sides.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesLeaf
public import LeanVM.Guest.B1.Merkle.Climb

/-!
# A query's Merkle path (`verify_merkle_path`, G:1026-1041)

`oqPair_hash`: one `keccak(a, b, out)` of two two-cell digests (the padding run as its tail and
capacity, `0x80` as its cell `8`) is `HashesPair` (G3's `keccak_one`).

`oqPath_sound`: level `l` stores the running node into the child its bit selects (the frame run
at `pp`, the address `pp·g^(2b)`), then hashes the four children; with the bits those of `q`,
the nodes are `climbNode leaf q sibs l` for the siblings `sibs` the hinted children hold, the
frame run holds `pathCell`, and the last node is `climbD leaf q sibs` (`climb`, V:492).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## One pair -/

/-- **A pair hash** (`keccak(path[4l:4l+2], path[4l+2:4l+4], node)`): 64 bytes, the padding run
`1, 0, 0, 0, 0` as tail and capacity, `0x80 << 56` as cell `8`. -/
theorem oqPair_hash {c0 c1 c2 c3 w : V} {pr : ℕ} {outs : List V}
    (hpad : σ (.n pr) = word 1 0 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hw : σ w = word (2 ^ 63) 0 0)
    (hK : (Atom.keccak [c0, c1, c2, c3, .n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), w,
      .n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)] outs false false).Holds rd σ) :
    HashesPair (σ c0) (σ c1) (σ c2) (σ c3) (σ (outs.getD 0 (.n 0))) (σ (outs.getD 1 (.n 0))) := by
  obtain ⟨-, ho, hKC⟩ := hK
  have z1 := hz 0 (by omega); have z2 := hz 1 (by omega); have z3 := hz 2 (by omega)
  have z4 := hz 3 (by omega)
  simp only [Nat.add_zero] at z1
  rw [show pr + 1 + 1 = pr + 2 by omega] at z2
  rw [show pr + 1 + 2 = pr + 3 by omega] at z3
  rw [show pr + 1 + 3 = pr + 4 by omega] at z4
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have := hKC.1
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [cells13] using this 0
    · simpa [cells13] using this 1
    · simpa [cells13] using this 2
    · simpa [cells13] using this 3
  · have h := (keccak_one (cells := [σ c0, σ c1, σ c2, σ c3]) (len := 64) (by simp) (by decide)
      (getD_cellsBytes_of_le (by simp))
      (fun c hc ↦ by
        fin_cases c <;> simp_all [padCells, xorByte, padRead, rate, byteCell, cells13])
      (fun c hc ↦ by fin_cases c <;> simp_all [cells13]) hKC).2
    rw [List.take_of_length_le (by simp)] at h
    have e0 : cells13 (List.map σ outs) 0 = σ (outs.getD 0 (.n 0)) := by
      simp [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show 0 < outs.length by omega)]
    have e1 : cells13 (List.map σ outs) 1 = σ (outs.getD 1 (.n 0)) := by
      simp [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show 1 < outs.length by omega)]
    rw [e0, e1] at h
    exact h

/-! ## The levels -/

theorem word_five : word 5 0 0 = 1 + gen ^ 2 := by
  rw [word_eOfNat, gen_pow_eq_eOfNat (by decide), ← eOfNat_one, ← eOfNat_xor]
  rfl

/-- The selected child's address: `pp` at bit `0`, `pp·g²` at bit `1`. -/
theorem sel_eq (pp : E) (b : Bool) :
    pp + bitE b * (pp * (1 + gen ^ 2)) = pp * gen ^ (if b then 2 else 0) := by
  cases b
  · simp [bitE]
  · have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    simp only [bitE, ↓reduceIte, one_mul]
    linear_combination pp * h2

theorem mem_oqPathT_level {s : Oq} {bp : V} {pr kL ch l : ℕ} (hl : l < s.pd) {a : Atom}
    (ha : Stmt.atom a ∈ oqLevelT s bp pr kL ch l) : Stmt.atom a ∈ oqPathT s bp pr kL ch := by
  unfold oqPathT
  exact List.mem_append_right _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩, ha⟩)

/-- The frame run of the path: every readable word at `pp·g^k`, `k < 4pd`, is hinted child `k`. -/
theorem oqPath_frame {s : Oq} {bp : V} {pr kL ch : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqPathT s bp pr kL ch → a.Holds rd σ) :
    IsInK (σ (.n (ch + 4 * s.pd))) ∧ ∀ k < 4 * s.pd, ∀ x,
      rd ((σ (.n (ch + 4 * s.pd))).limb 0 * Parameters.gpow k) = some x → x = σ (.n (ch + k)) := by
  have h := hA _ (by simp [oqPathT] : Stmt.atom (.frameAddr (.n (ch + 4 * s.pd))
    (((List.range (4 * s.pd)).map fun j ↦ .n (ch + j)) ++
      ((List.range (80 - 4 * s.pd)).map fun j ↦ .n (ch + 4 * s.pd + 1 + j)))) ∈ _)
  refine ⟨h.1, fun k hk x hx => ?_⟩
  have := h.2 k (by simp; omega) x hx
  rw [this]
  simp [List.getElem_append_left (show k < ((List.range (4 * s.pd)).map fun j ↦ V.n (ch + j)).length
    by simp [hk])]

/-- **One level** (G:1033-1040): with the bit `b` read and the running node `node`, the hinted
children hold the node on the bit's side and a sibling on the other, the next node is their hash
in that order, and the node is stored at `pp·g^(2b)`. -/
theorem oqLevel_sound {s : Oq} {bp : V} {pr kL ch l : ℕ} (hl : l < s.pd)
    (hA : ∀ a, Stmt.atom a ∈ oqPathT s bp pr kL ch → a.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    {b : Bool} (hbit : LoadHolds rd (σ bp) l (bitE b)) {node : Digest}
    (hnode : (σ (.n (oqNode s kL ch l 0)), σ (.n (oqNode s kL ch l 1))) = digestScalars node) :
    ∃ sib : Digest,
      (σ (.n (ch + 4 * l)), σ (.n (ch + 4 * l + 1))) = digestScalars (if b then sib else node) ∧
      (σ (.n (ch + 4 * l + 2)), σ (.n (ch + 4 * l + 3))) = digestScalars (if b then node else sib) ∧
      (σ (.n (oqNode s kL ch (l + 1) 0)), σ (.n (oqNode s kL ch (l + 1) 1))) =
        digestScalars (if b then hashPair sib node else hashPair node sib) ∧
      LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if b then 2 else 0)) (4 * l)
        (σ (.n (oqNode s kL ch l 0))) ∧
      LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if b then 2 else 0)) (4 * l + 1)
        (σ (.n (oqNode s kL ch l 1))) := by
  have mem := fun a (ha : Stmt.atom a ∈ oqLevelT s bp pr kL ch l) => hA a (mem_oqPathT_level hl ha)
  set L := oqL0 ch + 17 * l with hL
  have a0 := mem _ (by simp [oqLevelT, ← hL] : Stmt.atom (.load (.n L) bp l) ∈ _)
  have a1 := mem _ (by simp [oqLevelT, ← hL] :
    Stmt.atom (.mul (.n (L + 1)) (.n L) (.n (ch + 82))) ∈ _)
  have a2 := mem _ (by simp [oqLevelT, ← hL] :
    Stmt.atom (.add (.n (L + 2)) (.n (ch + 4 * s.pd)) (.n (L + 1))) ∈ _)
  have a3 := mem _ (by simp [oqLevelT, ← hL] :
    Stmt.atom (.load (.n (oqNode s kL ch l 0)) (.n (L + 2)) (4 * l)) ∈ _)
  have a4 := mem _ (by simp [oqLevelT, ← hL] :
    Stmt.atom (.load (.n (oqNode s kL ch l 1)) (.n (L + 2)) (4 * l + 1)) ∈ _)
  have a5 := mem _ (by simp [oqLevelT, ← hL] : Stmt.atom (.const (.n (L + 3)) (word (2 ^ 63) 0 0)) ∈ _)
  have a6 := mem _ (by simp [oqLevelT, ← hL] : Stmt.atom (.keccak [.n (ch + 4 * l),
    .n (ch + 4 * l + 1), .n (ch + 4 * l + 2), .n (ch + 4 * l + 3), .n pr, .n (pr + 1), .n (pr + 2),
    .n (pr + 3), .n (L + 3), .n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)]
    ((List.range 13).map fun c ↦ .n (L + 4 + c)) false false) ∈ _)
  have s1 := hA _ (by simp [oqPathT] : Stmt.atom (.const (.n (ch + 81)) (word 5 0 0)) ∈ _)
  have s2 := hA _ (by simp [oqPathT] :
    Stmt.atom (.mul (.n (ch + 82)) (.n (ch + 4 * s.pd)) (.n (ch + 81))) ∈ _)
  simp only [Atom.Holds] at a1 a2 a3 a4 a5 s1 s2
  have hb : σ (.n L) = bitE b := loadHolds_unique a0 hbit
  have hsel : σ (.n (L + 2)) = σ (.n (ch + 4 * s.pd)) * gen ^ (if b then 2 else 0) := by
    rw [a2, a1, hb, s2, s1, word_five, sel_eq]
  rw [hsel] at a3 a4
  have hpair := oqPair_hash hpad hz a5 a6
  obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests hpair
  have hfr := (oqPath_frame hA).2
  have fr : ∀ j, j < 2 → ∀ x, LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if b then 2 else 0))
      (4 * l + j) x → x = σ (.n (ch + 4 * l + (if b then 2 else 0) + j)) := fun j hj x hx => by
    rw [loadHolds_mul_gen_pow] at hx
    have := hfr _ (by split <;> omega) x hx.2
    rw [this]; congr 2; omega
  have n0 := fr 0 (by omega) _ a3
  have n1 := fr 1 (by omega) _ a4
  have o0 : oqNode s kL ch (l + 1) 0 = L + 4 := by simp [oqNode, hL]
  have o1 : oqNode s kL ch (l + 1) 1 = L + 5 := by simp [oqNode, hL]
  have hout : (σ (.n (oqNode s kL ch (l + 1) 0)), σ (.n (oqNode s kL ch (l + 1) 1))) =
      digestScalars (hashPair dl dr) := by
    rw [o0, o1, ← hp]; simp [List.getD_eq_getElem?_getD]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at n0 n1 ⊢
    have hdl : dl = node := capDigestScalars_injective (by rw [← hl', ← hnode, n0, n1])
    subst hdl
    exact ⟨dr, hl', hr', hout, a3, a4⟩
  · simp only [↓reduceIte] at n0 n1 ⊢
    have hdr : dr = node := capDigestScalars_injective (by
      rw [← hr', ← hnode, n0, n1])
    subst hdr
    exact ⟨dl, hl', hr', hout, a3, a4⟩

/-! ## The path -/

theorem climbNode_append {leaf : Digest} {q : ℕ} {sibs t : List Digest} {l : ℕ}
    (hl : l ≤ sibs.length) : climbNode leaf q (sibs ++ t) l = climbNode leaf q sibs l := by
  simp [climbNode, List.take_append_of_le_length hl]

theorem pathCell_append {leaf : Digest} {q : ℕ} {sibs t : List Digest} {k : ℕ}
    (hk : k < 4 * sibs.length) : pathCell leaf q (sibs ++ t) k = pathCell leaf q sibs k := by
  have hl : k / 4 < sibs.length := by omega
  simp only [pathCell, climbNode_append (le_of_lt hl), List.getD_eq_getElem?_getD,
    List.getElem?_append_left hl]

theorem climbNode_length (leaf : Digest) (q : ℕ) (sibs : List Digest) :
    climbNode leaf q sibs sibs.length = climbD leaf q sibs := by
  simp [climbNode]

/-- **The path below the cap** (`verify_merkle_path`, G:1026-1041): with the bits those of `q`
and the leaf's digest the first node, the hinted children are the frame run `pathCell` of some
siblings, each level's node is stored on its bit's side, and the last node is
`climbD leaf q sibs` (`climb`, V:492). -/
theorem oqPath_sound {s : Oq} {bp : V} {pr kL ch q : ℕ} {leaf : Digest}
    (hA : ∀ a, Stmt.atom a ∈ oqPathT s bp pr kL ch → a.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hbits : ∀ l < s.pd, LoadHolds rd (σ bp) l (bitE (q.testBit l)))
    (hleaf : (σ (.n (oqNode s kL ch 0 0)), σ (.n (oqNode s kL ch 0 1))) = digestScalars leaf) :
    ∃ sibs : List Digest, sibs.length = s.pd ∧
      (∀ k < 4 * s.pd, σ (.n (ch + k)) = pathCell leaf q sibs k) ∧
      (∀ l < s.pd,
        (σ (.n (oqNode s kL ch l 0)), σ (.n (oqNode s kL ch l 1))) =
          digestScalars (climbNode leaf q sibs l) ∧
        LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if q.testBit l then 2 else 0)) (4 * l)
          (σ (.n (oqNode s kL ch l 0))) ∧
        LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if q.testBit l then 2 else 0)) (4 * l + 1)
          (σ (.n (oqNode s kL ch l 1)))) ∧
      (σ (.n (oqNode s kL ch s.pd 0)), σ (.n (oqNode s kL ch s.pd 1))) =
        digestScalars (climbD leaf q sibs) := by
  suffices h : ∀ m ≤ s.pd, ∃ sibs : List Digest, sibs.length = m ∧
      (∀ k < 4 * m, σ (.n (ch + k)) = pathCell leaf q sibs k) ∧
      (∀ l < m,
        (σ (.n (oqNode s kL ch l 0)), σ (.n (oqNode s kL ch l 1))) =
          digestScalars (climbNode leaf q sibs l) ∧
        LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if q.testBit l then 2 else 0)) (4 * l)
          (σ (.n (oqNode s kL ch l 0))) ∧
        LoadHolds rd (σ (.n (ch + 4 * s.pd)) * gen ^ (if q.testBit l then 2 else 0)) (4 * l + 1)
          (σ (.n (oqNode s kL ch l 1)))) ∧
      (σ (.n (oqNode s kL ch m 0)), σ (.n (oqNode s kL ch m 1))) =
        digestScalars (climbD leaf q sibs) from h s.pd le_rfl
  intro m hm
  induction m with
  | zero => exact ⟨[], rfl, fun k hk => absurd hk (by omega), fun l hl => absurd hl (by omega), hleaf⟩
  | succ m ih =>
    obtain ⟨sibs, hlen, hch, hlv, hnd⟩ := ih (by omega)
    obtain ⟨sib, c01, c23, hnext, ld0, ld1⟩ :=
      oqLevel_sound (l := m) (by omega) hA hpad hz (hbits m (by omega)) hnd
    refine ⟨sibs ++ [sib], by simp [hlen], fun k hk => ?_, fun l hl => ?_, ?_⟩
    · by_cases hk' : k < 4 * m
      · rw [pathCell_append (by rw [hlen]; exact hk'), hch k hk']
      · have hl : k / 4 = m := by omega
        have hcl : climbNode leaf q (sibs ++ [sib]) m = climbD leaf q sibs := by
          rw [climbNode_append (by omega), ← hlen, climbNode_length]
        have hsg : (sibs ++ [sib]).getD m (Vector.replicate 4 0) = sib := by
          simp [List.getD_eq_getElem?_getD, hlen]
        simp only [pathCell, hl, hcl, hsg]
        obtain ⟨j, hj, rfl⟩ : ∃ j < 4, k = 4 * m + j := ⟨k - 4 * m, by omega, by omega⟩
        rw [show (4 * m + j) % 4 = j by omega, show (4 * m + j) % 2 = j % 2 by omega]
        have e0 := congrArg Prod.fst c01
        have e1 := congrArg Prod.snd c01
        have e2 := congrArg Prod.fst c23
        have e3 := congrArg Prod.snd c23
        simp only at e0 e1 e2 e3
        rw [show ch + 4 * m + 1 = ch + (4 * m + 1) by omega] at e1
        rw [show ch + 4 * m + 2 = ch + (4 * m + 2) by omega] at e2
        rw [show ch + 4 * m + 3 = ch + (4 * m + 3) by omega] at e3
        cases hb : q.testBit m <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at e0 e1 e2 e3 <;>
          interval_cases j <;> simp [e0, e1, e2, e3]
    · by_cases hl' : l < m
      · rw [climbNode_append (by omega)]; exact hlv l hl'
      · have : l = m := by omega
        subst this
        rw [climbNode_append (by omega), ← hlen, climbNode_length, hlen]
        exact ⟨hnd, ld0, ld1⟩
    · rw [hnext, climbD_snoc, hlen, Nat.testBit_eq_decide_div_mod_eq]
      by_cases h : q / 2 ^ m % 2 = 1
      · simp [h]
      · simp [show q / 2 ^ m % 2 = 0 by omega]

end
end LeanVM.Guest.B1
