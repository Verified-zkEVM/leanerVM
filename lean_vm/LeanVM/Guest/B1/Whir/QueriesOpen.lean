/-
  LeanVM.Guest.B1.Whir.QueriesOpen

  A level's queries, from `opening_queries`' meaning: the openings the Spec reads, each passing
  `openOne`, and the queries' sum the Spec's `enforcedSum`.
-/

module

public import LeanVM.Guest.B1.Whir.QueryBits
public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Opening.QueriesRun
public import LeanVM.Protocol.WithHash

/-!
# The queries' openings and sum (TRIAGE G #39, #40)

`queries_open`: `opening_queries`' meaning (B1-a's `MeaningOpeningQueries`) over a cap the cap check
holds (`MeaningVerifyMerkleCap`) with the level's root, at positions whose bits the decodes wrote
(`positions_of_decodes`), gives the Spec's openings (`⟨row, below-cap siblings ++ cap siblings⟩`,
each passing `openOne`, `query_openOne`) and the queries' sum is `enforcedSum` of their rows
(`oqChain_powers`, `enforcedSum_eq`), the rows read as the Spec reads them (`specRow`) when a
row's `rowDot` with the weights at `wp` is its `dot` with `eqKernel` of the level's folds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- Two positions below `2^d` with the same `d` bits are equal. -/
theorem eq_of_bits {a b d : ℕ} (ha : a < 2 ^ d) (hb : b < 2 ^ d)
    (h : ∀ l < d, a.testBit l = b.testBit l) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro l
  rcases Nat.lt_or_ge l d with hl | hl
  · exact h l hl
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hl)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hl))]

/-- Choices below `n` as a list (any type). -/
theorem exists_list_of_forall' {α : Type} [Inhabited α] {P : ℕ → α → Prop} {n : ℕ}
    (h : ∀ j < n, ∃ v, P j v) : ∃ l : List α, l.length = n ∧ ∀ j (hj : j < l.length), P j l[j] := by
  classical
  refine ⟨(List.range n).map fun j ↦ if hj : j < n then Classical.choose (h j hj) else default,
    by simp, fun j hj ↦ ?_⟩
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range, hj, ↓reduceDIte]
  exact Classical.choose_spec (h j hj)

instance : Inhabited Opening := ⟨⟨[], []⟩⟩

/-- **The queries' openings and sum.** -/
theorem queries_open {odd base I depth cd q N0 : ℕ} {cap flags lam lamN qptrs wp nG sum r0 r1 : E}
    {root : Digest}
    (hm : MeaningOpeningQueries odd base I depth cd rd [cap, flags, lam, lamN, qptrs, wp, nG] [sum])
    (hcap : MeaningVerifyMerkleCap cd rd [cap, flags] [r0, r1])
    (hroot : (r0, r1) = digestScalars root) (hcd : 2 ≤ cd) (hcdd : cd ≤ depth)
    (hnG : nG = gen ^ N0) (hN0 : N0 < ordG) (hQ : oqCount odd base N0 = q) (hodd : odd ≤ 1)
    (hb : base = 1 ∨ (base = 0 ∧ odd = 0))
    (qs : List ℕ) (hqlt : ∀ k < q, qs.getD k 0 < 2 ^ depth)
    (hbits : ∀ k < q, ∃ bp, LoadHolds rd qptrs k bp ∧ ∀ l < depth, ∀ w, LoadHolds rd bp l w →
      w = bitE ((qs.getD k 0).testBit l))
    (hlamN : lamN = lam ^ q) {width : ℕ} (hwidth : (if base = 1 then I else 3 * I) = width)
    (specRow : List K → List E) (fd : List E)
    (hdot : ∀ (row : List K) (w : ℕ → E), row.length = width →
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) →
        rowDot base I row w = dot (specRow row) (eqKernel fd)) :
    ∃ os : List Opening, os.length = q ∧
      (∀ k (hk : k < qs.length) (ho : k < os.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root depth width qs[k] os[k]) = true) ∧
      sum = enforcedSum ((os.map (·.leaf)).map specRow) fd (powers lam q) := by
  obtain ⟨N, hN, hnG', hlam, bps, qs', rows, ds, hall, ch, -, hret⟩ := hm
  have hNN : N = N0 := gen_pow_inj hN hN0 (hnG'.symm.trans hnG)
  subst hNN
  -- the positions
  have hqs' : ∀ k < q, qs' k = qs.getD k 0 := by
    intro k hk
    obtain ⟨hbp, hlt, hb', -⟩ := hall k (by rw [hQ]; exact hk)
    obtain ⟨bp, hbp', hbits'⟩ := hbits k hk
    have e := loadHolds_unique hbp hbp'
    subst e
    refine eq_of_bits hlt (hqlt k hk) fun l hl ↦ bitE_injective ?_
    exact hbits' l hl _ (hb' l hl)
  -- the openings
  have hop : ∀ k < q, ∃ o : Opening,
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root depth width (qs.getD k 0) o) = true ∧
        o.leaf = rows k := by
    intro k hk
    obtain ⟨-, hlt, -, hrow, sibs, w, pp, hsl, -, -, -, -, h0, h1, hfl, -⟩ := hall k (by rw [hQ]; exact hk)
    rw [hqs' k hk] at h0 h1 hfl hlt
    obtain ⟨cs, -, hcs⟩ := query_openOne hcd hcdd hcap hroot hlt (hrow.trans hwidth) hsl h0 h1 hfl
    exact ⟨⟨rows k, sibs ++ cs⟩, hcs, rfl⟩
  obtain ⟨os, hol, hos⟩ := exists_list_of_forall' hop
  refine ⟨os, hol, fun k hk ho ↦ ?_, ?_⟩
  · have := (hos k ho).1
    rwa [List.getD_eq_getElem _ _ hk] at this
  · -- the sum
    have hds : ∀ k < q, ds k = dot (specRow (rows k)) (eqKernel fd) := by
      intro k hk
      obtain ⟨-, -, -, hrow, sibs, w, pp, -, hw, -, -, -, -, -, -, hd⟩ := hall k (by rw [hQ]; exact hk)
      rw [hd]
      exact hdot _ _ (hrow.trans hwidth) hw
    obtain ⟨hret, -⟩ := List.cons_eq_cons.mp hret
    rw [hret, hlamN, ← hQ, oqChain_powers hlam hodd hb, hQ]
    have hrl : ((os.map (·.leaf)).map specRow).length = q := by simp [hol]
    rw [← hrl, enforcedSum_eq, hrl]
    unfold powSum
    have hmap : (List.range q).map (fun k ↦ lam ^ k * ds k) =
        (List.range q).map (fun k ↦ lam ^ k *
          dot (((os.map (·.leaf)).map specRow).getD k []) (eqKernel fd)) := by
      refine List.map_congr_left fun k hk ↦ ?_
      have hk' : k < q := List.mem_range.mp hk
      rw [hds k hk', List.getD_eq_getElem _ _ (by simp [hol]; exact hk')]
      simp only [List.getElem_map]
      rw [(hos k (by rw [hol]; exact hk')).2]
    rw [hmap]

end
end LeanVM.Guest.B1.Whir
