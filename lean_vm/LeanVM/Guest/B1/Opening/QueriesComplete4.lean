/-
  LeanVM.Guest.B1.Opening.QueriesComplete4

  The completeness of one query of `opening_queries`: every atom holds at the honest values, and
  the query's value is the row's dot product.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete3

/-!
# One query, completeness

`QD.Ok` is what `QueryOpens` says of an honest query (`exists_of_opens`): the siblings and the
row's length, the memory (`MemOk`), the weights at `wp`, the position below `2^depth`.
`query_complete`: at a valuation that is the honest values on the query's indices, with the
padding run `1, 0, 0, 0, 0` and the bit pointer reading the position's bits, every atom of
`oqQueryT` holds and the query's value is `rowDot` (by the soundness direction, `oqQuery_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A row's dot product reads the weights below `rowLo I + I / rowLo I` only. -/
theorem rowDot_congr {base I : ℕ} {row : List K} {w w' : ℕ → E}
    (h : ∀ l < rowLo I + I / rowLo I, w l = w' l) : rowDot base I row w = rowDot base I row w' := by
  unfold rowDot
  refine congrArg (List.foldl _ _) (List.map_congr_left fun hh hm => ?_)
  rw [List.mem_range] at hm
  rw [h _ (by omega)]
  refine congrArg (w' _ * ·) (congrArg (List.foldl _ _) (List.map_congr_left fun l hl => ?_))
  rw [List.mem_range] at hl
  rw [h l (by omega)]

namespace QD

/-- What `QueryOpens` says of an honest query. -/
structure Ok (d : QD) (rd : Reader) (wp : E) : Prop where
  hsibs : d.sibs.length = d.s.pd
  hrow : d.row.length = d.s.R
  hmem : d.MemOk rd
  hrd : d.rd = rd
  hw : ∀ l < d.s.lo + d.s.I / d.s.lo, LoadHolds rd wp l (d.w l)
  hq : d.q < 2 ^ (d.s.pd + d.s.cd)

/-- **An opening is an honest query**, wherever it is placed. -/
theorem exists_of_opens {rd : Reader} {s : Oq} {cap flags wp : E} {q : ℕ} {row : List K} {dv : E}
    (hq : q < 2 ^ (s.pd + s.cd))
    (h : QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q row dv) :
    ∃ (w : ℕ → E) (sibs : List Digest) (pp : E), dv = rowDot s.base s.I row w ∧
      ∀ b emit pr, (QD.mk s b emit pr row w q sibs pp cap flags rd).Ok rd wp := by
  obtain ⟨hrl, sibs, w, pp, hsl, hw, hpp, hfr, hnd, hc0, hc1, hfl, hd⟩ := h
  rw [show s.pd + s.cd - s.cd = s.pd by omega] at hsl hfr hnd hc0 hc1 hfl
  exact ⟨w, sibs, pp, hd, fun b emit pr => ⟨hsl, hrl, ⟨hpp, hfr, hnd, hc0, hc1, hfl⟩, rfl, hw, hq⟩⟩

variable (d : QD) {rd : Reader} {σ : Val}

/-- The padding run a query emits. -/
theorem pad_of_emit (he : d.emit = true)
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) :
    σ (.n d.prV) = word 1 0 0 ∧ ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0 := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hkL : d.kL = d.k1 + d.s.D + 5 := by rw [kL_eq, he]; rfl
  have hpr : d.prV = d.k1 + d.s.D := by simp only [prV, oqPr, he, ↓reduceIte]; rfl
  refine ⟨?_, fun i hi => ?_⟩
  · have := hv (d.k1 + d.s.D + 0) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    simpa only [hpr, Nat.add_zero, List.getD_cons_zero] using this
  · have := hv (d.k1 + d.s.D + (i + 1)) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    rw [hpr, show d.k1 + d.s.D + 1 + i = d.k1 + d.s.D + (i + 1) by omega, this]
    interval_cases i <;> rfl

/-- The row a query's atoms read is the honest row. -/
theorem oqRow_eq (hrow : d.row.length = d.s.R)
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i) : oqRow d.b d.s.R σ = d.row := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  refine List.ext_getElem (by simp [oqRow, hrow]) fun i h1 h2 => ?_
  have hi : i < d.s.R := by simpa [oqRow] using h1
  simp only [oqRow, List.getElem_map, List.getElem_range]
  rw [hv _ (by omega) (by omega), val_row d hi, QD.rw, limb_ofK]
  simp [List.getD_eq_getElem?_getD, h2]

/-- **One query holds at the honest values**, and its value is the row's dot product. -/
theorem query_complete (hs : d.s.RowShape) (hpd : 4 * d.s.pd ≤ 80) (hcd : 2 ≤ d.s.cd)
    (hcd8 : d.s.cd ≤ 8) {bp cap flags wp : V} (hok : d.Ok rd (σ wp))
    (hv : ∀ i, d.b ≤ i → i < d.z + 11 → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 0)
    (hbits : ∀ l < d.s.pd + d.s.cd, LoadHolds rd (σ bp) l (bitE (d.q.testBit l)))
    (hcap : σ cap = d.capv) (hflags : σ flags = d.flagsv) :
    (∀ a, Stmt.atom a ∈ oqQueryT d.s bp cap flags wp d.b d.emit d.pr → a.Holds rd σ) ∧
      σ (.n (oqDot d.s d.b)) = rowDot d.s.base d.s.I d.row d.w := by
  have hA : ∀ a, Stmt.atom a ∈ oqQueryT d.s bp cap flags wp d.b d.emit d.pr → a.Holds rd σ := by
    intro a ha
    simp only [oqQueryT, List.mem_append] at ha
    rcases ha with (((((ha | ha) | ha) | ha) | ha) | ha) | ha
    · simp only [oqRowT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      subst ha
      trivial
    · exact d.oqPacks_complete hv a ha
    · exact d.oqDot_complete hs hv hok.hw a ha
    · cases he : d.emit
      · simp [he] at ha
      · simp only [he, ↓reduceIte] at ha
        exact d.oqPad_complete he hv a ha
    · exact d.oqLeaf_complete hs hv hpad hz a ha
    · exact d.oqPath_complete hs hpd hok.hsibs hok.hrow hv hpad hz hbits hok.hmem hok.hrd a ha
    · exact d.oqCap_complete hs hpd hok.hsibs hok.hrow hcd hcd8 hok.hq hv hpad hz hbits hok.hmem
        hcap hflags a ha
  refine ⟨hA, ?_⟩
  obtain ⟨-, -, w', -, -, hw', -, -, -, -, -, -, hd⟩ :=
    oqQuery_sound hs hcd hcd8 hA hpad (fun i hi => by rw [← word_zero]; exact hz i hi) hok.hq hbits
  rw [hd, d.oqRow_eq hok.hrow hv]
  exact rowDot_congr fun l hl => loadHolds_unique (hw' l hl) (hok.hw l hl)

end QD

end
end LeanVM.Guest.B1
