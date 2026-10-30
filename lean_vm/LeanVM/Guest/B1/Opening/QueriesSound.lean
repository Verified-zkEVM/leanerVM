/-
  LeanVM.Guest.B1.Opening.QueriesSound

  One query is `QueryOpens`; the soundness direction of `opening_queries`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesCap

/-!
# One query, assembled (`opening_query`, G:1177-1241)

`oqQuery_sound`: the atoms of `oqQueryT` (the row, the dot product, the padding run, the leaf
hash, the path, the cap leaf) give `QueryOpens` at the position whose bits the bit pointer reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The query's pieces, by membership. -/
theorem oqQuery_pieces {s : Oq} {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ) :
    (∀ a, Stmt.atom a ∈ oqPacksT b s.R → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ) ∧
      (emit = true → ∀ a, Stmt.atom a ∈ oqPadT (oqK1 b s.R + s.D) → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqPathT s bp (oqPr s b emit pr) (oqKL s b emit) (oqCh s b emit) →
        a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqCapT s bp cap flags (oqKL s b emit) (oqCh s b emit) → a.Holds rd σ) := by
  refine ⟨fun a h => hA a ?_, fun a h => hA a ?_, fun he a h => hA a ?_, fun a h => hA a ?_,
    fun a h => hA a ?_, fun a h => hA a ?_⟩ <;> simp only [oqQueryT, List.mem_append] <;> simp_all

/-- **One query is `QueryOpens`** (G:1177-1241): with the padding run `1, 0, 0, 0, 0` and the bit
pointer reading the bits of `q < 2^(pd + cd)`, the query opens the hinted row at `q` and its value
is the row's dot product with the weights. -/
theorem oqQuery_sound {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ oqQueryT s bp cap flags wp b emit pr → a.Holds rd σ)
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hbits : ∀ l < s.pd + s.cd, LoadHolds rd (σ bp) l (bitE (q.testBit l))) :
    QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, hL, hPa, hC⟩ := oqQuery_pieces hA
  have hR2 : s.R % 2 = 0 := by rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [Oq.R, hb, hI]
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  -- the row and the dot product
  have hW := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hW
  -- the leaf
  have hpk : ∀ j < s.ncells, σ (.n (oqPk b s.R j)) =
      E.ofLimbs ((oqRow b s.R σ).getD (2 * j) 0) ((oqRow b s.R σ).getD (2 * j + 1) 0) 0 :=
    fun j hj => by
      have hj' : j < s.R / 2 := hj
      rw [(oqPack_sound hP hj').2.2, getD_oqRow (by omega), getD_oqRow (by omega)]
      rfl
  have hleaf := oqLeaf_sound hs hL hpad hz (by simp [oqRow, Oq.ncells]; omega) hpk
  -- the path
  obtain ⟨sibs, hsl, hch, hlv, hnd⟩ := oqPath_sound hPa hpad hz
    (fun l hl => hbits l (by omega)) hleaf
  obtain ⟨hpp, hfr⟩ := oqPath_frame hPa
  -- the cap
  obtain ⟨hflag, hc0, hc1⟩ := oqCap_sound hcd hcd8 hC hq (fun l h1 h2 => hbits l h2)
  unfold QueryOpens
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, sibs, oqW s b σ, σ (.n (oqCh s b emit + 4 * s.pd)), hsl,
    fun l hl => hw l (by simpa [Oq.lo] using hl), hpp, fun k hk x hx => ?_, fun l hl => ?_, ?_,
    ?_, hflag, ?_⟩
  · rw [hfr k hk x hx, hch k hk]
  · obtain ⟨hn, h0, h1⟩ := hlv l hl
    rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) l 0)) =
      (digestScalars (climbNode (hashWords (oqRow b s.R σ)) q sibs l)).1 by rw [← hn]] at h0
    rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) l 1)) =
      (digestScalars (climbNode (hashWords (oqRow b s.R σ)) q sibs l)).2 by rw [← hn]] at h1
    exact ⟨h0, h1⟩
  · rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) s.pd 0)) =
      (digestScalars (climbD (hashWords (oqRow b s.R σ)) q sibs)).1 by rw [← hnd]] at hc0
    exact hc0
  · rw [show σ (.n (oqNode s (oqKL s b emit) (oqCh s b emit) s.pd 1)) =
      (digestScalars (climbD (hashWords (oqRow b s.R σ)) q sibs)).2 by rw [← hnd]] at hc1
    exact hc1
  · rw [hdot, rowDot_eq]
    congr 1

end
end LeanVM.Guest.B1
