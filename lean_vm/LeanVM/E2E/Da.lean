/-
  LeanVM.E2E.Da

  The DA leg of the end-to-end theorem in the random-oracle model (design E5): a DA claim held
  and outer-checked on a log without the DA bad event is backed by codewords, and the game ends
  with that bad event with probability at most `Q · 14 / 2^192 + 4 Q² / 2^256`.
-/

module

public import LeanVM.E2E.Engine
public import LeanVM.E2E.Da.Potential

/-!
# The DA leg

The design's §0 DA event: V_I accepts, and a root DA claim `(r, v)` is not backed by codeword
rows whose commitment and vector digest the final log answers (`DaBacked`). The guest's DA
check gives a witness opening the claim with the log's answers (`Witness.OpensWith`), and V_I's
outer check gives `toBytes v = vectorDigestOfWith (look ℓ) r`, answered (`outerChecksWith`).

**The bad event** (`DaBad pc`). A log is DA-bad if it failed for DA (`FailDA pc`: a collision,
an answer equal to the padding digest `pc`, or an answer predicting a chunk or a completed root
of an input), or it has a *DA hit* (`DaHit pc`): an entry completing a root `ρ` in the entries
before it (the anchor of `ρ`'s membership challenges) whose 14 squeezes the log answers, with
challenges accepting every row of rows the entries before the anchor commit to `ρ`
(`ColCommits`) that are not all codewords (`DaBadSet`).

**The cache form** (`daBacked_of_not_daBad`). On a log that is not DA-bad, a claim held and
outer-checked is backed: the vector digests have no collision, so the witness's vector is the
membership vector of `r`, which is the dual codeword of the challenges (`dualCodeword_eq_dual`);
every row is orthogonal to it; the root's commitment precedes the anchor (no completed root is
predicted) and its column tree precedes the root (no chunk is predicted, `colTree_take`), so the
rows are committed before the anchor; there being no hit, they are codewords.

**The probability** (`prEvent_game_daBad_le`, `prEvent_game_daUnbacked_le`). The DA potential
(`daPot`) forces `1` on a DA-bad log (`one_le_daPot_of_daBad`) and rises by at most
`14 / |E| + 4 (|ℓ| + 1) / |Digest|` per fresh hash query (`daPot_step`), so by the game's engine
(`prEvent_game_le_of_freshStepBelow`), for a game with at most `Q` hash queries,

  `Pr[some DA claim of the root is held and outer-checked but not backed] ≤
    Q · (14 / 2^192 + 4 Q / 2^256)`.

With the query bound of `gameComp` from its parts (`isQueryBoundP_gameComp`), `Q` is
`nx · cxk + ns · csk + (qH + sX · cxs + sS · css) + budget` (`prEvent_game_daUnbacked_le_of_costs`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The bad event -/

/-- **A DA hit**: an entry completing a root `ρ` in the entries before it, whose `14` squeezes
the log answers, with challenges bad for `ρ` there. -/
def DaHit (pc : LeanDa.Digest) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length) (ρ : LeanDa.Digest) (zs : List E),
    DaRootOf (ℓ.take i) ℓ[i].1 ρ ∧
      Da.squeezesWith (Da.daHash (look ℓ)) LeanDa.logK (Da.toBytes ℓ[i].2) = some zs ∧
      zs ∈ DaBadSet pc (ℓ.take i) ρ

/-- **The DA bad event of a log**: it failed for DA, or it has a DA hit. -/
def DaBad (pc : LeanDa.Digest) (ℓ : Log) : Prop := FailDA pc ℓ ∨ DaHit pc ℓ

/-- The potential is at least one on a DA-bad log. -/
theorem one_le_daPot_of_daBad {pc : LeanDa.Digest} {ℓ : Log} (h : DaBad pc ℓ) :
    1 ≤ daPot pc ℓ := by
  by_cases hf : FailDA pc ℓ
  · rw [daPot, ite_eq_left hf]
  rcases h with h | ⟨i, hi, ρ, zs, hr, hzs, hbad⟩
  · exact absurd h hf
  rw [daPot, ite_eq_right hf]
  refine le_trans ?_ (Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_range.mpr hi))
  rw [daTerm_eq hi, anchorRoot_eq_some hr]
  dsimp only
  rw [gch_of_squeezes _ _ _ _ hzs, ind_of hbad]

/-! ## The cache form -/

section Cache

variable {ℓ : Log}

/-- A squeeze chain answered has as many challenges as squeezes. -/
theorem length_squeezesWith {HD : List UInt8 → Option LeanDa.Digest} :
    ∀ (n : ℕ) (s : LeanDa.Digest) (zs : List E), Da.squeezesWith HD n s = some zs →
      zs.length = n
  | 0, _, zs, h => by
    simp only [Da.squeezesWith, pure, Option.some.injEq] at h
    subst h; rfl
  | n + 1, s, zs, h => by
    simp only [Da.squeezesWith, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨s', -, rest, hrest, rfl⟩ := h
    rw [List.length_cons, length_squeezesWith n s' rest hrest]

/-- LeanDA's hash on a log, answered: a digest the log answers. -/
theorem daHash_eq_some {x : Bytes} {s : LeanDa.Digest} (h : Da.daHash (look ℓ) x = some s) :
    ∃ d, look ℓ x = some d ∧ s = Da.toBytes d := by
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  exact ⟨d, hd, rfl⟩

/-- **The outer check, answered**: the label's hash, the two observations of the root, the
squeezes, and the vector digest of the dual codeword of the challenges. -/
theorem vectorDigestOfWith_eq_some {r : Digest} {vd : LeanDa.Digest}
    (h : Da.vectorDigestOfWith (look ℓ) r = some vd) :
    ∃ (d0 d1 d2 : Digest) (zs : List E), look ℓ LeanDa.label = some d0 ∧
      look ℓ (digestBytes d0 ++ obsBlock (Da.toBytes r) 0) = some d1 ∧
      look ℓ (digestBytes d1 ++ obsBlock (Da.toBytes r) 1) = some d2 ∧
      Da.squeezesWith (Da.daHash (look ℓ)) LeanDa.logK (Da.toBytes d2) = some zs ∧
      Da.daHash (look ℓ) (vecBytes (LeanDa.dualCodeword zs)) = some vd := by
  simp only [Da.vectorDigestOfWith, Da.membershipVectorWith, Da.membershipChallengesWith,
    bind, Option.bind_eq_some_iff] at h
  obtain ⟨vec, hvec, hvd⟩ := h
  simp only [Functor.map, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hvec
  obtain ⟨zs, ⟨s0, h0, s1, h1, s2, h2, hzs⟩, rfl⟩ := hvec
  obtain ⟨d0, hd0, rfl⟩ := daHash_eq_some h0
  obtain ⟨d1, hd1, rfl⟩ := daHash_eq_some h1
  obtain ⟨d2, hd2, rfl⟩ := daHash_eq_some h2
  exact ⟨d0, d1, d2, zs, hd0, hd1, hd2, hzs, hvd⟩

/-- The membership vector of `14` challenges, read as a function, is their dual codeword. -/
theorem getD_ofFn_dual (z : Fin 14 → E) :
    (fun b : Fin (2 ^ 15) ↦ (List.ofFn (LeanDa.dual z)).getD b 0) = LeanDa.dual z := by
  funext b
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact b.isLt), List.getElem_ofFn]

/-- **The cache form of the DA leg.** On a log that is not DA-bad, a DA claim `(r, v)` held by
a witness whose hashes the log answers, and outer-checked with the log's answers, is backed by
codewords. -/
theorem daBacked_of_not_daBad {pc pr : LeanDa.Digest} (h : ¬ DaBad pc ℓ) {r v : Digest}
    {w : Da.Witness} (hw : w.OpensWith (look ℓ) pc pr r v)
    (hout : Da.vectorDigestOfWith (look ℓ) r = some (Da.toBytes v)) :
    DaBacked ℓ pc pr (r, v) := by
  have hF : ¬ FailDA pc ℓ := fun hf ↦ h (Or.inl hf)
  have hH : ¬ DaHit pc ℓ := fun hh ↦ h (Or.inr hh)
  obtain ⟨h1, h2, h3, hcom, -, hvd, horth⟩ := hw
  set ρ := Da.toBytes r
  obtain ⟨d0, d1, d2, zs, hd0, hd1, hd2, hzs, hvd'⟩ := vectorDigestOfWith_eq_some hout
  -- The witness's vector is the dual codeword of the challenges.
  have hvec : w.vector = LeanDa.dualCodeword zs :=
    vecBytes_injective (daHash_inj_of_not_failDA hF hvd hvd')
  have hlen : zs.length = 14 := length_squeezesWith _ _ _ hzs
  set z : Fin 14 → E := fun i ↦ zs[(i : ℕ)]'(by omega)
  have hz : zs = List.ofFn z :=
    List.ext_getElem (by rw [List.length_ofFn, hlen]) fun i _ _ ↦ by
      simp only [List.getElem_ofFn, z]
  have hdual : w.vector = List.ofFn (LeanDa.dual z) := by
    rw [hvec, hz, LeanDa.dualCodeword_eq_dual]
  have hacc : ∀ row ∈ w.rows, Accepts zs row := fun row hrow ↦
    ⟨z, hz, by have := horth row hrow; rwa [hdual, getD_ofFn_dual] at this⟩
  -- Backed if every row is a codeword.
  by_cases hcw : ∀ row ∈ w.rows, rowFn row ∈ LeanDa.rsCode
  · refine ⟨w.rows, h1, h2, fun row hrow ↦ ⟨h3 row hrow, ?_⟩, hcom, hout⟩
    have hmem : rowFn row ∈ (LeanDa.rsCode : Set LeanDa.Row) := hcw row hrow
    rw [← LeanDa.range_encodeRow] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hp.symm⟩
  push Not at hcw
  exfalso
  refine hH ?_
  -- The anchor: the entry observing the root's second half.
  obtain ⟨i, hi, hei, hni⟩ := (look_eq_some_iff ℓ _ d2).mp hd2
  obtain ⟨j1, hj1, hej1, -⟩ := (look_eq_some_iff ℓ _ d1).mp hd1
  have hj1i : j1 < i := lt_of_chunk_da hF hj1 hi (Or.inl (by
    rw [hei, hej1, chunk0_append]))
  -- The root is completed in every prefix past the first observation.
  have hroot : ∀ m, j1 < m → m ≤ ℓ.length →
      DaRootOf (ℓ.take m) (digestBytes d1 ++ obsBlock ρ 1) ρ := by
    intro m hm hml
    refine ⟨d1, ℓ[j1], rfl, ?_, by rw [hej1, List.drop_left' (digestBytes_length d0)]⟩
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp [hej1], j1, by simp; omega, by simp, fun j hj ↦ ?_⟩
    have := output_ne_da hF (by omega) hj1 hj
    simp only [List.getElem_take, hej1] at this ⊢
    simpa using this
  have hri : DaRootOf (ℓ.take i) ℓ[i].1 ρ := by
    rw [hei]; exact hroot i hj1i hi.le
  refine ⟨i, hi, ρ, zs, hri, by rw [hei]; exact hzs, ?_⟩
  -- The rows are committed before the anchor.
  obtain ⟨rt, c, hcol, hrc⟩ := commitCodewordsWith_eq_some hcom
  obtain ⟨vr, hvr, hρ⟩ := daHash_eq_some hrc
  obtain ⟨jr, hjr, hejr, hnjr⟩ := (look_eq_some_iff ℓ _ vr).mp hvr
  have hjri : jr < i := by
    by_contra hge
    push Not at hge
    refine not_daRootOf_of_not_failDA hF hjr ℓ[i].1 (mem_inputs_of_le_da hjr hge) ?_
    rw [hejr, ← hρ, hei]
    exact hroot jr (by omega) hjr.le
  have hrc' : Da.daHash (look (ℓ.take i)) (LeanDa.pairBytes rt c) = some ρ := by
    rw [Da.daHash, look_take_of_first hjr hejr hnjr hjri]
    simp [hρ]
  exact ⟨w.rows, ⟨⟨h1, h2, h3⟩, rt, c, colTree_take hF hi.le hrc' hcol, hrc'⟩, hcw, hacc⟩

end Cache

/-! ## The probability in the game -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The game ends DA-bad with probability at most `Q · (14 / 2^192 + 4 Q / 2^256)`**, for a
game with at most `Q` hash queries. -/
theorem prEvent_game_daBad_le (pc : LeanDa.Digest) (guest : Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[DaBad pc z.2] ≤
      Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) := by
  have h := prEvent_game_le_of_freshStepBelow (Φ := daPot pc)
    (δ := 14 * (Fintype.card E : ℝ≥0∞)⁻¹ + ((4 * Q : ℕ) : ℝ≥0∞) / Fintype.card Digest) Q
    (fun ℓ t hℓ _ ↦ by
      refine daPot_step.trans (add_le_add le_rfl (add_le_add le_rfl ?_))
      gcongr
      omega)
    guest fuel budget A Q hQ le_rfl (fun _ ℓ ↦ DaBad pc ℓ)
    (fun z _ hz ↦ one_le_daPot_of_daBad hz)
  rw [daPot_nil, zero_add] at h
  refine h.trans (le_of_eq ?_)
  rw [card_E_da, card_digest, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- **The DA leg in the game.** A DA claim of the root statement held by a witness whose hashes
the final log answers and outer-checked with its answers, but not backed, has probability at
most `Q · (14 / 2^192 + 4 Q / 2^256)`, for a game with at most `Q` hash queries. -/
theorem prEvent_game_daUnbacked_le (pc pr : LeanDa.Digest) (guest : Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[∃ c ∈ z.1.statement.claims.da,
        (∃ w : Da.Witness, w.OpensWith (look z.2) pc pr c.1 c.2) ∧
        Da.vectorDigestOfWith (look z.2) c.1 = some (Da.toBytes c.2) ∧
        ¬ DaBacked z.2 pc pr c] ≤
      Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz ↦ ?_)
    (prEvent_game_daBad_le pc guest fuel budget A Q hQ)
  obtain ⟨c, -, ⟨w, hw⟩, hout, hnb⟩ := hz
  by_contra hbad
  exact hnb (daBacked_of_not_daBad hbad hw hout)

/-- **The DA leg in the game, with the game's query bound from its parts**: the honest signers'
costs, the adversary's hash queries and signing requests, and V_I's budget. -/
theorem prEvent_game_daUnbacked_le_of_costs (pc pr : LeanDa.Digest) {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    let Q := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget
    Pr{let z ← game guest fuel budget A}[∃ c ∈ z.1.statement.claims.da,
        (∃ w : Da.Witness, w.OpensWith (look z.2) pc pr c.1 c.2) ∧
        Da.vectorDigestOfWith (look z.2) c.1 = some (Da.toBytes c.2) ∧
        ¬ DaBacked z.2 pc pr c] ≤
      Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) :=
  prEvent_game_daUnbacked_le pc pr guest fuel budget A _
    (isQueryBoundP_gameComp hxk hsk hxs hss guest fuel budget A hH hX hS)

end Game

end
end LeanVM.E2E
