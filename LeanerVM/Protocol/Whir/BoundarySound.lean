/-
  LeanerVM.Protocol.Whir.BoundarySound

  The soundness of a level's boundary for the list relation: the residual claim, the commitment of
  the next word, the out-of-domain point, the positions, the batching challenge and the glue; the
  language at each seam and the count of escapes at each challenge.
-/

module

public import LeanerVM.Protocol.Whir.FoldSound
public import LeanerVM.Protocol.Whir.Counting

/-!
# The level boundary is sound for the list relation

Category B: Annex B, proof of `thm:rbr`: "the level interface", "OOD challenge `z`", "query message
`Q_i`", "batching challenge `λ`".

Between the last fold challenge and the next level's first round the statement is the record `Bd`,
and the language (what a cheating prover has gained, `FoldSound`) changes at each step:

* after the folds and the residual claim's polynomial: `ResLang`, some codeword near the level's
  word satisfies the residual claim (or the folded lists failed to correspond);
* the commitment of the next word and the messages (the out-of-domain answer, its claim's
  polynomial, the nonce) carry nothing into it;
* `OodLang` after the coordinates of the out-of-domain point: `ResLang`, or two codewords near the
  next word are not yet separated on the coordinates drawn (`Sep`), the pairs' differences being
  tables that vanish on the partial point (`RestrictedZero`); each coordinate separates all but
  `C(L', 2)` values (`card_ood_step_le`), where `L'` is the next word's list bound;
* `QLang` after the positions: `OodLang`, or some codeword near the next word satisfies the residual
  claim, the out-of-domain claim and the consistency claims at the positions (`AllClaims`); outside
  `OodLang` that happens for at most `a ^ t` choices of the positions (`card_positions_bad_le`);
* `BLang` after the batching challenge: some codeword near the next word satisfies the batched
  claim; outside `QLang` at most `(t + 1) L'` challenges (`card_batch_bad_le`). The reading of the
  level's word records the folded symbols (`cqAt`) and drops it; the language afterwards is `BLang`
  with the recorded symbols;
* `relP`, after the query batch's polynomial: the next level's language at its start (`FoldLangMid`
  at the glued claim and polynomial).

Every language here ignores the witness (`Component.indep`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Whir

/-! ## Tables and lanes -/

/-- Distinct interleaved codewords decode to distinct tables. -/
private theorem ofLanes_injective {L κ : ℕ} :
    Function.Injective (ofLanes : (Fin (2 ^ L) → CMlPolynomialEval E κ) →
      CMlPolynomialEval E (L + κ)) := by
  intro m m' h
  funext u
  apply Vector.ext
  intro i hi
  have := congrArg (fun t ↦ t[cubeIndex u ⟨i, hi⟩]) h
  simp only [ofLanes_getElem] at this
  exact this

/-- The partial point of the coordinates drawn so far, with one more. -/
private theorem partial_ofVector_push {j : ℕ} (z : Vector E j) (c : E) :
    Partial.ofVector 0 (z.push c) = Function.update (Partial.ofVector 0 z) j (some c) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [Partial.ofVector]
  · rw [Function.update_of_ne hi]
    simp only [Partial.ofVector]
    by_cases hij : i < j
    · simp [hij, show i < j + 1 by omega]
    · simp [hij, show ¬ i < j + 1 by omega]

/-! ## The languages of the boundary -/

section Boundary

variable {sh sh' : Shape} {κ' : ℕ} (P : Par sh (Kap sh' κ')) (P' : Par sh' κ')

/-- The level's own oracle among the oracles beside the next word. -/
abbrev oldOf (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) :
    ∀ i, OneW sh (Kap sh' κ') i := fun i ↦ ob (.inl i)

/-- The next level's word among the oracles beside it. -/
abbrev newOf (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) :
    WordOf sh' κ' := ob (.inr ())

/-- The interleaved codeword with messages `h` is within the next level's threshold of its word. -/
def InNew (nw : WordOf sh' κ') (h : Msgs sh'.ℓ κ') : Prop :=
  Cl κ' sh'.R P'.a sh'.ℓ nw.lanes h

/-- The tables decoded from the codewords near the next word are pairwise distinct as functions
on the coordinates drawn so far: no pair has a difference that vanishes on them. -/
def Sep (nw : WordOf sh' κ') {j : ℕ} (z : Vector E j) : Prop :=
  ∀ h h' : Msgs sh'.ℓ κ', InNew P' nw h → InNew P' nw h' → h ≠ h' →
    ¬ RestrictedZero (diffTable (ofLanes h) (ofLanes h')) (Partial.ofVector 0 z)

/-- The language after `j` coordinates of the out-of-domain point: the residual claim's language,
or two codewords near the next word are not yet separated. -/
def OodLang {j : ℕ} (s : Bd sh (Kap sh' κ')) (z : Vector E j)
    (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) : Prop :=
  ResLang P s (oldOf ob) ∨ ¬ Sep P' (newOf ob) z

/-- Before any coordinate is drawn the tables are separated: distinct codewords decode to distinct
tables. -/
private theorem sep_nil (nw : WordOf sh' κ') : Sep P' nw (#v[] : Vector E 0) := by
  intro h h' _ _ hne hz
  rw [Partial.ofVector_zero, diffTable_restrictedZero_empty_iff] at hz
  exact hne (ofLanes_injective hz)

/-- **One coordinate of the out-of-domain point.** If the tables are separated on the coordinates
drawn so far, at most `C(L, 2)` values of the next coordinate fail to separate them: one value for
each unordered pair of codewords near the next word. -/
theorem card_ood_step_le (nw : WordOf sh' κ') {j : ℕ} (z : Vector E j) (hsep : Sep P' nw z) :
    Nat.card {c : E // ¬ Sep P' nw (z.push c)} ≤ Nat.choose P'.L 2 := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite (Msgs sh'.ℓ κ')
  let S : Finset (Msgs sh'.ℓ κ') :=
    Finset.univ.filter fun h ↦ Cl κ' sh'.R P'.a sh'.ℓ nw.lanes h
  have hS : S.card ≤ P'.L := by
    have := P'.hlist nw.lanes
    rwa [natCard_subtype_eq_card_filter] at this
  let 𝓛 : Finset (CMlPolynomialEval E (sh'.ℓ + κ')) := S.image ofLanes
  have h𝓛 : 𝓛.card ≤ P'.L := Finset.card_image_le.trans hS
  have hσ : ∀ g ∈ 𝓛, ∀ g' ∈ 𝓛, g ≠ g' →
      ¬ RestrictedZero (diffTable g g') (Partial.ofVector 0 z) := by
    intro g hg g' hg' hne
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hg'
    exact hsep h h' (Finset.mem_filter.mp hh).2 (Finset.mem_filter.mp hh').2
      (fun e ↦ hne (by rw [e]))
  have key := card_ood_bad_le 𝓛 (Partial.ofVector 0 z) j hσ
  rw [natCard_subtype_eq_card_filter] at key ⊢
  refine le_trans (Finset.card_le_card fun c hc ↦ ?_) (key.trans (Nat.choose_le_choose 2 h𝓛))
  have hc' : ¬ Sep P' nw (z.push c) := (Finset.mem_filter.mp hc).2
  simp only [Sep, not_forall] at hc'
  obtain ⟨h, h', hh, hh', hne, hz⟩ := hc'
  rw [not_not] at hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [partial_ofVector_push] at hz
  exact ⟨ofLanes h, Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩,
    ofLanes h', Finset.mem_image.mpr ⟨h', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh'⟩, rfl⟩,
    fun e ↦ hne (ofLanes_injective e), hz⟩

/-! ## The query positions -/

/-- The folded symbol of the level's word at the `q`-th position: the row at the position, folded
by the fold point. -/
def cqAt {κ : ℕ} (s : Bd sh κ) (o : ∀ i, OneW sh κ i) (q : Fin sh.t) : E :=
  foldRow s.r ((o 0).row (s.pos q))

/-- The claims of the next level at the glue, about the codeword with messages `h`: the residual
claim, the out-of-domain claim and the consistency claims at the positions, whose folded symbols
are `cqf`. -/
def AllClaims (s : Bd sh (Kap sh' κ')) (cqf : Fin sh.t → E) (nw : WordOf sh' κ') : Prop :=
  ∃ h : Msgs sh'.ℓ κ', InNew P' nw h ∧ s.resid.pair (RingHom.id E) (ofLanes h) = s.c ∧
    evalMle (ofLanes h) s.z = s.cood ∧
    ∀ q, encode (algebraMap K E) (Kap sh' κ') sh.R (ofLanes h) (s.pos q) = cqf q

/-- The language after the positions: the language before, or some codeword near the next word
satisfies all the claims. -/
def QLang (s : Bd sh (Kap sh' κ'))
    (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) : Prop :=
  OodLang P P' s s.z ob ∨ AllClaims P' s (cqAt s (oldOf ob)) (newOf ob)

/-- At most one codeword near the next word has the claimed out-of-domain value, when the tables
are separated at the point. -/
private theorem eq_of_sep_eval (nw : WordOf sh' κ') (z : Vector E (sh'.ℓ + κ')) (hsep : Sep P' nw z)
    {h h' : Msgs sh'.ℓ κ'} (hh : InNew P' nw h) (hh' : InNew P' nw h')
    (he : evalMle (ofLanes h) z = evalMle (ofLanes h') z) : h = h' := by
  by_contra hne
  refine hsep h h' hh hh' hne ?_
  rw [restrictedZero_of_all _ _ z (fun k hk ↦ by simp [Partial.ofVector, hk]), evalMle_diffTable,
    he, sub_self]

/-- **The query positions.** If the residual claim's language and the separation fail to hold,
at most `a ^ t` of the choices of the `t` positions make some codeword near the next word satisfy
all the claims: at most one codeword has the out-of-domain value, and either it is a fold of a
codeword near the level's word, which does not satisfy the residual claim, or its encoding agrees
with the folded word on fewer than `a` positions, and every position must be one of them. -/
theorem card_positions_bad_le (s : Bd sh (Kap sh' κ'))
    (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i)
    (hnot : ¬ OodLang P P' s s.z ob) :
    Nat.card {x : Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R)) //
      AllClaims P' { s with pos := x } (cqAt { s with pos := x } (oldOf ob)) (newOf ob)} ≤
        P.a ^ sh.t := by
  classical
  have := Fintype.ofFinite (Msgs sh'.ℓ κ')
  unfold OodLang at hnot
  push Not at hnot
  obtain ⟨hres, hsep⟩ := hnot
  rw [natCard_subtype_eq_card_filter]
  by_cases hex : ∃ h : Msgs sh'.ℓ κ', InNew P' (newOf ob) h ∧
      evalMle (ofLanes h) s.z = s.cood ∧ s.resid.pair (RingHom.id E) (ofLanes h) = s.c
  · obtain ⟨h0, hh0, he0, hr0⟩ := hex
    -- the positions where the codeword's encoding agrees with the folded word
    let S : Finset (Fin (2 ^ (Kap sh' κ' + sh.R))) := Finset.univ.filter fun y ↦
      encode (algebraMap K E) (Kap sh' κ') sh.R (ofLanes h0) y =
        foldRow s.r ((oldOf ob 0).row y)
    have hS : S.card ≤ P.a := card_agree_folded_le P s (oldOf ob) hres (ofLanes h0) hr0
    refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun x :
        Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R)) ↦ ∀ q, x q ∈ S) fun x hx ↦ ?_) ?_
    · obtain ⟨h, hh, hr, he, hc⟩ := (Finset.mem_filter.mp hx).2
      have hhh : h = h0 := eq_of_sep_eval P' (newOf ob) s.z hsep hh hh0 (he.trans he0.symm)
      subst hhh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q ↦ Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc q⟩⟩
    · rw [← natCard_subtype_eq_card_filter]
      exact card_positions_le S hS
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h, hh, hr, he, -⟩
    exact hex ⟨h, hh, he, hr⟩

/-! ## The batching challenge -/

/-- The batching of the claims is the batching of their discrepancies' coefficients, in the order
the glued weight batches them: the residual claim, the out-of-domain claim, and the consistency
claims. -/
private theorem powerBatch_glue {t : ℕ} (x₀ x₁ lam : E) (xs : Fin t → E) :
    powerBatch ![x₀, x₁, powerBatch xs lam] lam =
      powerBatch (Fin.cons x₀ (Fin.cons x₁ xs : Fin (t + 1) → E) : Fin (t + 2) → E) lam := by
  have hy : powerBatch xs lam * lam ^ 2 = ∑ q : Fin t, xs q * lam ^ (q.val + 2) := by
    simp only [powerBatch, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ ↦ by ring
  generalize powerBatch xs lam = y at hy ⊢
  simp only [powerBatch, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [show ∑ q : Fin t, xs q * lam ^ (q.val + 1 + 1) = ∑ q : Fin t, xs q * lam ^ (q.val + 2) from
    Finset.sum_congr rfl fun q _ ↦ by ring, ← hy]
  ring

/-- The language after the batching challenge: some codeword near the next word satisfies the
batched claim, whose folded symbols are `cqf`. -/
def BLang (s : Bd sh (Kap sh' κ')) (cqf : Fin sh.t → E) (nw : WordOf sh' κ') : Prop :=
  ∃ h : Msgs sh'.ℓ κ', InNew P' nw h ∧
    (gluedWeight s.resid s.z s.pos s.lam).pair (RingHom.id E) (ofLanes h) =
      powerBatch ![s.c, s.cood, powerBatch cqf s.lam] s.lam

/-- **The batching challenge.** If the language before it does not hold, at most `(t + 1) L`
challenges make some codeword near the next word satisfy the batched claim: each of at most `L`
codewords violates one of the `t + 2` claims, so its batched discrepancy is a nonzero polynomial of
degree below `t + 2` in the challenge. -/
theorem card_batch_bad_le (s : Bd sh (Kap sh' κ'))
    (ob : ∀ i, Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i)
    (hnot : ¬ QLang P P' s ob) :
    Nat.card {x : E // BLang P' { s with lam := x } (cqAt { s with lam := x } (oldOf ob))
      (newOf ob)} ≤ (sh.t + 1) * P'.L := by
  classical
  unfold QLang at hnot
  push Not at hnot
  obtain ⟨-, hall⟩ := hnot
  let Gs := {h : Msgs sh'.ℓ κ' // InNew P' (newOf ob) h}
  have := Fintype.ofFinite (Msgs sh'.ℓ κ')
  have hGs : Nat.card Gs ≤ P'.L := P'.hlist (newOf ob).lanes
  let claims : Msgs sh'.ℓ κ' → Fin (sh.t + 2) → E := fun h ↦
    (Fin.cons (s.resid.pair (RingHom.id E) (ofLanes h)) (Fin.cons (evalMle (ofLanes h) s.z)
      (fun q ↦ encode (algebraMap K E) (Kap sh' κ') sh.R (ofLanes h) (s.pos q)) :
        Fin (sh.t + 1) → E) : Fin (sh.t + 2) → E)
  let target : Fin (sh.t + 2) → E :=
    (Fin.cons s.c (Fin.cons s.cood (cqAt s (oldOf ob)) : Fin (sh.t + 1) → E) :
      Fin (sh.t + 2) → E)
  let d : Gs → Fin (sh.t + 2) → E := fun h i ↦ claims h.1 i - target i
  have hd : ∀ h : Gs, ∃ i, d h i ≠ 0 := by
    intro h
    by_contra hzero
    push Not at hzero
    refine hall ⟨h.1, h.2, ?_, ?_, fun q ↦ ?_⟩
    · exact sub_eq_zero.mp (hzero 0)
    · exact sub_eq_zero.mp (hzero 1)
    · exact sub_eq_zero.mp (hzero q.succ.succ)
  have key := card_batch_exists_zero_le d hd
  have hJ : sh.t + 2 - 1 = sh.t + 1 := by omega
  rw [hJ] at key
  refine le_trans ?_ (key.trans (Nat.mul_le_mul_left _ hGs))
  rw [natCard_subtype_eq_card_filter, natCard_subtype_eq_card_filter]
  refine Finset.card_le_card fun x hx ↦ ?_
  obtain ⟨h, hh, he⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h, hh⟩, ?_⟩
  rw [pair_gluedWeight, powerBatch_glue, powerBatch_glue] at he
  show powerBatch (fun i ↦ claims h i - target i) x = 0
  rw [← powerBatch_sub, sub_eq_zero]
  exact he

/-! ## The relations of the boundary -/

/-- The residual claim's language, with the next word beside the level's. -/
def relResB : Set ((Bd sh (Kap sh' κ') × ∀ i,
    Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) ×
      Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ ResLang P p.1 (oldOf p.2)

/-- The language after `j` coordinates of the out-of-domain point. -/
def relOodJ (j : ℕ) : Set (((Bd sh (Kap sh' κ') × Vector E j) × ∀ i,
    Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) × Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ OodLang P P' p.1.1 p.1.2 p.2

/-- The language after the out-of-domain point, in the record. -/
def relOod : Set ((Bd sh (Kap sh' κ') × ∀ i,
    Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) × Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ OodLang P P' p.1 p.1.z p.2

/-- The language after the positions. -/
def relQ : Set ((Bd sh (Kap sh' κ') × ∀ i,
    Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) × Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ QLang P P' p.1 p.2

/-- The language after the batching challenge, before the old word is read. -/
def relB : Set ((Bd sh (Kap sh' κ') × ∀ i,
    Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ') i) × Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ BLang P' p.1 (cqAt p.1 (oldOf p.2)) (newOf p.2)

/-- The language after the old word is read: the next word is the one oracle, and the folded
symbols are the recorded ones. -/
def relBR : Set ((Bd sh (Kap sh' κ') × ∀ i, Component.keptOracles
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) keepNew i) ×
      Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ BLang P' p.1 p.1.cq (p.2 0)

/-- The language after the query batch's polynomial: the next level's language at its start, with
the glued claim and polynomial. -/
def relP : Set ((Bd sh (Kap sh' κ') × ∀ i, Component.keptOracles
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) keepNew i) ×
      Tab (sh.ℓ + Kap sh' κ')) :=
  Component.indep _ _ _ fun p ↦ FoldLangMid P' 0 (gluedWeight p.1.resid p.1.z p.1.pos p.1.lam)
    (#v[] : Vector E 0) (powerBatch ![p.1.c, p.1.cood, powerBatch p.1.cq p.1.lam] p.1.lam)
    (batchMessage ![p.1.p1, p.1.p2, p.1.p3] p.1.lam) p.2

/-! ## The security of the boundary's steps -/

/-- The commitment of the next word: the message carries nothing into the language. -/
def commitSecurity : Component.Security (commitNext sh sh' κ') (relRes P) (relResB P)
    (Component.sayOError (WordOf sh' κ')) :=
  Component.sendOracleBesideSecurity (OneW sh (Kap sh' κ')) (WordOf sh' κ') _ _
    fun _ _ _ _ h ↦ h

/-- The out-of-domain point, one coordinate at a time, each at `C(L, 2) / |E|`. -/
def pointSecurity : Component.Security (drawPoint sh sh' κ') (relResB P)
    (relOodJ P P' (Kap sh' κ'))
    (drawsError E ((Nat.choose P'.L 2 : ℕ) / (Nat.card E : ℝ≥0)) (Kap sh' κ')) :=
  Component.drawPushesSecurity (S := Bd sh (Kap sh' κ')) (W := Tab (sh.ℓ + Kap sh' κ'))
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) E
    (fun j ↦ relOodJ P P' j) (relResB P) (Kap sh' κ') (Nat.choose P'.L 2)
    (fun s o w h ↦ by
      rcases h with h | h
      · exact h
      · exact absurd (sep_nil P' (newOf o)) h)
    (fun j _ s o ↦ Component.card_badChallenge_le_of_indep _ E _ _ _ _ s o fun hnot ↦ by
      unfold OodLang at hnot
      push Not at hnot
      obtain ⟨hres, hsep⟩ := hnot
      refine le_trans (natCard_subtype_mono fun c hc ↦ ?_) (card_ood_step_le P' (newOf o) s.2 hsep)
      rcases hc with hc | hc
      · exact absurd hc hres
      · exact hc)
    (Kap sh' κ') le_rfl

/-- The out-of-domain answer: the message, recorded with the point, carries nothing into the
language. -/
def oodSecurity : Component.Security (sendOod sh sh' κ') (relOodJ P P' (Kap sh' κ'))
    (relOod P P') (sayError E) :=
  Component.sendCheckedSecurity _ E _ _ _ fun _ _ _ _ _ h ↦ h

/-- The out-of-domain claim's polynomial. -/
def oodPolySecurity : Component.Security (sendOodPoly sh sh' κ') (relOod P P') (relOod P P')
    (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity _ (SumcheckRound.Message E 2) _ _ _ fun _ _ _ _ _ h ↦ h

/-- The grinding nonce. -/
def nonceSecurity : Component.Security (sendNonce (Component.besideOracles
    (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh (Kap sh' κ')) (relOod P P') (relOod P P')
    (sayError E) :=
  Component.sendCheckedSecurity _ E _ _ _ fun _ _ _ _ _ h ↦ h

/-- **The positions**, at `a ^ t / (2 ^ (κ + R)) ^ t`, that is `(1 - γ) ^ t`: if the language before
does not hold, at most `a ^ t` of the choices of the positions let some codeword near the next word
satisfy all the claims. -/
def positionsSecurity : Component.Security (drawPositions (Component.besideOracles
    (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh (Kap sh' κ')) (relOod P P') (relQ P P')
    (drawError (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R)))
      ((P.a ^ sh.t : ℕ) / (Nat.card (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R))) : ℝ≥0))) :=
  Component.sampleChallengeSecurity _ _ _ _ (P.a ^ sh.t) fun s o _ ↦
    Component.card_badChallenge_le_of_indep _ _ _ _ _ _ s o fun hnot ↦
      le_trans (natCard_subtype_mono fun x hx ↦ by
        rcases hx with hx | hx
        · exact absurd hx hnot
        · exact hx) (card_positions_bad_le P P' s o hnot)

/-- **The batching challenge**, at `(t + 1) L / |E|`. -/
def batchingSecurity : Component.Security (drawBatch (Component.besideOracles
    (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh (Kap sh' κ')) (relQ P P') (relB P')
    (drawError E (((sh.t + 1) * P'.L : ℕ) / (Nat.card E : ℝ≥0))) :=
  Component.sampleChallengeSecurity _ _ _ _ ((sh.t + 1) * P'.L) fun s o _ ↦
    Component.card_badChallenge_le_of_indep _ _ _ _ _ _ s o fun hnot ↦
      card_batch_bad_le P P' s o hnot

/-- The reading of the old word: the recorded folded symbols are the folded rows of the old word. -/
def readSecurity : Component.Security (readOld sh sh' κ') (relB P') (relBR P')
    (fun i ↦ Fin.elim0 i.1) :=
  Component.queryRecordSecurity _ keepNew (readQuery sh sh' κ') _ _ fun _ _ _ _ h ↦ h

/-- The query batch's polynomial: the message carries nothing into the language. -/
def queryPolySecurity : Component.Security (sendQueryPoly (Component.keptOracles
    (Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) keepNew) sh (Kap sh' κ'))
    (relBR P') (relP P') (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity _ (SumcheckRound.Message E 2) _ _ _ fun s o w msg _ h ↦ by
    rcases h with ⟨g, hg, hc, -⟩ | hn
    · refine ⟨g, hg, ?_⟩
      rw [← claim_zero] at *
      exact hc
    · exact absurd (foldOK_nil _ _ _ _ _) hn

/-- The glue: the next level's language at its start, with the glued claim, is the language
before. -/
def glueSecurity : Component.Security (glue sh sh' κ') (relP P') (foldRelMid P' 0)
    (fun i ↦ Fin.elim0 i.1) :=
  Component.mapWitnessSecurity _ _ _ (fun _ ↦ Vector.replicate _ 0) fun _ _ _ h ↦ h

end Boundary

end Whir

end

end LeanerVM.Protocol
