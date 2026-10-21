/-
  LeanVM.E2E.NoForgery

  T5 assembled: the probability that V_I accepts a root statement with a forged claim or an
  unbacked DA claim is at most the chain's bad events, leanXMSS's multi-user bound and
  leanSPHINCS's, at the game's hash-query budget.
-/

module

public import LeanVM.E2E.Reduction.Sphincs
public import LeanVM.E2E.Guest

/-!
# No forgery (T5), assembled

`prEvent_breaks_le`: for a game of the deployed guest whose honest keys, signatures and
adversary are query-bounded (`isQueryBoundP_gameComp`'s hypotheses, `Q` the game's total hash
queries), the probability of `Breaks` (V_I accepts, and the root statement has a forged claim or a
DA claim the final log does not back) is at most `noForgeryError`:

* the chain's bad events (`aggBadError Q`: T1, W6's batching, E5's DA, T3's prediction), which
  cover every unbacked DA claim and every claim not known under the final log;
* leanXMSS's multi-user bound at the reduction's budget `Q + cx` (`cx` the final verification's
  queries), `q/2^127 + n_x²/2^127 + q²/2^252` (`LeanXmss.MultiUser.HasMultiUserSecurity`,
  `q < 2^126`);
* leanSPHINCS's multi-user bound `ε` at `Q + cs` (any `ε` with
  `Sphincs.Security.Multi.HasMultiUserBound n_s ε`; `Sphincs.Lifetimes.requestedMultiUser` gives
  `ε q = n_s · q/2^127`).

The guest's open callees (T2's last facts, `Guest.Located.GuestHypsM` at every oracle model) are
a hypothesis of `prEvent_breaks_le`; `aggregate_no_forgery` discharges it (`guestHypsM_model`).

**The decomposition.** `Breaks` on a log with the bad events is in the first term. On a log
without them, an accepted DA claim is backed (T4 at the final log, through the game-to-cache
bridge `game_accepted`), so a break is a forgery: a leanXMSS one (`prEvent_forgedX_le`) or a
leanSPHINCS one (`prEvent_forgedS_le`), each at most its reduction's multi-user advantage. A
scheme with no honest key has no forgery.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-- **The chain's bad events' error** at `Q` hash queries: T1's (V°'s certificate and the log's
failures), W6's (the batching from the baked start), E5's (DA), T3's (a prediction). -/
noncomputable def aggBadError (Q : ℕ) : ℝ≥0∞ :=
  Q * (εLean + failBound leanVmSeeds Q) + Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) +
    Q * (14 / 2 ^ 192 + 4 * Q / 2 ^ 256) + Q * (Q + 1) / 2 ^ 193

/-- leanXMSS's multi-user bound at `q` hash calls and `n` keys
(`LeanXmss.MultiUser.HasMultiUserSecurity`). -/
noncomputable def xmssMultiError (n q : ℕ) : ℝ≥0∞ :=
  q / ((2 ^ 127 : ℕ) : ℝ≥0∞) + (n ^ 2 : ℕ) / ((2 ^ 127 : ℕ) : ℝ≥0∞) +
    (q ^ 2 : ℕ) / ((2 ^ 252 : ℕ) : ℝ≥0∞)

/-- **The no-forgery error** of the game with `Q` hash queries, `nx` leanXMSS keys, final
verifications of `cx` and `cs` hash queries and leanSPHINCS's multi-user bound `εs`: the chain's
bad events, leanXMSS's multi-user bound at `Q + cx`, leanSPHINCS's at `Q + cs`. -/
noncomputable def noForgeryError (Q nx cx cs : ℕ) (εs : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  aggBadError Q + xmssMultiError nx (Q + cx) + εs (max 1 (Q + cs))

variable {nx ns : ℕ} [Sphincs.Params]

/-- A forgery is a leanXMSS or a leanSPHINCS one. -/
theorem forged_iff (z : GameOutcome nx ns) : Forged z ↔ XmssRed.ForgedX z ∨ SphincsRed.ForgedS z :=
  Iff.rfl

/-- **A break on a good log is a forgery**: on every reachable outcome without the chain's bad
events, an accepted DA claim is backed. -/
theorem forged_of_breaks
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {z : GameOutcome nx ns × Log}
    (hz : z ∈ support (game Guest.guest fuel budget A)) (hb : Breaks z.1 z.2) (hbad : ¬ AggBad z.2) :
    Forged z.1 := by
  obtain ⟨ha, hf | ⟨c, hc, hnb⟩⟩ := hb
  · exact hf
  · exact absurd ((aggregate_knowledge_cache (hG z.2) hbad (game_accepted hz ha)).2.2 c hc) hnb

/-- The leanXMSS part of a break is at most leanXMSS's multi-user bound at the reduction's
budget. -/
theorem prEvent_forgedX_le_bound
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity) (fuel budget : ℕ) (A : GameAdversary nx ns)
    {Q cx : ℕ} (hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hq : Q + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ XmssRed.ForgedX z.1 ∧
      ¬ AggBad z.2] ≤ xmssMultiError nx (Q + cx) := by
  rcases Nat.eq_zero_or_pos nx with rfl | hnx
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0
  · have : NeZero nx := ⟨hnx.ne'⟩
    exact (XmssRed.prEvent_forgedX_le hG fuel budget A).trans
      (hxmss nx (Q + cx) hq _ (XmssRed.hasHashQueryBound_xAdv hQ hvx))

/-- The leanSPHINCS part of a break is at most leanSPHINCS's multi-user bound at the reduction's
budget. -/
theorem prEvent_forgedS_le_bound
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ SphincsRed.ForgedS z.1 ∧
      ¬ AggBad z.2] ≤
      εs (max 1 (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs)) := by
  rcases Nat.eq_zero_or_pos ns with rfl | hns
  · refine le_trans (le_of_eq ?_) zero_le
    exact prEvent_eq_zero_of_forall_not _ _ fun z h ↦ by obtain ⟨-, ⟨j, -⟩, -⟩ := h; exact j.elim0
  · have : NeZero ns := ⟨hns.ne'⟩
    refine (SphincsRed.prEvent_forgedS_le hG fuel budget A).trans (hsph _ (le_max_left _ _) _ ?_)
    intro r hr
    exact (SphincsRed.hasHashQueryBound_sAdv hxk hsk hxs hss hvs Guest.guest fuel budget A hH hX
      hS r hr).trans (le_max_right _ _)

/-- **No forgery (T5), with the guest's open callees as a hypothesis.** For the game of the
deployed guest with an adversary making at most `qH` hash queries, `sX` leanXMSS and `sS`
leanSPHINCS signing requests, honest key generations and signatures of at most `cxk`, `csk`,
`cxs`, `css` hash queries, final verifications of at most `cx` and `cs`, and `Q` the game's total
hash queries (`isQueryBoundP_gameComp`): if leanXMSS has its multi-user security, leanSPHINCS
the multi-user bound `εs`, and `Q + cx < 2^126`, then V_I accepting a root statement with a
forged claim or an unbacked DA claim has probability at most `noForgeryError Q nx cx cs εs`. -/
theorem prEvent_breaks_le
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx cx cs εs := by
  set Q := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget
  have hQ : IsQueryBoundP (gameComp Guest.guest fuel budget A) IsHash Q :=
    isQueryBoundP_gameComp hxk hsk hxs hss Guest.guest fuel budget A hH hX hS
  set g := game Guest.guest fuel budget A
  have e : Pr{let z ← g}[Breaks z.1 z.2] ≤ Pr{let z ← g}[(AggBad z.2 ∨
      (z.1.accepted = true ∧ XmssRed.ForgedX z.1 ∧ ¬ AggBad z.2)) ∨
      (z.1.accepted = true ∧ SphincsRed.ForgedS z.1 ∧ ¬ AggBad z.2)] :=
    prEvent_mono_of_support _ _ _ fun z hz hb ↦ by
      by_cases hbad : AggBad z.2
      · exact Or.inl (Or.inl hbad)
      · rcases (forged_iff z.1).mp (forged_of_breaks hG hz hb hbad) with hf | hf
        · exact Or.inl (Or.inr ⟨hb.1, hf, hbad⟩)
        · exact Or.inr ⟨hb.1, hf, hbad⟩
  refine e.trans ((prEvent_or_le _ _ _).trans (add_le_add ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ ?_)) ?_))
  · exact prEvent_game_aggBad_le fuel budget A Q hQ
  · exact prEvent_forgedX_le_bound hG hxmss fuel budget A hQ hvx hq
  · exact (prEvent_forgedS_le_bound hG hsph hxk hsk hxs hss hvs fuel budget A hH hX hS).trans
      (le_of_eq (by rw [show nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs =
        Q + cs from rfl]))

/-- **No forgery (T5), the end theorem.** For the game of the deployed guest with an adversary
making at most `qH` hash queries, `sX` leanXMSS and `sS` leanSPHINCS signing requests, honest key
generations and signatures of at most `cxk`, `csk`, `cxs`, `css` hash queries and final
verifications of at most `cx` and `cs`: if leanXMSS has its multi-user security, leanSPHINCS the
multi-user bound `εs`, and the game's hash queries `Q = nx·cxk + ns·csk + (qH + sX·cxs + sS·css) +
budget` satisfy `Q + cx < 2^126`, then V_I accepting a root statement with a forged claim of an
honest key or a DA claim the oracle's final log does not back has probability at most
`noForgeryError Q nx cx cs εs`. -/
theorem aggregate_no_forgery
    (hxmss : LeanXmss.MultiUser.HasMultiUserSecurity)
    {εs : ℕ → ℝ≥0∞} (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs)
    {cxk csk cxs css cx cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cx < 2 ^ 126) :
    Pr{let z ← game Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx cx cs εs :=
  prEvent_breaks_le (fun _ _ _ ↦ guestHypsM_model _) hxmss hsph hxk hsk hxs hss hvx hvs fuel
    budget A hH hX hS hq

end
end LeanVM.E2E
