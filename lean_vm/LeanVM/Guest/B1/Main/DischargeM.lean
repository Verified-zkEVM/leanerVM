/-
  LeanVM.Guest.B1.Main.DischargeM

  `main`'s callees without a hash witness over a hash model, from the other groups' model lemmas
  (`Discharge.lean` over a `HashModel`): the digests, the claim lists, the DA root list and cover,
  the exponent tables.
-/

module

public import LeanVM.Guest.B1.Main.CalleesWM
public import LeanVM.Guest.B1.Main.Discharge
public import LeanVM.Guest.B1.Digest.ChildListM
public import LeanVM.Guest.B1.Da.ListDigestM
public import LeanVM.Guest.B1.ExpKnownB

/-!
# `main`'s callees over a hash model, discharged

Each is the owning group's model lemma restated in `CalleesWM`'s shape, for any call relation
below the program's under `M.sem`:

* `statement_digest`, `claim_list_digest`, `child_claim_list_digest`, `da_list_digest`: the
  Digest + Da group's `statement_digest_model`, `claim_list_digest_model`,
  `child_claim_list_digest_model`, `da_list_digest_model`;
* `cover_da_root`, `exponent_tables`: free of `BLAKE2S`, their deployed lemmas under every
  semantics (`Core.relB_iff_rel_of_freeOn`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {M : HashModel} {rd : Reader} {C : CallRel}

theorem statement_digest_soundM (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ seed0 seed1 sigp da0 da1 dp d0 d1,
      C "statement_digest" [seed0, seed1, sigp, da0, da1, dp] [d0, d1] →
      ∃ (seed sig da : Digest) (cells : List E), cells.length = 53 ∧
        (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
        LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
        ReadsAt rd dp cells ∧
        ∃ pi, Digest.stmtDigestOfWith M.H seed sig da cells = some pi ∧
          (d0, d1) = digestScalars pi := by
  intro seed0 seed1 sigp da0 da1 dp d0 d1 h
  obtain ⟨_, _, _, _, _, _, _, _, ha, hr, seed, sig, da, cells, h1, h2, h3, h4, h5, h6, pi, h7,
    h8⟩ := Digest.statement_digest_model rd _ _ (hC _ _ _ h)
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨seed, sig, da, cells, h1, h2, h3, h4, h5, h6, pi, h7, h8⟩

theorem claim_list_digest_soundM (hm : MemOk rd) (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ p n_g gsq d0 d1, SquaresTable rd gsq → C "claim_list_digest" [p, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ cs : List E, cs.length = 4 * n ∧ ReadsAt rd p cs ∧
        ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d := by
  intro p n_g gsq d0 d1 hT h
  obtain ⟨_, _, _, _, _, ha, hr, n, hn, hng, cs, hl, hc, -, d, hd, hdd⟩ :=
    Digest.claim_list_digest_model (memOk_digest hm) (squaresAt_of_table hT) _ _ _ (hC _ _ _ h)
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨n, hn, hng, cs, hl, hc, d, hd, hdd⟩

theorem child_claim_list_digest_soundM (hm : MemOk rd)
    (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ entries cover base origin limit n_g gsq d0 d1, SquaresTable rd gsq →
      C "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧
        ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d := by
  intro entries cover base origin limit n_g gsq d0 d1 hT h
  obtain ⟨_, _, _, _, _, _, _, _, _, ha, hr, n, hn, hng, off, cs, hl, hc, -, d, hd, hdd⟩ :=
    Digest.child_claim_list_digest_model (memOk_digest hm) (squaresAt_of_table hT) (hC _ _ _ h)
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨n, hn, hng, off, cs, hl, hc, d, hd, hdd⟩

theorem da_list_digest_soundM (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ roots n_g d0 d1, C "da_list_digest" [roots, n_g] [d0, d1] →
      ∃ claims : List DaClaim, claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧
        DaClaimsAt rd roots claims ∧
        ∃ d, daListDigestWith M.H claims = some d ∧ (d0, d1) = digestScalars d := by
  intro roots n_g d0 d1 h
  obtain ⟨_, _, _, _, ha, hr, claims, h1, h2, h3, d, h4, h5⟩ :=
    Digest.da_list_digest_model rd _ _ (hC _ _ _ h)
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨claims, h1, h2, h3, d, h4, h5⟩

/-- `cover_da_root` is free of `BLAKE2S` and calls nothing. -/
theorem freeOn_cover_da_root : coreProgram.FreeOn ["cover_da_root"] = true := by decide +kernel

theorem cover_da_root_soundM (hm : MemOk rd) (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ roots cover nslots mark r0 r1 r2 r3,
      C "cover_da_root" [roots, cover, nslots, mark] [r0, r1, r2, r3] →
      ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := fun _ _ _ _ _ _ _ _ h =>
  cover_da_root_sound' hm _ _ _ _ _ _ _ _
    ((relB_iff_rel_of_freeOn freeOn_cover_da_root (List.mem_singleton_self _) _ _).mp (hC _ _ _ h))

theorem exponent_tables_soundM (hC : CallRel.Le C (coreProgram.RelB M.sem rd)) :
    ∀ p q, C "exponent_tables" [] [p, q] → ExpTables rd p q := fun _ _ h =>
  B1.expKnownB M.sem rd _ _ (hC _ _ _ h)

end
end LeanVM.Guest.B1.Main
