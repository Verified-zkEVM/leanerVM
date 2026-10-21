/-
  LeanVM.Guest.Located.VerifySubB

  The child proof `verify_sub` checks, decoded from the memory under any semantics of `BLAKE2S`,
  and accepted over a hash model (`Located/VerifySub.lean` over `S` and a `HashModel`).
-/

module

public import LeanVM.Guest.Located.DaB
public import LeanVM.Guest.Located.VerifySub
public import LeanVM.Guest.B1.VerifySub.SoundWM

/-!
# The child proof, located, under any semantics

`Located/VerifySub.lean`'s decoders with the frames under `S` (`frameDecB S`, `loopDecB S`):
`wlLB`, `wqDecB`, `wqLB`, `wOLB` (the stacked openings) and `wVsLB` (the child proof), each the
deployed one at `blakeDeployed` (`wOLB_deployed`, `wVsLB_deployed`).

`vsWit_outM`: a located call of `verify_sub` under the model's semantics accepts the decoded proof
over the model (`verifyDeferredWith M.H … = some true`), by `verify_sub_sound_wCM`, given the
hashing callees' soundness over the model: GKR, the tables and Flock (`SoundGkrM`,
`SoundTablesM`, `SoundFlockM`, the Tables group's), and `open_stacked` at the decoded openings
(`SoundOpenWCM … (wOLB M.sem L)`, the B1 root's: the deployed `wOL_spec` over the model, from the
model forms of `oqFrame_sound`, `oqOpeningOf_ok`, `opening_queries_frame_w` and
`open_stacked_frame_wC`). The hash-free callees (placement, kappas, the terminal) are the deployed
lemmas.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The empty opening, the decoders' default. -/
local instance : Inhabited Opening := ⟨⟨[], []⟩⟩

variable (S : BlakeSem)

/-- The loop's openings, decoded under `S` (`wlL`). -/
noncomputable def wlLB {κ : ℕ} (L : MemImage κ) (base I blocks pd cd : ℕ) (loop : String) :
    List E → List E → List Opening :=
  loopDecB S L loop (fun ps => ps.getD 0 0) (oqOpeningOf base I blocks pd cd L.read)

/-- A specialization of `opening_queries`' openings, decoded under `S` (`wqDec`). -/
noncomputable def wqDecB {κ : ℕ} (L : MemImage κ) (name loop : String) (base I blocks pd cd : ℕ)
    (args rets : List E) : List Opening :=
  frameDecB S L name (fun σ => oqQueriesOs (wlLB S L base I blocks pd cd loop) σ) args rets

/-- Level `i`'s `opening_queries` openings, decoded under `S` (`wqL`). -/
noncomputable def wqLB {κ : ℕ} (L : MemImage κ) (cfg : OsCfg) (i : ℕ) (args rets : List E) :
    List Opening :=
  match oqLookup (cfg.lv i).queriesFn with
  | some (loop, base, I, blocks, pd, cd) =>
      wqDecB S L (cfg.lv i).queriesFn loop base I blocks pd cd args rets
  | none => []

/-- **`open_stacked`'s openings, decoded under `S`** (`wOL`). -/
noncomputable def wOLB {κ : ℕ} (L : MemImage κ) (name : String) (args rets : List E) :
    List Opening :=
  frameDecB S L name (fun σ => osOsOf (osCfgOf name) σ (wqLB S L (osCfgOf name))) args rets

/-- **`verify_sub`'s child proof, decoded under `S`** (`wVsL`). -/
noncomputable def wVsLB {κ : ℕ} (L : MemImage κ) (args rets : List E) : Proof :=
  frameDecB S L "verify_sub" (fun σ => vsProofOf End.bytecode L.read σ (wOLB S L)) args rets

variable {S}

/-! ## At the deployed semantics -/

theorem wOLB_deployed {κ : ℕ} (L : MemImage κ) : wOLB blakeDeployed L = wOL L := by
  have hl : wlLB blakeDeployed L = wlL L := by
    funext base I blocks pd cd loop
    simp only [wlLB, wlL, loopDecB_deployed]
  have hq : wqDecB blakeDeployed L = wqDec L := by
    funext name loop base I blocks pd cd args rets
    simp only [wqDecB, wqDec, frameDecB_deployed, hl]
  have hqL : wqLB blakeDeployed L = wqL L := by
    funext cfg i args rets
    unfold wqLB wqL
    rw [hq]
    split <;> rename_i h <;> rw [h]
  funext name args rets
  simp only [wOLB, wOL, frameDecB_deployed, hqL]

theorem wVsLB_deployed {κ : ℕ} (L : MemImage κ) : wVsLB blakeDeployed L = wVsL L := by
  funext args rets
  simp only [wVsLB, wVsL, frameDecB_deployed, wOLB_deployed]

/-! ## Over a hash model -/

variable {M : HashModel}

set_option maxRecDepth 100000 in
/-- **A located call of `verify_sub` under the model's semantics accepts the decoded proof over the
model** (`vsWit_out`): on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables, given
the hashing callees' soundness over the model (GKR, the tables with the terminal's context, Flock,
and `open_stacked` at the decoded openings), the cells are a public input and an IV, and the
deferring verifier accepts `wVsLB M.sem L args []` for them over the model with claims of the
guest's shape at `defer_out`. -/
theorem vsWit_outM {κ : ℕ} {L : MemImage κ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ)
    (hgkr : SoundGkrM M L.read) (htab : SoundTablesM M End.bytecode TCtx L.read)
    (hfl : SoundFlockM M L.read)
    (hop : SoundOpenWCM M L.read (RLB M.sem coreProgram L certByName) (wOLB M.sem L))
    {pi0 pi1 s0 s1 glp gsq out : E} (ht : ExpTables L.read glp gsq)
    (h : RLB M.sem coreProgram L certByName "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] []) :
    ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
      (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh
        (wVsLB M.sem L [pi0, pi1, s0, s1, glp, gsq, out] []) = some true := by
  have key : ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
      (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh
        (wVsLB M.sem L [pi0, pi1, s0, s1, glp, gsq, out] []) = some true := by
    unfold wVsLB
    refine frameDecB_spec (t := fun π => ∃ (pi iv : Digest) (fresh : FixedClaims),
      (pi0, pi1) = digestScalars pi ∧ (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧
      ReadsAt L.read out (Node.fixedCells fresh) ∧
      verifyDeferredWith M.H End.bytecode iv pi fresh π = some true) find_verify_sub h
      fun a hp hb => ?_
    rw [core15_params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, -⟩ := hp
    rw [core15_body, holdsListB_append, holdsListB_noRet _ vsPre_noRet] at hb
    have hvC : VsHoldsCB M.sem (RLB M.sem coreProgram L certByName) L.read (valAt L "verify_sub" a) :=
      hb.1
    have ht' : ExpTables L.read (valAt L "verify_sub" a (.n 4)) (valAt L "verify_sub" a (.n 5)) := by
      rw [e4, e5]; exact ht
    obtain ⟨hpi, hseed, hsh, hout, hacc⟩ := verify_sub_sound_wCM hκ hκ6 L (relLB_le_rel coreProgram)
      End.bytecode_length hgkr htab hfl (soundPlace hκ L) (hypKappa _) hop
      (check_opening_terminal_sound _) hvC ht'
    refine ⟨_, _, _, ?_, ?_, hsh, ?_, hacc⟩
    · rw [← e0, ← e1]; exact hpi
    · rw [← e2, ← e3]; exact hseed
    · rw [← e6]; exact hout
  exact key

end
end LeanVM.Guest.Located
