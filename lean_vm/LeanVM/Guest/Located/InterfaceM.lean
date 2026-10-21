/-
  LeanVM.Guest.Located.InterfaceM

  What the guest's knowledge soundness over a hash model takes of the B1 groups still converting:
  their callees' soundness over the model, and at the deployed model the deployed lemmas.
-/

module

public import LeanVM.Guest.Located.VerifySubB
public import LeanVM.Guest.B1.Main.AggSoundM

/-!
# The open callees over a hash model

`End.guest_knowledge_model` (`Guest/EndKnowB.lean`) proves the guest's knowledge soundness over
any hash model from the facts below, each the model form (pattern A–E of
`docs/roadmap/w2-guest-model.md`: the relation under `M.sem`, runs answered by the model) of a
deployed lemma `guest_knowledge` uses, owned by a group whose conversion is not merged yet:

| field | deployed lemma | owner |
|---|---|---|
| `batch_sumcheck` | `batch_sumcheck_L22_iff`, `batch_sumcheck_L28_iff` (soundness) | B1 root |
| `gkr` | `verify_bus_gkr_sound` (`SoundGkr`) | Tables |
| `tables` | `verify_tables_sound` (`SoundTables … TCtx`) | Tables |
| `flock` | `verify_flock_sound` (`SoundFlock`) | Tables |
| `open_stacked` | `Located.wOL_spec` (`SoundOpenWC` at the decoded openings) | B1 root + Whir |

The statements are `Main.BatchSumcheckM` (`MeaningBatchSumcheckM`, the B1 root's
`MeaningBatchSumcheckWith` verbatim) and `VerifySub.InterfaceM`'s `SoundGkrM`, `SoundTablesM`,
`SoundFlockM`, `SoundOpenWCM`; the last at the decoded openings `wOLB M.sem L`
(`Located/VerifySubB.lean`), whose proof is `wOL_spec`'s over the model's semantics from the model
forms of the Whir lemmas it composes (`oqFrame_sound`, `oqOpeningOf_ok`,
`opening_queries_frame_w`, `open_stacked_frame_wC`). Every memory field is over the memories
`Main.MemOk` admits (`2^κ` words, `16 ≤ κ ≤ 32`).

`guestHypsM_deployed`: at `HashModel.deployed` every field is its deployed lemma, so the
hypothesis weakens nothing.
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **The open callees of the guest over a hash model**: `batch_sumcheck` (B1 root), GKR, the
tables and Flock (Tables), and `open_stacked` at the decoded openings (B1 root + Whir), each
sound over the model on every memory of a valid execution. -/
structure GuestHypsM (M : HashModel) : Prop where
  /-- `batch_sumcheck__L22`, `__L28` over the model (`batch_sumcheck_L22_model`, …). -/
  batch_sumcheck : ∀ rd, Main.MemOk rd → Main.BatchSumcheckM M rd
  /-- `verify_bus_gkr` over the model. -/
  gkr : ∀ rd, Main.MemOk rd → SoundGkrM M rd
  /-- `verify_tables` over the model, with the terminal's context. -/
  tables : ∀ rd, Main.MemOk rd → SoundTablesM M End.bytecode TCtx rd
  /-- `verify_flock` over the model. -/
  flock : ∀ rd, Main.MemOk rd → SoundFlockM M rd
  /-- `open_stacked`'s located calls over the model, at the decoded openings (`wOL_spec`). -/
  open_stacked : ∀ {κ : ℕ} (L : MemImage κ), 16 ≤ κ → κ ≤ 32 →
    SoundOpenWCM M L.read (RLB M.sem coreProgram L certByName) (wOLB M.sem L)

/-- **At the deployed model every open callee is its deployed lemma.** -/
theorem guestHypsM_deployed : GuestHypsM HashModel.deployed where
  batch_sumcheck rd _ := Main.batchSumcheckM_deployed rd
  gkr rd hm := by
    obtain ⟨κ, -, h32, L, rfl⟩ := hm
    exact soundGkrM_deployed.mpr (verify_bus_gkr_sound h32 L)
  tables rd hm := by
    obtain ⟨κ, -, h32, L, rfl⟩ := hm
    exact soundTablesM_deployed.mpr (verify_tables_sound h32 L End.bytecode_length)
  flock rd _ := soundFlockM_deployed.mpr (verify_flock_sound rd)
  open_stacked L _ _ := by
    show SoundOpenWCM HashModel.deployed L.read (RLB blakeDeployed coreProgram L certByName)
      (wOLB blakeDeployed L)
    rw [rlB_deployed, wOLB_deployed]
    exact soundOpenWCM_deployed.mpr (wOL_spec L)

end
end LeanVM.Guest.Located
