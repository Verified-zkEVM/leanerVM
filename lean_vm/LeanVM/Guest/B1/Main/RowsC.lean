/-
  LeanVM.Guest.B1.Main.RowsC

  What `main`'s completeness over a hash needs of the inline `BLAKE2S` rows and of the batching
  sumchecks: their backward halves, stated over a semantics `S` and an answered hash `H`.
-/

module

public import LeanVM.Guest.B1.Main.HashH
public import LeanVM.Guest.B1.Sumcheck

/-!
# The inline rows over an answered hash

The deployed completeness of `main` and `aggregate_claims` builds its `BLAKE2S` rows from
BLAKE2s itself (`holds_fsNextT`, `holds_fsCompressT`, `holds_squeezeT`, `compress_of_hashPair`)
and runs the batching sumchecks by `batch_sumcheck_L22_iff`. Over a completeness model each is
the converse of its W2 soundness lemma at the model's answers (group B1's hash sites,
`docs/roadmap/t6-completeness.md` §4.2). `FsRowsC S H` collects the three Fiat-Shamir blocks
(`holdsB_fsNextT_comp`, `holdsB_fsCompressT_comp`, `holdsB_squeezeT_comp` of B1's hash sites,
with `obsCvM`, `sqCvM` unfolded to `H`), and the one-block row (`CompModel.check_one`);
`BsRowsC S H` the two batching sumchecks (`batch_sumcheck_L22_comp`, `…_L28_comp`) at the meaning
`MeaningBsC H n` (`MeaningBatchSumcheckComp` with the model's `H`).

They hold over every completeness model (`RowsCModel.lean`: `fsRowsC_model`, `bsRowsC_model`,
from B1's hash sites `Guest/B1/Comp/FsBlocks.lean`, `Comp/Sumcheck.lean`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- **The inline rows over an answered hash**: the Fiat-Shamir blocks `fs_next`, `fs_compress`,
`squeeze` and a one-block hash hold under `S` at the honest values when `H` answers their
strings. -/
structure FsRowsC (S : BlakeSem) (H : List UInt8 → Option Digest) : Prop where
  /-- `fs_next` (`holdsB_fsNextT_comp`). -/
  fsNext : ∀ {C : CallRel} {rd : Reader} {σ : Val} (s0 s1 cur : V) (j b : ℕ) {next : Prop}
    {kret : List E → Prop},
    (LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv d, (σ s0, σ s1) = digestScalars cv ∧
      H (digestBytes cv ++ blockOf (σ (.n b)) 1) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + 1 + k)) = fsValsD (σ (.n b)) d 1 k) ∧ next →
    Stmt.HoldsListB S C rd σ (fsNextT s0 s1 cur j b) next kret
  /-- `fs_compress` (`holdsB_fsCompressT_comp`). -/
  fsCompress : ∀ {C : CallRel} {rd : Reader} {σ : Val} (s0 s1 x : V) (b : ℕ) {tag : ℕ},
    tag < 256 → ∀ {next : Prop} {kret : List E → Prop},
    (∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ H (digestBytes cv ++ blockOf (σ x) tag) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + k)) = fsValsD (σ x) d tag k) ∧ next →
    Stmt.HoldsListB S C rd σ (fsCompressT s0 s1 x b tag) next kret
  /-- `squeeze` (`holdsB_squeezeT_comp`). -/
  squeeze : ∀ {C : CallRel} {rd : Reader} {σ : Val} (s0 s1 : V) (b : ℕ) {next : Prop}
    {kret : List E → Prop},
    (∃ cv d, (σ s0, σ s1) = digestScalars cv ∧ H (digestBytes cv ++ blockOf 0 2) = some d ∧
        ∀ k, k < 14 → σ (.n (b + k)) = sqValsD d k) ∧ next →
    Stmt.HoldsListB S C rd σ (squeezeT s0 s1 b) next kret
  /-- One block from the IV (`CompModel.check_one`): an answered 64-byte string's block checks
  from the IV to the answer, at counter 64 with the flag. -/
  oneBlock : ∀ {m : Fin 4 → E} {d : Digest}, (∀ j, IsCanonical128 (m j)) →
    H (blockBytes m) = some d →
    S.check m ivCells.1 ivCells.2 (digestScalars d).1 (digestScalars d).2 (metadataCell 64 true)

/-- **`batch_sumcheck(n)` over an answered hash** (`MeaningBatchSumcheck`, the rounds the
answered `batchRoundsWith`; B1's `MeaningBatchSumcheckComp` at the model's `H`). -/
def MeaningBsC (H : List UInt8 → Option Digest) (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, msgs, running, point], rets =>
      ∃ cv rounds rs final cv', (s0, s1) = digestScalars cv ∧ rounds.length = n ∧
        (∀ r (hr : r < rounds.length),
          LoadHolds rd msgs (2 * r) rounds[r].1 ∧ LoadHolds rd msgs (2 * r + 1) rounds[r].2) ∧
        (Node.batchRoundsWith (m := Option) H running rounds).run cv = some ((rs, final), cv') ∧
        ReadsAt rd point rs ∧ rets = [(digestScalars cv').1, (digestScalars cv').2, final]
  | _, _ => False

/-- **The batching sumchecks over an answered hash** (`batch_sumcheck_L22_comp`,
`batch_sumcheck_L28_comp`). -/
structure BsRowsC (S : BlakeSem) (H : List UInt8 → Option Digest) : Prop where
  bs22 : ∀ rd args rets, MeaningBsC H 22 rd args rets →
    coreProgram.RelB S rd "batch_sumcheck__L22" args rets
  bs28 : ∀ rd args rets, MeaningBsC H 28 rd args rets →
    coreProgram.RelB S rd "batch_sumcheck__L28" args rets



end
end LeanVM.Guest.B1.Main
