/-
  LeanVM.E2E.Vis.Rank

  W-vis: T3's conclusion for the guest on a log, as a predicate (`RankOK`). T4 at V_I's trace
  (`Vis/Knowledge.lean`) takes it as a hypothesis; T3 restricted (`Vis/Pred.lean`) proves it.
-/

module

public import LeanVM.E2E.Termination
public import LeanVM.Guest.B1.Main.AggSoundM

/-!
# T3's conclusion as a hypothesis (W-vis)

`rank_lt_of_child` (`LeanVM.E2E.Termination`) gives T4's induction its measure: a child's digest is
answered before its parent's. Its hypothesis `¬ Pred` fails on the visible accounting
(decision E2E-6), where T3 holds only off the hidden entries (`PredS`). `RankOK ℓ` is its
conclusion for the guest (the Fiat-Shamir seed of the guest's bytecode, the batching from the
guest's baked start `aggSeedD`, the offset of the guest's last matrix coordinate), so that T4 can
be stated without fixing which form of T3 provides it. `RankOK2 ℓ` asks it only at the guest's
shape (`2 · blake2sR1csLogSize` matrix coordinates), all T4 needs; `RankOK` gives it.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-- **T3's conclusion for the guest on the log `ℓ`**: for a parent's statement bytes of the
guest's shape, answered by `pi` and deferring a claim the batching from the guest's start made
of children `cs`, every child whose public input `ℓ` answers is answered before `pi`. -/
def RankOK (ℓ : Log) : Prop :=
  ∀ {seed sd dd pi : Digest} {d : DeferredClaim} {cs : List ChildClaims} {h : BatchHints}
    {c : ChildClaims} {i p : ℕ},
    96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) =
      predOffset (bytecodeWords Guest.guest) →
    fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed →
    look ℓ (stmtInput seed sd dd d) = some pi → d.matrixPoint ≠ [] →
    batchWith (look ℓ) Guest.B1.Main.aggSeedD cs h = some (some d) → c ∈ cs →
    ∀ (hi : i < ℓ.length) (hp : p < ℓ.length), ℓ[i].2 = c.publicInput → ℓ[p].2 = pi → i < p

/-- **T3's conclusion for the guest at the guest's shape**: `RankOK`, for parents whose matrix
point has the guest's `2 · blake2sR1csLogSize` coordinates (`DeferredClaim.Shaped`). T4 at the
trace needs no more (`Vis/Knowledge.lean`), and the two-challenge form of T3 gives it
(`Vis/Pred2.lean`). -/
def RankOK2 (ℓ : Log) : Prop :=
  ∀ {seed sd dd pi : Digest} {d : DeferredClaim} {cs : List ChildClaims} {h : BatchHints}
    {c : ChildClaims} {i p : ℕ},
    96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) =
      predOffset (bytecodeWords Guest.guest) →
    d.matrixPoint.length = 2 * blake2sR1csLogSize →
    fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed →
    look ℓ (stmtInput seed sd dd d) = some pi → d.matrixPoint ≠ [] →
    batchWith (look ℓ) Guest.B1.Main.aggSeedD cs h = some (some d) → c ∈ cs →
    ∀ (hi : i < ℓ.length) (hp : p < ℓ.length), ℓ[i].2 = c.publicInput → ℓ[p].2 = pi → i < p

/-- `RankOK` gives its form at the guest's shape. -/
theorem RankOK.toRankOK2 {ℓ : Log} (h : RankOK ℓ) : RankOK2 ℓ :=
  fun ho _ hs hpi hm hbw hc hi hp hci hpp ↦ h ho hs hpi hm hbw hc hi hp hci hpp

end
end LeanVM.E2E
