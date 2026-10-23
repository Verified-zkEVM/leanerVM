/-
  LeanerVM.Protocol.Prove.Compiled

  The compiled protocol's honest prover with prover-only state: the bus phase and the table
  sumcheck cached over the committed word, every other component its honest prover; proved to
  run as the honest prover of the list-binding compilation.
-/

module

public import LeanerVM.Protocol.ListBinding
public import LeanerVM.Protocol.HonestProver
public import LeanerVM.Protocol.Whir.Cached
public import LeanerVM.Protocol.Whir.WordFast

/-!
# The compiled protocol's honest prover

The compiled protocol is the list-binding compilation `listBindingDef`: the level-0 word
committed, the front phases and the opening's batching over it, the opening's input, and WHIR's
opening. A front phase over the word runs its honest prover on the stack the witness holds
(`Phase.FrontDef.over`), and a cached prover of the phase runs over the word likewise
(`Component.Cached.over`, `LeanerVM.Protocol.ListBinding`), so the cached bus phase, table
sumcheck and Flock phase of `LeanerVM.Protocol.HonestProver` carry over to the compiled
protocol.

`listBindingCached` is the cached prover of the whole compilation: the level-0 word's rows encoded
once by the transform and the word reading them sent (`commitWordCached`, on `κ + R ≤ 64`
positions' bits, which every deployed level has), the cached bus phase, table sumcheck and Flock
phase over the word, WHIR's cached opening (`Whir.whirOpenCached`), and the honest provers of the
public-input check, the batching and the opening's input. **`compiledProver_run`**: the run of
its prover, `compiledProver`, is the run of the compilation's honest prover, on every statement,
stack and challenge sequence. No definition or statement of the protocol changes.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec Whir

@[expose] public section

/-! ## The compiled protocol's cached prover -/

variable (I : M3Instance) (h : Bus.Conditions I) {sh : Whir.Shape} {κ : ℕ} (hμ : κ + sh.ℓ = I.μ)
  (L : Ladder sh κ) (hb : κ + sh.R ≤ 64)

/-- The commitment of the level-0 word read off a cache holding its rows. -/
def commitWordRowsCached : Component.Cached (commitWord I hμ)
    (fun p ↦ kwordRows sh.ℓ κ sh.R (hμ.symm ▸ p.2.values)) (fun _ ↦ ()) := by
  unfold commitWord
  exact Component.Cached.sendEncoded (msg := fun _ rows ↦ KWord.ofRows rows)
    fun p ↦ ofRows_kwordRows hb _

/-- The commitment of the level-0 word, its rows encoded once by the transform from the stack
when the step starts, the word reading them sent and handed on. -/
def commitWordCached : Component.Cached (commitWord I hμ) (fun _ ↦ ()) (fun _ ↦ ()) :=
  (commitWordRowsCached I hμ hb).adaptIn
    (fun p _ ↦ kwordRows sh.ℓ κ sh.R (hμ.symm ▸ p.2.values)) fun _ ↦ rfl

/-- **The compiled protocol's cached prover**: the commitment, the bus phase, the table
sumcheck, the Flock phase and WHIR's opening cached, the public-input check, the batching and the
opening's input their honest provers. -/
def listBindingCached :
    Component.Cached (listBindingDef (leanVmPhases I h) hμ L) (fun _ ↦ ()) (fun _ ↦ ()) :=
  (((((((commitWordCached I hμ hb).append
    ((Bus.busCached I h).over (KOracle sh κ))).append
    ((TableSumcheck.tableCached I).over (KOracle sh κ))).append
    (Component.Cached.ofDef ((leanVmPhases I h).pub.over I (KOracle sh κ)))).append
    ((flockCached I).over (KOracle sh κ))).append
    (Component.Cached.ofDef (openingBatchOver I (KOracle sh κ)))).append
    (Component.Cached.ofDef (openInput I hμ))).append (whirOpenCached sh κ L)

/-- The compiled protocol's prover with its state. -/
def compiledProver :
    OracleProver []ₒ I.Stmt NoOracle (Column I.μ) Unit (OneW L.finShape L.finN) Unit
      (listBindingSpec I sh κ L) :=
  (listBindingCached I h hμ L hb).toProver

/-- **The prover with state is the compiled protocol's honest prover**: on every statement and
stack, its run is the run of `listBindingDef`'s prover. -/
theorem compiledProver_run (s : I.Stmt × ∀ i, NoOracle i) (w : Column I.μ) :
    (compiledProver I h hμ L hb).run s w =
      (listBindingDef (leanVmPhases I h) hμ L).red.prover.run s w :=
  (listBindingCached I h hμ L hb).toProver_run s w

end
end LeanerVM.Protocol
