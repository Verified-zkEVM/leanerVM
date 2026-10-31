module

public import Statement.Prover.Run
public import Statement.Prover.Columns
public import Statement.Prover.Ntt
public import Statement.Prover.Bus
public import Statement.Prover.Table
public import Statement.Prover.Public
public import Statement.Prover.Keccak
public import Statement.Prover.Ring
public import Statement.Prover.Whir

/-!
# The honest prover

`LeanVM.Prover.prove F prog input t ρ fuel`: leanVM's honest prover over the permutation `F` in any
monad, Keccak-256 the sponge over `F`. With Keccak-f[1600] in `Id` it is the executable
(`lake exe leanvm-prove`); with the model's permutation (`Common.queryPermutation`) it is the
prover the completeness statements name (`LeanVm.lean`, `LeanVmGuest.lean`).

From the trace it computes the witness (`witness?`: one run of the program; `none` unless the
trace is a valid execution on the input within `2^28` committed cells), and, at a valid rate
`1 ≤ ρ ≤ 4`, runs the honest script against the verifier's own program (`runScript`): the sizes
announced, the stack committed (its codeword by the additive transform, `stackWordFast`), then
the bus (`busFast`), the table sumcheck (`tableFast`), the public input (`pubFast`), the Keccak
reduction (`keccakPhaseProve`), ring switching (`ringFast`) and the stacked opening
(`openingFast`). Otherwise the proof is empty. Its only search is the proof-of-work nonce search,
bounded by `fuel`; nothing branches on a permutation answer except through the
challenges the verifier's program samples.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

/-- **The honest script** of an execution's witness `W` at the layout `layout` and the rate
`ρ`: the eight moves of `verify_execution` (`verifier.py:1463-1516`), each phase's executable
prover. -/
def honestScript (W : Witness) (layout : Layout) (ρ : ℕ) : Script Unit :=
  (Script.sendList (W.announce ρ)).bind fun _ ↦
  (Script.commitS (stackWordFast W.μ ρ W.stack)).bind fun _ ↦
  (busFast layout W.cols).bind fun bus ↦
  (tableFast W.cols layout.tableLogHeights bus).bind fun claims ↦
  (pubFast layout W.cols).bind fun pub ↦
  (KeccakGkr.keccakPhaseProve (layout.tableLogHeights.getD opKeccak 0) W.cols (claims ++ pub)).bind
    fun kr ↦
  (ringFast kr.2.1 kr.2.2).bind fun r ↦
  (openingFast W.μ ρ W.stack (r.claim layout :: kr.1.map (ClaimDesc.column layout))).bind
    fun _ ↦ .ret ()

/-- **leanVM's honest prover.** The proof of the execution `t` of `prog` on `input` at the rate
`2^-ρ`, trying `fuel` nonces per proof of work; `none` for a trace that is no valid execution
within the cap, an invalid rate, or a proof-of-work search that finds no nonce. -/
def prove {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (prog : Program)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : m (Option Proof) :=
  match witness? prog input t with
  | none => pure none
  | some W =>
    if 1 ≤ ρ ∧ ρ ≤ 4 then
      match buildLayout (bytecodeWords prog) W.logMem W.rows with
      | none => pure none
      | some layout => do
        let seed ← seedWith F (bytecodeWords prog) (publicDigest input)
        runScript F (leanVmProgram (bytecodeWords prog) (publicDigest input))
          (honestScript W layout ρ) seed fuel
    else pure none

end LeanVM.Prover

end
