/-
  LeanVM.E2E.Vis.PerKey.Sphincs

  W-vis, P7b: the per-key reduction of T5 for one leanSPHINCS key. It plays leanSPHINCS's
  single-key game, generates every other key itself, and answers their hash inputs from a private
  lazy oracle.
-/

module

public import LeanVM.E2E.Vis.PerKey.Xmss
public import LeanVM.E2E.Reduction.Sphincs

/-!
# The per-key reduction for leanSPHINCS (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/Xmss.lean`.

**The adversary** (`sRedJ j`). Against leanSPHINCS's single-key game
(`Sphincs.Security.Det.gameCoreDet`), it receives key `j`'s public key `pkj`, with parameter `pj`
(16 bytes), and runs the end-to-end game (the game with V_I's trace, in the schemes' world) with
three kinds of hash answers:

* **forwarded by class** (`rcS pj`, `routeImpl (PrivJ pj)`): the adversary's and V_I's queries and
  the other keys' seed and parameter derivations. A query in `PrivJ pj` is answered by the private
  lazy oracle, any other one by the challenger's oracle;
* **private** (`rpS`, `routeImpl (fun _ ↦ True)`): the other keys' trees and signatures, whatever
  their inputs;
* **the challenger's signing oracle**: key `j`'s signing requests, past `signatureLimit` refused as
  in the game (`sphincsFwdJ`).

It outputs, for a forged claim of key `j` with a signature valid under V_I's trace (`SWinAt j`),
that message and signature (`forgeryOfJS`, a classical choice).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

variable {nx ns : ℕ}

/-- The single-key game's world: the schemes' world and key `j`'s signing oracle. -/
abbrev RSs : OracleSpec ((ℕ ⊕ List UInt8) ⊕ Sphincs.Message) := OW + Sphincs.SigningSpec

/-- The reduction's monad: the private oracle's cache over the single-key game's world. -/
abbrev RMs : Type → Type := StateT (QueryCache LeanXmss.HashSpec) (OracleComp RSs)

/-- A public key's parameter, as the 16 bytes its inputs start with. -/
def pjOfS (pk : Sphincs.PublicKey) : Bytes := Sphincs.bytesLE 16 pk.parameter

/-- A computation of the schemes' world, routed by class. -/
noncomputable def rcS (pj : Bytes) {α : Type} (oa : OracleComp OW α) : RMs α :=
  simulateQ (rImpl Sphincs.SigningSpec (PrivJ pj)) oa

/-- A computation of the schemes' world, answered by the private oracle. -/
noncomputable def rpS {α : Type} (oa : OracleComp OW α) : RMs α :=
  simulateQ (rImpl Sphincs.SigningSpec (fun _ ↦ True)) oa

variable [Sphincs.Params]

/-- **A leanXMSS key's generation** (`PerKeyX.xKeygenR` in this world): the seed and the two
derivations routed by class, the tree under the derived parameter private. -/
noncomputable def xKeygenRS (pj : Bytes) : RMs (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) := do
  let seed ← rcS pj (liftM LeanXmss.sampleMasterSeed)
  let S ← rcS pj (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.seedHashInput seed)) :
    OracleComp LeanXmss.HashSpec _))
  let o ← rcS pj (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.keygenHashInput 0 .parameter S)) :
    OracleComp LeanXmss.HashSpec _))
  let root ← rpS (liftM (LeanXmss.Seeded.treeNode (LeanXmss.truncateHash o) LeanXmss.topLayer S
    LeanXmss.layerHeight 0 : OracleComp LeanXmss.HashSpec _))
  pure (⟨root, LeanXmss.truncateHash o⟩, ⟨S, LeanXmss.truncateHash o, root⟩)

/-- **Another leanSPHINCS key's generation** (`PerKeyX.sKeygenR` in this world): the seed and the
two derivations routed by class, the tree under the derived parameter private. -/
noncomputable def sKeygenRS (pj : Bytes) : RMs (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) := do
  let seed ← rcS pj (liftM Sphincs.sampleMasterSeed)
  let S ← rcS pj (sLift (liftM (Sphincs.HashSpec.query (Sphincs.schemeSeedInput seed)) :
    OracleComp Sphincs.HashSpec _))
  let o ← rcS pj (sLift (liftM (Sphincs.HashSpec.query (Sphincs.keygenHashInput 0 .parameter S)) :
    OracleComp Sphincs.HashSpec _))
  let root ← rpS (sLift (Sphincs.Seeded.spineNode (Sphincs.truncateHash o) Sphincs.topLayer
    Sphincs.Concrete.rootTree S (Sphincs.totalHeight - Sphincs.subtreeHeight) :
      OracleComp Sphincs.HashSpec _))
  pure (⟨root, Sphincs.truncateHash o⟩, ⟨S, Sphincs.truncateHash o, root⟩)

/-- **Key `j`'s signing request**: past `signatureLimit` refused; otherwise sent to the
challenger's signing oracle, and the request and its answer recorded (`sphincsSign` with the
signer replaced by the oracle). -/
noncomputable def sphincsFwdJ (j : Fin ns) (msg : Sphincs.Message) :
    StateT (SignState nx ns) RMs (Option Sphincs.Signature) := do
  if Sphincs.signatureLimit ≤ ((← get).slog j).length then return none
  let σ ← (liftM (liftM (liftM (RSs.query (.inr msg)) :
    OracleComp RSs (Option Sphincs.Signature)) : RMs (Option Sphincs.Signature)) :
      StateT (SignState nx ns) RMs (Option Sphincs.Signature))
  modify fun st ↦ { st with slog := Function.update st.slog j (st.slog j ++ [(msg, σ)]) }
  pure σ

/-- **The reduction's answers to the adversary**: coins and hash queries routed by class, key
`j`'s requests to the challenger, the other keys' requests signed privately. -/
noncomputable def advImplJS (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) :
    QueryImpl (AdvSpec nx ns) (StateT (SignState nx ns) RMs)
  | .inl (.inl t) => StateT.mk fun st ↦ rcS pj (tw (advImpl keys (.inl (.inl t))) st)
  | .inl (.inr q) => StateT.mk fun st ↦ rpS (tw (advImpl keys (.inl (.inr q))) st)
  | .inr q =>
    if q.1 = j then sphincsFwdJ j q.2
    else StateT.mk fun st ↦ rpS (tw (advImpl keys (.inr q)) st)

/-- The secret key the reduction places for key `j`: never used, its parameter `pkj`'s (so the
keys' parameters are the game's). -/
def holeKeyS (pkj : Sphincs.PublicKey) : Sphincs.Seeded.SecretKey := ⟨0, pkj.parameter, pkj.root⟩

/-- **The reduction's run after the keys**: the adversary with the reduction's answers, then V_I
recorded and routed by class. -/
noncomputable def restJS (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (pj : Bytes) (j : Fin ns) (keys : Keys nx ns) : RMs (XmssRed.BOut nx ns) := do
  let (sip, st) ← (simulateQ (advImplJS pj j keys)
    (A (fun i ↦ (keys.xmss i).1) (fun i ↦ (keys.sphincs i).1))).run (SignState.init nx ns)
  let (o, st') ← rcS pj (tw (viRec budget guest sip.2 fuel sip.1) st)
  pure (keys, sip.1, sip.2, o, st')

/-- **The reduction's run** with key `j`'s public key `pkj`: the other keys, then the rest. -/
noncomputable def sBodyJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns)
    (pkj : Sphincs.PublicKey) : RMs (XmssRed.BOut nx ns) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ xKeygenRS (pjOfS pkj)
  let ss ← LeanXmss.Concrete.sequenceFin fun i : Fin ns ↦
    if i = j then pure (pkj, holeKeyS pkj) else sKeygenRS (pjOfS pkj)
  restJS guest fuel budget A (pjOfS pkj) j ⟨xs, ss⟩

/-- The game's outcome and V_I's trace of a run of the reduction (`PerKeyX.outJ`). -/
def outJS (r : XmssRed.BOut nx ns) : GameOutcome nx ns × Log :=
  (⟨r.1, r.2.1, r.2.2.1, (r.2.2.2.1.map Prod.fst).getD false, r.2.2.2.2⟩,
    (r.2.2.2.1.map Prod.snd).getD [])

/-- The outcome is leanXMSS's reduction's. -/
theorem outJS_eq_outJ (r : XmssRed.BOut nx ns) : outJS r = PerKeyX.outJ r := rfl

open Classical in
/-- **The reduction's forgery**: the forged claim's message and signature when the run wins
against key `j` (`SWinAt j`), a dummy otherwise. -/
noncomputable def forgeryOfJS (j : Fin ns) (r : XmssRed.BOut nx ns) : Sphincs.Forgery :=
  if h : SWinAt j (outJS r).1 (outJS r).2 then ⟨h.2.choose, h.2.choose_spec.choose⟩
  else ⟨0, SphincsRed.dummySig⟩

/-- **The per-key reduction for leanSPHINCS key `j`.** -/
noncomputable def sRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns) :
    Sphincs.Security.Adversary where
  main pkj := forgeryOfJS j <$> (sBodyJ guest fuel budget A j pkj).run' ∅

end PerKeyS

end
end LeanVM.E2E
