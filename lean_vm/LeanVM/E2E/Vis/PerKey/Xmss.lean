/-
  LeanVM.E2E.Vis.PerKey.Xmss

  W-vis, P7b: the per-key reduction of T5 for one leanXMSS key. It plays leanXMSS's single-key
  game, generates every other key itself, and answers their hash inputs from a private lazy
  oracle.
-/

module

public import LeanVM.E2E.Vis.PerKey.Sim
public import LeanVM.E2E.Reduction.Xmss

/-!
# The per-key reduction for leanXMSS (W-vis, P7b)

**The adversary** (`xRedJ j`). Against leanXMSS's single-key game (`LeanXmss.Security`), it
receives key `j`'s public key `pkj`, with parameter `pj` (16 bytes), and runs the end-to-end game
(the game with V_I's trace, in the schemes' world) with three kinds of hash answers:

* **forwarded by class** (`rc pj`, `routeImpl (PrivJ pj)`): the adversary's and V_I's queries and
  the other keys' seed and parameter derivations. A query in `PrivJ pj` is answered by the private
  lazy oracle, any other one by the challenger's oracle;
* **private** (`rp`, `routeImpl (fun _ ↦ True)`): the other keys' trees and signatures, whatever
  their inputs;
* **the challenger's signing oracle**: key `j`'s signing requests, a used leaf refused as in the
  game (`xmssFwdJ`).

Its forwarded hash queries are at most the adversary's, V_I's budget and two per other key, on
every run.

It outputs, for a forged claim of key `j` with a signature valid under V_I's trace (`XWinAt j`),
that signature (`forgeryOfJ`, a classical choice).

**Its run is the game's** where no other key's parameter is `pj` or zero. There, every other
key's input after its parameter derivation is in `PrivJ pj`, so routing by caller is routing by
class (`Vis/PerKey/Partition.lean`). Key `j`'s generation and signatures make no query in
`PrivJ pj`, so the class-routed game is the game (`evalDistEq_route`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyX

variable {nx ns : ℕ}

/-- The single-key game's world: the schemes' world and key `j`'s signing oracle. -/
abbrev RS : OracleSpec ((ℕ ⊕ List UInt8) ⊕ LeanXmss.SignRequest) := OW + LeanXmss.SigningSpec

/-- The reduction's monad: the private oracle's cache over the single-key game's world. -/
abbrev RM : Type → Type := StateT (QueryCache LeanXmss.HashSpec) (OracleComp RS)

/-- A public key's parameter, as the 16 bytes its inputs start with. -/
def pjOf (pk : LeanXmss.PublicKey) : Bytes := LeanXmss.bytesLE 16 pk.parameter

/-- A computation of the schemes' world, routed by class. -/
noncomputable def rc (pj : Bytes) {α : Type} (oa : OracleComp OW α) : RM α :=
  simulateQ (rImpl LeanXmss.SigningSpec (PrivJ pj)) oa

/-- A computation of the schemes' world, answered by the private oracle. -/
noncomputable def rp {α : Type} (oa : OracleComp OW α) : RM α :=
  simulateQ (rImpl LeanXmss.SigningSpec (fun _ ↦ True)) oa

variable [Sphincs.Params]

/-- **Another leanXMSS key's generation** (`xmss_keygenFromSeed_eq`): the seed and the two
derivations routed by class, the tree under the derived parameter private. -/
noncomputable def xKeygenR (pj : Bytes) : RM (LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) := do
  let seed ← rc pj (liftM LeanXmss.sampleMasterSeed)
  let S ← rc pj (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.seedHashInput seed)) :
    OracleComp LeanXmss.HashSpec _))
  let o ← rc pj (liftM (liftM (LeanXmss.HashSpec.query (LeanXmss.keygenHashInput 0 .parameter S)) :
    OracleComp LeanXmss.HashSpec _))
  let root ← rp (liftM (LeanXmss.Seeded.treeNode (LeanXmss.truncateHash o) LeanXmss.topLayer S
    LeanXmss.layerHeight 0 : OracleComp LeanXmss.HashSpec _))
  pure (⟨root, LeanXmss.truncateHash o⟩, ⟨S, LeanXmss.truncateHash o, root⟩)

/-- **A leanSPHINCS key's generation** (`sphincs_keygenFromSeed_eq`): the seed and the two
derivations routed by class, the tree under the derived parameter private. -/
noncomputable def sKeygenR (pj : Bytes) : RM (Sphincs.PublicKey × Sphincs.Seeded.SecretKey) := do
  let seed ← rc pj (liftM Sphincs.sampleMasterSeed)
  let S ← rc pj (sLift (liftM (Sphincs.HashSpec.query (Sphincs.schemeSeedInput seed)) :
    OracleComp Sphincs.HashSpec _))
  let o ← rc pj (sLift (liftM (Sphincs.HashSpec.query (Sphincs.keygenHashInput 0 .parameter S)) :
    OracleComp Sphincs.HashSpec _))
  let root ← rp (sLift (Sphincs.Seeded.spineNode (Sphincs.truncateHash o) Sphincs.topLayer
    Sphincs.Concrete.rootTree S (Sphincs.totalHeight - Sphincs.subtreeHeight) :
      OracleComp Sphincs.HashSpec _))
  pure (⟨root, Sphincs.truncateHash o⟩, ⟨S, Sphincs.truncateHash o, root⟩)

/-- **Key `j`'s signing request**: a used leaf refused; otherwise sent to the challenger's
signing oracle, and the request and its answer recorded. -/
noncomputable def xmssFwdJ (j : Fin nx) (req : XmssRequest) :
    StateT (SignState nx ns) RM (Option LeanXmss.Signature) := do
  if ((← get).xlog j).any (·.1.1 = req.1) then return none
  let σ ← (liftM (liftM (liftM (RS.query (.inr ⟨req.1, req.2⟩)) :
    OracleComp RS (Option LeanXmss.Signature)) : RM (Option LeanXmss.Signature)) :
      StateT (SignState nx ns) RM (Option LeanXmss.Signature))
  modify fun st ↦ { st with xlog := Function.update st.xlog j (st.xlog j ++ [(req, σ)]) }
  pure σ

/-- **The reduction's answers to the adversary**: coins and hash queries routed by class, key
`j`'s requests to the challenger, the other keys' requests signed privately. -/
noncomputable def advImplJ (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) :
    QueryImpl (AdvSpec nx ns) (StateT (SignState nx ns) RM)
  | .inl (.inl t) => StateT.mk fun st ↦ rc pj (tw (advImpl keys (.inl (.inl t))) st)
  | .inl (.inr q) =>
    if q.1 = j then xmssFwdJ j q.2
    else StateT.mk fun st ↦ rp (tw (advImpl keys (.inl (.inr q))) st)
  | .inr q => StateT.mk fun st ↦ rp (tw (advImpl keys (.inr q)) st)

/-- The secret key the reduction places for key `j`: never used, its parameter `pkj`'s (so the
keys' parameters are the game's). -/
def holeKey (pkj : LeanXmss.PublicKey) : LeanXmss.Seeded.SecretKey := ⟨0, pkj.parameter, pkj.root⟩

/-- **The reduction's run after the keys**: the adversary with the reduction's answers, then V_I
recorded and routed by class. -/
noncomputable def restJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (pj : Bytes)
    (j : Fin nx) (keys : Keys nx ns) : RM (XmssRed.BOut nx ns) := do
  let (sip, st) ← (simulateQ (advImplJ pj j keys)
    (A (fun i ↦ (keys.xmss i).1) (fun i ↦ (keys.sphincs i).1))).run (SignState.init nx ns)
  let (o, st') ← rc pj (tw (viRec budget guest sip.2 fuel sip.1) st)
  pure (keys, sip.1, sip.2, o, st')

/-- **The reduction's run** with key `j`'s public key `pkj`: the other keys, then the rest. -/
noncomputable def xBodyJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx)
    (pkj : LeanXmss.PublicKey) : RM (XmssRed.BOut nx ns) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun i : Fin nx ↦
    if i = j then pure (pkj, holeKey pkj) else xKeygenR (pjOf pkj)
  let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ sKeygenR (pjOf pkj)
  restJ guest fuel budget A (pjOf pkj) j ⟨xs, ss⟩

/-- The game's outcome and V_I's trace of a run of the reduction. -/
def outJ (r : XmssRed.BOut nx ns) : GameOutcome nx ns × Log :=
  (⟨r.1, r.2.1, r.2.2.1, (r.2.2.2.1.map Prod.fst).getD false, r.2.2.2.2⟩,
    (r.2.2.2.1.map Prod.snd).getD [])

open Classical in
/-- **The reduction's forgery**: the forged claim's message and signature when the run wins
against key `j` (`XWinAt j`), a dummy otherwise. -/
noncomputable def forgeryOfJ (j : Fin nx) (r : XmssRed.BOut nx ns) : LeanXmss.Forgery :=
  if h : XWinAt j (outJ r).1 (outJ r).2 then ⟨h.2.choose, h.2.choose_spec.choose⟩
  else ⟨0, XmssRed.dummySig⟩

/-- **The per-key reduction for leanXMSS key `j`.** -/
noncomputable def xRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) :
    LeanXmss.Security.Adversary where
  main pkj := forgeryOfJ j <$> (xBodyJ guest fuel budget A j pkj).run' ∅

end PerKeyX

end
end LeanVM.E2E
