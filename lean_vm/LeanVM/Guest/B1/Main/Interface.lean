/-
  LeanVM.Guest.B1.Main.Interface

  The interface of B1 for `main` and `aggregate_claims`: what the batching of the children
  computes, what `main` asks of its callees, the decoders of the seed, the statement and the
  witness, and the statement that `main`'s run establishes `NodeRel` of what they decode.
-/

module

public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Sig.Interface

/-!
# `main` and `aggregate_claims`: meanings (TRIAGE G #96, #97)

**`aggregate_claims`** (G:4285-4392, `core31`): from the batching seed (`AGG_SEED_*`), the
duplex sponge absorbs the children's count and every child's words, squeezes two coefficients per
child, and one sumcheck (`batch_sumcheck`) reduces the children's claims on the bytecode to the
claim written at `defer_stmt`: `Node.batch` (N:272) of the children whose words the memory holds
(`ChildWordsAt`) returns that claim, for the hints `bc_sumcheck_msgs`, `bc_star_hint`
(`MeaningAggregateClaims`).

**`main`** (G:4086-4282, `core0`). Its callees with a witness, each through a witness function of
the call's words (`CalleesW`): a leanXMSS signature `wX p` for the claim at `p`
(`verify_lean_xmss`, `Sig.XmssOut`), a leanSPHINCS signature `wS p` (`verify_sig_lean_sphincs`,
`Sig.SphincsOut`, with the byte table), a matrix `wD args rets` (`da_verify`, `Da.Witness.Opens`),
a child's proof `wV args` (`verify_sub`: `verifyDeferred` of the child's public input under the
seed, its fresh claim at the call's pointer, `VerifySubOut`), and the batching's hints
`wA args` (`aggregate_claims`). The function's other callees are the deterministic functions
whose `…_Spec`s are stated in `Digest/Interface`, `Da/Interface`, `Bits/Meaning` (B1-a's
`exponent_tables`) and here.

**The decoders** read `main`'s valuation and the memory:
* `decSeed σ`: the seed `fs_seed`;
* `decStmt σ rd`: the claims of the declared prefixes of the leanXMSS and leanSPHINCS tables
  (`Sig.xmssClaimOf`, `Sig.sphincsClaimOf`), the declared DA claims at `da_roots`, the deferred
  claim at `defer_stmt`;
* `decWit σ rd wX wS wD wV wA`: the children (child `c`'s statement read off the coverage table:
  its claims are the slots whose marks run from its base `written[c]`, `kidStmt`; its fresh
  claim at `child_fresh · g^(24c)`; its proof `wV` at its `verify_sub` call's words); for every
  declared claim a holder by the mark in its slot (`markOf`): a raw writer's (below `n_raw_x`,
  `n_raw_x + n_raw_s`, `+ n_direct_da`) holds it directly, a child's the child whose segment of
  the running counts holds the mark (`kidOf`); and the batching's hints `wA`.

**The statement** (`main_sound_Spec`): on a memory image, given the callees' contracts, a run of
`main`'s body whose public input cells hold the digest `D` gives `statementDigest (decSeed σ)
(decStmt σ rd) = D` and `NodeRel bytecode (decSeed σ) (decStmt σ rd) (decWit …)`. Its proof,
`main_sound_w`, composes the `…_Spec`s of every family.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Reading the memory -/

/-- The exponent of a power of `g` below `2^34` (`0` for other words). -/
@[irreducible] noncomputable def gLog (x : E) : ℕ := ((gLog? 34 (x.limb 0)).map Fin.val).getD 0

/-- The digest of two cells, their low limbs its four words (`digestOfScalars`, unchecked). -/
def digestOfCells (a b : E) : Digest :=
  #v[(a.limb 0).lane, (a.limb 1).lane, (b.limb 0).lane, (b.limb 1).lane]

/-- The word at `p · g^k`, or `0`. -/
noncomputable def cellAt (rd : Reader) (p : E) (k : ℕ) : E :=
  (rd (p.limb 0 * Parameters.gpow k)).getD 0

/-- The `n` words from `p`. -/
noncomputable def readCells (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (cellAt rd p)

/-- `BYTECODE_VARS`. -/
abbrev bytecodeVars : ℕ := 23

/-- A deferred claim of its `24` cells: the point, then the value. -/
def deferOfCells (cs : List E) : DeferredClaim := ⟨cs.take bytecodeVars, cs.getD bytecodeVars 0⟩

/-- A proof's claim on the bytecode of its `24` cells (`defer_out`). -/
def fixedOfCells (cs : List E) : FixedClaims := ⟨cs.take bytecodeVars, cs.getD bytecodeVars 0⟩

/-! ## `aggregate_claims` (G:4285-4392, TRIAGE #97) -/

/-- **Child `c`'s words in memory**: its public input's two cells at `child_pi · g^(2c)`, its
proof's claim at `child_fresh · g^(24c)`, its statement's deferred claim at
`child_carried · g^(24c)`, both claims at `23` coordinates. -/
def ChildWordsAt (rd : Reader) (cpi cfresh ccarried : E) (c : ℕ) (cc : ChildClaims) : Prop :=
  cc.fresh.bytecodePoint.length = bytecodeVars ∧ cc.carried.bytecodePoint.length = bytecodeVars ∧
    LoadHolds rd cpi (2 * c) (digestScalars cc.publicInput).1 ∧
    LoadHolds rd cpi (2 * c + 1) (digestScalars cc.publicInput).2 ∧
    ReadsAt rd (cfresh * gen ^ (24 * c)) (DeferredClaim.cells cc.fresh) ∧
    ReadsAt rd (ccarried * gen ^ (24 * c)) cc.carried.cells

/-- **`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)`**, for
`n_children_g = g^m`, `1 ≤ m ≤ 16`: it returns nothing, and for some hints the claim written at
`defer_stmt` (`23` coordinates, then the value) is the batching (`Node.batch`) of every list of
`m` children whose words the memory holds. -/
def MeaningAggregateClaims (rd : Reader) : List E → List E → Prop
  | [ncg, cpi, cfresh, ccarried, dst], rets => ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ (h : BatchHints) (out : DeferredClaim),
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs h = some out
  | _, _ => False

/-- `aggregate_claims`' core IR gives its meaning. -/
def aggregate_claims_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "aggregate_claims" args rets → MeaningAggregateClaims rd args rets

/-! ## What `main` asks of its callees with a witness -/

/-- **What a `verify_sub` call establishes for the proof `π`** (B1-d's `verify_sub`, G:3147;
`VerifySub.MeaningVerifySub`): its first four cells hold a public input and a seed, its seventh
argument the child proof's claim on the bytecode (`23` coordinates, then the value), and the
deferring verifier accepts `π` for the public input under the seed. -/
def VerifySubOut (bytecode : List K) (rd : Reader) (args : List E) (π : Proof) : Prop :=
  ∃ pi0 pi1 s0 s1 glp gsq out, args = [pi0, pi1, s0, s1, glp, gsq, out] ∧
    ∃ (seed pi : Digest) (fresh : FixedClaims), (s0, s1) = digestScalars seed ∧
      (pi0, pi1) = digestScalars pi ∧ fresh.bytecodePoint.length = bytecodeVars ∧
      ReadsAt rd out (DeferredClaim.cells fresh) ∧ verifyDeferred bytecode seed pi fresh π = true

/-- **The callees' contracts with witness functions**, on the call relation `coreProgram.Rel`. -/
structure CalleesW (bytecode : List K) (rd : Reader) (wX : E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.Witness)
    (wV : List E → Proof) (wA : List E → BatchHints) : Prop where
  /-- A leanXMSS check: the signature `wX p` verifies the claim at `p`. -/
  xmss : ∀ p, coreProgram.Rel rd "verify_lean_xmss" [p] [] → Sig.XmssOut rd p (wX p)
  /-- A leanSPHINCS check with the byte table: the signature `wS p` verifies the claim at `p`. -/
  sphincs : ∀ p bb, coreProgram.Rel rd "verify_sig_lean_sphincs" [p, bb] [] →
    Sig.ByteBits rd bb → Sig.SphincsOut rd p (wS p)
  /-- The DA check with the exponent table: the matrix `wD args rets` opens the returned claim. -/
  da : ∀ gsq rets, coreProgram.Rel rd "da_verify" [gsq] rets → Da.SquaresAt rd gsq →
    ∃ root vd : Digest, (wD [gsq] rets).Opens root vd ∧ rets = digestCells root ++ digestCells vd
  /-- A child proof's check with the exponent tables: the proof `wV args`. -/
  sub : ∀ pi0 pi1 s0 s1 glp gsq out,
    coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] → ExpTables rd glp gsq →
    VerifySubOut bytecode rd [pi0, pi1, s0, s1, glp, gsq, out] (wV [pi0, pi1, s0, s1, glp, gsq, out])
  /-- The batching, for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the hints `wA args`. -/
  agg : ∀ ncg cpi cfresh ccarried dst, coreProgram.Rel rd "aggregate_claims"
    [ncg, cpi, cfresh, ccarried, dst] [] → ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs (wA [ncg, cpi, cfresh, ccarried, dst]) = some out

/-! ## The decoders

`main`'s values (`core0`): the counts `n_lx = .n 0`, `n_xdup = .n 1`, `n_raw_x = .n 2`,
`n_ls = .n 3`, `n_sdup = .n 4`, `n_raw_s = .n 5`, `n_children = .n 6`, `n_direct_da = .n 7`,
`n_da = .n 40`, `n_da_dup = .n 41` (each `g^count`); the region sizes `da_slots = .n 50`,
`lx_slots = .n 55`, `ls_slots = .n 56`, `da_base = .n 57`, `n_total = .n 58`; `fs_seed = .n 63,
.n 64`; the exponent tables `.n 65`, `.n 66`; the pointers `da_roots = .n 69`,
`lx_table = .n 77`, `ls_table = .n 80`, `cover = .n 117`, `child_pi = .n 394`,
`child_fresh = .n 400`, `child_carried = .n 406`, `written = .n 409`, `defer_stmt = .n 417`; the
direct DA check's words `.n 384 … .n 387`. -/

/-- The four cells of slot `s` of a table at `p`. -/
noncomputable def slotCells (rd : Reader) (p : E) (s : ℕ) : List E := readCells rd (p * gen ^ (4 * s)) 4

/-- The leanXMSS claim of slot `s` of the table at `p`. -/
noncomputable def xmssAt (rd : Reader) (p : E) (s : ℕ) : XmssClaim :=
  let c := slotCells rd p s
  Sig.xmssClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

/-- The leanSPHINCS claim of slot `s` of the table at `p`. -/
noncomputable def sphincsAt (rd : Reader) (p : E) (s : ℕ) : SphincsClaim :=
  let c := slotCells rd p s
  Sig.sphincsClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

/-- The DA claim of slot `s` of the roots at `p`: a root and a membership vector digest, two cells
each (the guest's `da_roots`). -/
noncomputable def daAt (rd : Reader) (p : E) (s : ℕ) : DaClaim :=
  let c := slotCells rd p s
  ⟨digestOfCells (c.getD 0 0) (c.getD 1 0), digestOfCells (c.getD 2 0) (c.getD 3 0)⟩

/-- The mark in coverage slot `s`, as a log. -/
noncomputable def markOf (rd : Reader) (σ : Val) (s : ℕ) : ℕ := gLog (cellAt rd (σ (.n 117)) s)

/-- The running count `written[c]`, as a log. -/
noncomputable def countOf (rd : Reader) (σ : Val) (c : ℕ) : ℕ := gLog (cellAt rd (σ (.n 409)) c)

/-- The number of children. -/
noncomputable def nKids (σ : Val) : ℕ := gLog (σ (.n 6))

/-- The child whose segment of the running counts holds the mark `e`. -/
noncomputable def kidOf (rd : Reader) (σ : Val) (e : ℕ) : ℕ :=
  ((List.range (nKids σ)).find? fun c => decide (e < countOf rd σ (c + 1))).getD 0

/-- The slot of the region `[lo, lo + len)` holding the mark `e` (relative to `lo`). -/
noncomputable def slotOf (rd : Reader) (σ : Val) (lo len e : ℕ) : ℕ :=
  ((List.range len).find? fun s => decide (markOf rd σ (lo + s) = e)).getD 0

/-- The number of slots of the region `[lo, lo + len)` whose marks lie in `[a, b)`. -/
noncomputable def segCount (rd : Reader) (σ : Val) (lo len a b : ℕ) : ℕ :=
  ((List.range len).filter fun s => decide (a ≤ markOf rd σ (lo + s) ∧ markOf rd σ (lo + s) < b)).length

/-- The region sizes, as logs: leanXMSS slots, leanSPHINCS slots, DA slots. -/
noncomputable def lxSlots (σ : Val) : ℕ := gLog (σ (.n 55))
noncomputable def lsSlots (σ : Val) : ℕ := gLog (σ (.n 56))
noncomputable def daSlots (σ : Val) : ℕ := gLog (σ (.n 50))

/-- **Child `c`'s statement**, read off the coverage table: of the marks in its segment
`[written[c], written[c + 1])`, the leanXMSS region's in order, then the leanSPHINCS region's,
then the DA region's, each the claim of its slot; its deferred claim at
`child_carried · g^(24c)`. -/
noncomputable def kidStmt (rd : Reader) (σ : Val) (c : ℕ) : NodeStatement :=
  let a := countOf rd σ c
  let b := countOf rd σ (c + 1)
  let nx := segCount rd σ 0 (lxSlots σ) a b
  let ns := segCount rd σ (lxSlots σ) (lsSlots σ) a b
  let nd := segCount rd σ (lxSlots σ + lsSlots σ) (daSlots σ) a b
  ⟨⟨(List.range nx).map fun j => xmssAt rd (σ (.n 77)) (slotOf rd σ 0 (lxSlots σ) (a + j)),
    (List.range ns).map fun j => sphincsAt rd (σ (.n 80)) (slotOf rd σ (lxSlots σ) (lsSlots σ)
      (a + nx + j)),
    (List.range nd).map fun j => daAt rd (σ (.n 69)) (slotOf rd σ (lxSlots σ + lsSlots σ)
      (daSlots σ) (a + nx + ns + j))⟩,
   deferOfCells (readCells rd (σ (.n 406) * gen ^ (24 * c)) 24)⟩

/-- The words of child `c`'s `verify_sub` call. -/
noncomputable def subArgs (rd : Reader) (σ : Val) (c : ℕ) : List E :=
  [cellAt rd (σ (.n 394)) (2 * c), cellAt rd (σ (.n 394)) (2 * c + 1), σ (.n 63), σ (.n 64),
    σ (.n 65), σ (.n 66), σ (.n 400) * gen ^ (24 * c)]

/-- **Child `c`**: its statement (`kidStmt`), its fresh claim at `child_fresh · g^(24c)`, its
proof `wV` at its `verify_sub` call's words. -/
noncomputable def decKid (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) : Child :=
  ⟨kidStmt rd σ c, fixedOfCells (readCells rd (σ (.n 400) * gen ^ (24 * c)) 24),
    wV (subArgs rd σ c)⟩

/-- **The seed**: the cells `fs_seed`. -/
def decSeed (σ : Val) : Digest := digestOfCells (σ (.n 63)) (σ (.n 64))

/-- **The statement**: the declared claims at the leanXMSS and leanSPHINCS tables and the DA
roots, the deferred claim at `defer_stmt`. -/
noncomputable def decStmt (σ : Val) (rd : Reader) : NodeStatement :=
  ⟨⟨(List.range (gLog (σ (.n 0)))).map (xmssAt rd (σ (.n 77))),
    (List.range (gLog (σ (.n 3)))).map (sphincsAt rd (σ (.n 80))),
    (List.range (gLog (σ (.n 40)))).map (daAt rd (σ (.n 69)))⟩,
   deferOfCells (readCells rd (σ (.n 417)) 24)⟩

/-- The number of raw leanXMSS signatures, raw leanSPHINCS signatures, direct DA checks. -/
noncomputable def nRawX (σ : Val) : ℕ := gLog (σ (.n 2))
noncomputable def nRawS (σ : Val) : ℕ := gLog (σ (.n 5))
noncomputable def nDirect (σ : Val) : ℕ := gLog (σ (.n 7))

/-- **The witness**: the children, a holder for every declared claim by its slot's mark, the
batching's hints. -/
noncomputable def decWit (σ : Val) (rd : Reader) (wX : E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.Witness)
    (wV : List E → Proof) (wA : List E → BatchHints) : NodeWitness :=
  ⟨(List.range (nKids σ)).map (decKid rd σ wV),
    (List.range (gLog (σ (.n 0)))).map fun k =>
      let e := markOf rd σ k
      if e < nRawX σ then .direct (wX (σ (.n 77) * gen ^ (4 * k))) else .child (kidOf rd σ e),
    (List.range (gLog (σ (.n 3)))).map fun k =>
      let e := markOf rd σ (lxSlots σ + k)
      if e < nRawX σ + nRawS σ then .direct (wS (σ (.n 80) * gen ^ (4 * k)))
      else .child (kidOf rd σ e),
    (List.range (gLog (σ (.n 40)))).map fun k =>
      let e := markOf rd σ (lxSlots σ + lsSlots σ + k)
      if e < nRawX σ + nRawS σ + nDirect σ then
        .direct (wD [σ (.n 66)] [σ (.n 384), σ (.n 385), σ (.n 386), σ (.n 387)])
      else .child (kidOf rd σ e),
    wA [σ (.n 6), σ (.n 394), σ (.n 400), σ (.n 406), σ (.n 417)]⟩

/-! ## The statement -/

/-- **`main`, soundly, its witness decoded** (G:4086-4282, TRIAGE #96): on a memory image whose
public input cells (`[1]`, `[g]`) hold the digest `D`, given the callees' contracts with the
witness functions, every run of `main`'s body (under `coreProgram.Rel`) gives the seed
`decSeed σ` and the statement `decStmt σ rd` of digest `D`, which the witness
`decWit σ rd wX wS wD wV wA` holds (`NodeRel`) for the guest's bytecode of `2^23` words. -/
def main_sound_Spec (bytecode : List K) : Prop :=
  bytecode.length = 2 ^ bytecodeVars →
  ∀ (rd : Reader), MemOk rd →
  ∀ (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.Witness) (wV : List E → Proof) (wA : List E → BatchHints),
    CalleesW bytecode rd wX wS wD wV wA →
  ∀ (D : Digest) (σ : Val), LoadHolds rd 1 0 (digestScalars D).1 →
    LoadHolds rd 1 1 (digestScalars D).2 →
    Stmt.HoldsList (coreProgram.Rel rd) rd σ Data.core0.body False (fun rs => rs = []) →
      statementDigest (decSeed σ) (decStmt σ rd) = D ∧
        NodeRel bytecode (decSeed σ) (decStmt σ rd) (decWit σ rd wX wS wD wV wA)

/-! ## The functions, found -/

theorem find_main : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

theorem find_aggregate_claims : coreProgram.find? "aggregate_claims" = some Data.core31 :=
  Program.find?_of_indexOf? (j := 31) (by decide +kernel) rfl

end
end LeanVM.Guest.B1.Main
