/-
  LeanVM.E2E.Complete.Witness

  T6-det is not vacuous: a leaf holding one leanXMSS claim directly, at an explicit hash, rate and
  proof-of-work fuel, satisfies every hypothesis of `idealVerify_complete_det`.
-/

module

public import LeanVM.E2E.Complete.DecodeFinal
public import LeanVM.Protocol.EndToEnd.Blind.Assemble

/-!
# A witness of T6-det's hypotheses

`idealVerify_complete_det` asks of an honest tree `T`, at a hash `H`, a rate `ρ` and a
proof-of-work fuel `pfuel`: `T.Valid H`, `T.WithinLimits' H ρ pfuel` (the deployed limits, the
budget `b2cBudget'.size (work s w) ≤ 2^28`, and fewer than `2^64` block prefixes of the node's
hashed strings), and the three good events `PowFound`, `WeightsNonzero`, `RootsInjAt`. They hold
together at

* the constant hash `wH`, every string hashing to `wD`, whose first word is zero and whose first
  `128` bits, read as leanXMSS's digest, are a codeword (their `58` digits sum to `106`);
* the rate `1` and the fuel `1`;
* the leaf `wTree`: one leanXMSS claim `wClaim`, held directly by the signature `wSig`, all
  zero, under the key `wPk` whose root is the truncation of `wD`.

Under `wH` every leanXMSS hash is the truncation of `wD`: both layers' message digests are the
codeword, and every root is that truncation, the key's root (`xmssHeld_wSig`, by the kernel). Every
proof of work of V° has `17` bits (`Blind.movesOK_blindProgram`) and every proof-of-work digest is
`wD`, whose low `32` bits are zero: the nonce `0` passes (`powFound_wTree`). `WeightsNonzero` and
`RootsInjAt` hold at a leaf (no children, one entry). The limits are counted on the leaf's
statement and witness (`limits_wTree`); the budget is evaluated on its coefficients by the kernel
(`budget_wTree`, a committed size below `2^20`); the strings the leaf hashes are counted by the
kernel (`count_wTree`).

`idealVerify_complete_wTree`: the honest idealized prover outputs on `wTree` a statement with its
claim and an idealized proof that V_I accepts.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa

@[expose] public section

/-! ## The witness -/

/-- **The witness's digest**: its first word zero, its first `128` bits a leanXMSS codeword
(digits `16`–`47` all `3`, then `3, 3, 3, 1`). -/
def wD : Digest := #v[0, 0xFFFFFFFF, 0xFFFFFFFF, 0x7F, 0, 0, 0, 0]

/-- **The witness's hash**: every string hashes to `wD`. -/
def wH (_ : Bytes) : Digest := wD

/-- **The key**: the root every leanXMSS computation reaches under `wH`, the zero parameter. -/
def wPk : LeanXmss.PublicKey := ⟨LeanXmss.truncateHash (digestBits wD), 0⟩

/-- **The signature**: leaf `0`, every layer's randomizer, chain values and path zero. -/
def wSig : LeanXmss.Signature := ⟨⟨0, Nat.two_pow_pos _⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩

/-- **The claim**: the key signed the zero message. -/
def wClaim : XmssClaim := (wPk, 0)

/-- The witness's claims: `wClaim` alone. -/
def wClaims : Claims := ⟨[wClaim], [], []⟩

/-- **The witness tree**: a leaf holding `wClaim` directly by `wSig`. -/
def wTree : HonestTree := .node wClaims [.direct wSig] [] [] []

/-- The leaf's statement. -/
def wStmt : NodeStatement := ⟨wClaims, leafDefer⟩

/-- The leaf's witness. -/
def wWit : NodeWitness := ⟨[], [.direct wSig], [], [], noHints⟩

/-! ## The leaf's children and deferred claim -/

theorem kidOuts_nil (H : Bytes → Digest) (ρ pfuel : ℕ) : kidOuts H ρ pfuel [] = some [] := rfl

theorem honestDefer_nil (H : Bytes → Digest) : honestDefer H [] = some (noHints, leafDefer) := by
  simp only [honestDefer, ↓reduceIte]

/-- At a leaf, the children's outputs are none and the deferred claim is `leafDefer`. -/
theorem leaf_outs {H : Bytes → Digest} {ρ pfuel : ℕ} {kos : List HonestOut}
    (hkos : kidOuts H ρ pfuel [] = some kos) {hd : BatchHints × DeferredClaim}
    (hdef : honestDefer H (kos.map HonestOut.child) = some hd) : kos = [] ∧ hd = (noHints, leafDefer) := by
  rw [kidOuts_nil, Option.some.injEq] at hkos
  subst hkos
  rw [List.map_nil, honestDefer_nil, Option.some.injEq] at hdef
  exact ⟨rfl, hdef.symm⟩

/-! ## The claim holds -/

/-- The logged verification of `wSig` accepts (the kernel runs it). -/
theorem xmssVerify_wSig : (xmssVerifyWith (LogM.hash wH) wPk 0 wSig).val = true := by
  decide +kernel

/-- **The signature verifies** under `wH`. -/
theorem xmssHeld_wSig : xmssVerifyWith (fun x ↦ some (wH x)) wPk 0 wSig = some true := by
  rw [logs_xmssVerifyWith full_answers wPk 0 wSig (all_true _), xmssVerify_wSig]

/-- **The leaf is valid** under `wH`. -/
theorem valid_wTree : wTree.Valid wH := by
  refine ⟨?_, fun c hc ↦ absurd hc List.not_mem_nil⟩
  rw [wTree, HonestTree.allNodes_node]
  exact ⟨⟨.cons xmssHeld_wSig .nil, .nil, .nil⟩, fun k hk ↦ absurd hk List.not_mem_nil⟩

/-! ## The good events -/

/-- **The proofs of work are found** under `wH` within one nonce: each has `17` bits, and every
proof-of-work digest is `wD`, whose low `32` bits are zero. -/
theorem powFound_wTree : wTree.PowFound wH 1 1 := by
  rw [wTree, HonestTree.PowFound, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef hist bits k cv hg
  have hb : bits = Whir.queryGrindingBits := ((EndToEnd.Blind.movesOK_blindProgram _ _).after hg).1
  subst hb
  unfold findNonce
  split
  · exact Option.some_ne_none _
  · show ((List.range 1).find? fun n ↦ powOk Whir.queryGrindingBits (nonceOf n) wD).map nonceOf ≠ none
    decide +kernel

/-- **The batching's weights**: a leaf batches nothing. -/
theorem weightsNonzero_wTree (H : Bytes → Digest) (ρ pfuel : ℕ) : wTree.WeightsNonzero H ρ pfuel := by
  rw [wTree, HonestTree.WeightsNonzero, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hne
  rw [kidOuts_nil, Option.some.injEq] at hkos
  exact absurd hkos.symm hne

/-- **The roots do not collide**: a leaf's output has one entry. -/
theorem rootsInjAt_wTree (H : Bytes → Digest) (ρ pfuel : ℕ) : wTree.RootsInjAt H ρ pfuel := by
  intro o ho
  rw [wTree, honestOut_node, kidOuts_nil, Option.bind_some] at ho
  obtain ⟨hd, e, π, -, -, rfl⟩ := honestStep_spec H ρ pfuel ho
  intro e₁ he₁ e₂ he₂ _
  simp only [List.flatMap_nil, List.mem_singleton] at he₁ he₂
  rw [he₁, he₂]

/-! ## The limits -/

theorem coverage_wTree : End.coverage wStmt wWit = 1 := rfl

/-- **The leaf is within the deployed limits.** -/
theorem limits_wTree : End.Limits wStmt wWit where
  stackLog := fun c hc ↦ absurd hc List.not_mem_nil
  stream := fun c hc ↦ absurd hc List.not_mem_nil
  directDa := Nat.zero_le _
  xmssHeld := fun x ↦ by simp [wStmt, wWit, wClaims, Hints.direct]
  sphincsHeld := fun x ↦ by simp [wStmt, wClaims]
  daHeld := fun x ↦ by simp [wStmt, wClaims]
  children := Nat.zero_le _
  daRoots := ⟨Nat.zero_le _, fun c hc ↦ absurd hc List.not_mem_nil⟩
  lists := fun c hc ↦ absurd hc List.not_mem_nil
  coverage := by rw [coverage_wTree]; norm_num
  nonempty := Nat.one_pos

/-- The leaf's work: one declared claim, one coverage slot, one raw leanXMSS signature. -/
theorem work_wTree : End.work wStmt wWit = ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := rfl

/-- A linear bound at the leaf's work: its constant and its coefficients of the declared claims,
the coverage slots and the raw leanXMSS signatures. -/
theorem eval_leaf (l : End.Linear) :
    l.eval ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = l.base + l.declared + l.coverage + l.rawXmss := by
  simp [End.Linear.eval]

/-- The budget's words at the leaf's work. -/
theorem words_wTree : (B2C.b2cBudget'.words).eval ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ ≤ 2 ^ 14 := by
  rw [eval_leaf]
  decide +kernel

/-- Bounds on the budget's instructions of each opcode at the leaf's work. -/
def instrsBound : Opcode → ℕ
  | .xor => 2 ^ 11
  | .mulNative => 2 ^ 11
  | .setConstant => 2 ^ 13
  | .deref => 2 ^ 11
  | .jump => 2 ^ 9
  | .blake2s => 2 ^ 10

theorem instrs_wTree (op : Opcode) :
    (B2C.b2cBudget'.instrs op).eval ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ ≤ instrsBound op := by
  rw [eval_leaf]
  cases op <;> decide +kernel

/-- **The leaf is within the budget**: its committed size below `2^20`. -/
theorem budget_wTree : B2C.b2cBudget'.size (End.work wStmt wWit) ≤ 2 ^ 28 := by
  rw [work_wTree]
  refine (End.sizeOf_mono words_wTree instrs_wTree).trans ?_
  simp only [End.sizeOf, instrsBound, Memory.logMem, Nat.clog_pow 2 _ one_lt_two, guest_logSize,
    minLogMem]
  norm_num

/-- The bytecode point's length. -/
theorem log2_bytecode_length : Nat.log2 End.bytecode.length = 22 :=
  (congrArg Nat.log2 End.bytecode_length).trans Nat.log2_two_pow

/-- A deferred claim, its bytecode point the zero point of `22` coordinates. -/
theorem deferredClaim_eta : ∀ d : DeferredClaim, d.bytecodePoint = List.replicate 22 0 →
    d = ⟨List.replicate 22 0, d.bytecodeValue, d.matrixPoint, d.matrixA, d.matrixB⟩ := by
  rintro ⟨a, b, c, d, e⟩ h
  subst h
  rfl

/-- The leaf's deferred claim, its bytecode point's length evaluated. -/
theorem leafDefer_eq : leafDefer = ⟨List.replicate 22 0, leafDefer.bytecodeValue, leafDefer.matrixPoint,
    leafDefer.matrixA, leafDefer.matrixB⟩ :=
  deferredClaim_eta _ (by rw [leafDefer, log2_bytecode_length])

/-- The block prefixes of two lists of strings. -/
theorem length_prefixesOf_append (A B : List Bytes) :
    (prefixesOf (A ++ B)).length = (prefixesOf A).length + (prefixesOf B).length := by
  simp [prefixesOf, List.flatMap_append]

theorem LogM.log_pure {α : Type} (a : α) : (pure a : LogM α).log = [] := rfl

theorem LogM.val_pure {α : Type} (a : α) : (pure a : LogM α).val = a := rfl

theorem childClaimsM_nil (H : Bytes → Digest) (seed : Digest) :
    childClaimsM (LogM.hash H) seed [] = pure [] := rfl

/-- **A leaf's batching** hashes one string: the chain state and the children's count. -/
theorem batchWith_nil_log (H : Bytes → Digest) (s0 : Digest) :
    (batchWith (LogM.hash H) s0 [] noHints).log = [digestBytes s0 ++ blockOf (ofK (gpow 0)) 1] := by
  simp only [batchWith, batchWith.go, observeWith, squeezeWith, batchRoundsWith, noHints, StateT.run',
    List.forIn_nil, List.length_nil, pure_bind, List.zipWith_nil_left, sumE, List.foldl_nil, mul_zero,
    add_zero, and_self, ↓reduceIte]
  rfl

/-- **The leaf's hashed strings**: its statement's digest, the signature's verification and the
batching. -/
theorem nodeLog_wTree : nodeLog wH wStmt wWit =
    (statementDigestWith (LogM.hash wH) (seedOf wH) wStmt).log ++
      (xmssVerifyWith (LogM.hash wH) wPk 0 wSig).log ++
      (batchWith (LogM.hash wH) B1.Main.aggSeedD [] noHints).log := by
  simp only [nodeLog, nodeLogWith, wWit, wStmt, wClaims, wClaim, holdersLog, holderLog,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.flatten_cons, List.flatten_nil,
    List.flatMap_nil, List.append_nil, childClaimsM_nil, LogM.log_pure, LogM.val_pure]

/-- **The leaf's hashed strings** have fewer than `2^64` block prefixes (each part counted by the
kernel). -/
theorem count_wTree : (prefixesOf (nodeLog wH wStmt wWit)).length < 2 ^ 64 := by
  have h1 : (prefixesOf (statementDigestWith (LogM.hash wH) (seedOf wH) wStmt).log).length < 2 ^ 62 := by
    rw [wStmt, leafDefer_eq]
    decide +kernel
  have h2 : (prefixesOf (xmssVerifyWith (LogM.hash wH) wPk 0 wSig).log).length < 2 ^ 62 := by
    decide +kernel
  have h3 : (prefixesOf [digestBytes B1.Main.aggSeedD ++ blockOf (ofK (gpow 0)) 1]).length < 2 ^ 62 := by
    decide +kernel
  rw [nodeLog_wTree, length_prefixesOf_append, length_prefixesOf_append, batchWith_nil_log]
  omega

/-- **The leaf is within the limits, the budget and the count.** -/
theorem withinLimits_wTree : wTree.WithinLimits' wH 1 1 := by
  rw [wTree, HonestTree.WithinLimits', HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef
  obtain ⟨rfl, rfl⟩ := leaf_outs hkos hdef
  exact ⟨limits_wTree, budget_wTree, count_wTree⟩

/-! ## T6-det on the witness -/

/-- **T6-det's hypotheses hold together**: at the hash `wH`, the rate `1` and the fuel `1`, the
leaf `wTree` is valid, within the limits, and its good events hold. -/
theorem hyps_wTree : validRate 1 ∧ wTree.Valid wH ∧ wTree.WithinLimits' wH 1 1 ∧
    wTree.PowFound wH 1 1 ∧ wTree.WeightsNonzero wH 1 1 ∧ wTree.RootsInjAt wH 1 1 ∧
    wTree.size ≤ 1 :=
  ⟨by decide, valid_wTree, withinLimits_wTree, powFound_wTree, weightsNonzero_wTree _ _ _,
    rootsInjAt_wTree _ _ _, by rw [wTree, HonestTree.size]; simp⟩

/-- **T6-det on the witness**: the honest idealized prover outputs on `wTree` a statement making
`wClaim` and an idealized proof that V_I accepts with every hash answered by `wH`. -/
theorem idealVerify_complete_wTree :
    ∃ s ip, honestIdeal wH 1 1 wTree = some (s, ip) ∧ s.claims = wClaims ∧
      idealVerify (m := Id) (fun x ↦ (pure (wH x) : Id Digest)) guest ip 1 s = true := by
  obtain ⟨hρ, hv, hlim, hpow, hw, hroots, hfuel⟩ := hyps_wTree
  exact idealVerify_complete_det wH 1 1 wTree hρ hv hlim hpow hw hroots hfuel

end
end LeanVM.E2E.Complete
