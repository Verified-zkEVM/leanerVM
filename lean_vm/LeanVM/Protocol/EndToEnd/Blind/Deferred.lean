/-
  LeanVM.Protocol.EndToEnd.Blind.Deferred

  The Flock-blind verifier V° accepts whatever the deferring verifier accepts with a true
  bytecode claim, and whatever the deployed verifier accepts, from the same seed, for a hash in
  `Option` (every query answered by a log) or in `Id`.
-/

module

public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Spec.Ideal.Blind

/-!
# The deferring and the deployed verifiers refine V°

V° (`blindProgram`) is `verifyExecution` with the bytecode's value computed (`.computed`) and with
the lincheck's matrices value and terminal `require` deleted (`verifyFlockLincheckBlind`). The
deferring program (`deferredProgram c`) takes both fixed polynomials' values from the claims `c`
(`Evaluations.claimed c`): each is refused unless asked at `c`'s point, then `c`'s value. So:

* `deferredProgram_le_blind`: where `c`'s **bytecode claim is true** (`FixedClaims.BytecodeHolds`:
  `multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue`, the first conjunct of
  `FixedClaims.Holds`), the deferring program refines V° (`Prog.Le`: it does what V° does, or
  fails): its bytecode value is refused or the computed one, and its matrices value and the
  terminal check only add failures. The matrices claim plays no part.
* `leanVmProgram_le_blind`: the deployed program refines V°, the terminal check only adding a
  failure.

A refining program's accepted proof is the refined program's, from the same seed, for a hash in
`Option` (`runProof_of_le_option`; in `Id`, the deployed `runProof_of_le`). Hence (design D3):

* `runProof_blind_of_deferred`, `verifyBlindWith_of_verifyDeferredWith`: a proof the deferring
  verifier accepts, with a true bytecode claim, V° accepts from the same seed; under the IV hashed
  from the bytecode, from the deployed seed;
* `runProof_blind_of_deployed`, `verifyBlindWith_of_verifyWith`, `verifyBlind_of_verify`: a proof
  the deployed verifier accepts, V° accepts.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

@[expose] public section

section Run

variable (H : Bytes → Option Digest)

/-- A refining program's successful run is the refined program's, for a hash in `Option`. -/
theorem run_of_le_option {α : Type} {p q : Prog α} (hpq : Prog.Le p q) :
    ∀ {s : St} {r : α × St}, run H p s = some (some r) → run H q s = some (some r) := by
  induction hpq with
  | fail q => intro s r h; simp [run] at h
  | ret a => intro s r h; exact h
  | read _ ih =>
    intro s r h
    simp only [run] at h ⊢
    split at h
    · simp at h
    · next x xs hs =>
      obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
      exact Option.bind_eq_some_iff.mpr ⟨cv, hcv, ih x h⟩
  | sample _ ih =>
    intro s r h
    simp only [run] at h ⊢
    obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
    exact Option.bind_eq_some_iff.mpr ⟨cv, hcv, ih _ h⟩
  | grind bits _ ih =>
    intro s r h
    simp only [run] at h ⊢
    split at h
    · simp at h
    · next n xs hs =>
      obtain ⟨base, hbase, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨cv, hcv, h⟩ := Option.bind_eq_some_iff.mp h
      refine Option.bind_eq_some_iff.mpr ⟨base, hbase, Option.bind_eq_some_iff.mpr ⟨d, hd,
        Option.bind_eq_some_iff.mpr ⟨cv, hcv, ?_⟩⟩⟩
      split at h
      · next hpow => simp only [hpow, ↓reduceIte]; exact ih h
      · simp at h
  | commit height width _ ih =>
    intro s r h
    simp only [run] at h ⊢
    split at h
    · next x0 x1 xs hs =>
      obtain ⟨cv0, hcv0, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨cv1, hcv1, h⟩ := Option.bind_eq_some_iff.mp h
      refine Option.bind_eq_some_iff.mpr ⟨cv0, hcv0, Option.bind_eq_some_iff.mpr ⟨cv1, hcv1, ?_⟩⟩
      split at h
      · exact ih h
      · simp at h
    · simp at h
  | query i ps _ ih =>
    intro s r h
    simp only [run] at h ⊢
    split at h
    · simp at h
    · next root height width hr =>
      obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.mp h
      refine Option.bind_eq_some_iff.mpr ⟨o, ho, ?_⟩
      split at h
      · next rows rest => exact ih rows h
      · simp at h

/-- **A refining program's accepted proof is the refined program's**, for a hash in `Option`. -/
theorem runProof_of_le_option {P Q : Prog Bool} (hPQ : Prog.Le P Q) {seed : Digest} {π : Proof}
    (h : runProof H P seed π = some true) : runProof H Q seed π = some true := by
  unfold runProof at h ⊢
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.mp h
  refine Option.bind_eq_some_iff.mpr ⟨o, ?_, h⟩
  match o, h with
  | some (true, s), _ => exact run_of_le_option H hPQ ho
  | some (false, _), h => simp at h
  | none, h => simp at h

end Run

end
end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- **The bytecode claim of `c` is true of `bytecode`**: the bytecode's multilinear extension at
`c`'s point is `c`'s value (the first conjunct of `FixedClaims.Holds`). -/
def FixedClaims.BytecodeHolds (bytecode : List K) (c : FixedClaims) : Prop :=
  multilinearEval (bytecode.map ofK) c.bytecodePoint = c.bytecodeValue

/-- True claims have a true bytecode claim. -/
theorem FixedClaims.Holds.bytecode {bytecode : List K} {c : FixedClaims} (h : c.Holds bytecode) :
    c.BytecodeHolds bytecode :=
  h.1

/-- A true bytecode claim refines the computed bytecode value: it is refused, or the computed
one. -/
theorem claimed_bytecode_le {bytecode : List K} {c : FixedClaims} (hc : c.BytecodeHolds bytecode)
    (point : List E) :
    Prog.Le ((Evaluations.claimed c).bytecode bytecode point)
      (Evaluations.computed.bytecode bytecode point) := by
  simp only [Evaluations.claimed, Evaluations.computed, Prog.require]
  split
  · next h => rw [h, ← hc]; exact .ret _
  · exact .fail _

/-- The bus phase refines with the bytecode's value. -/
theorem verifyBusBalance_le_of_bytecode {ev ev' : Evaluations} {layout : Layout}
    (hev : ∀ point,
      Prog.Le (ev.bytecode layout.bytecode point) (ev'.bytecode layout.bytecode point)) :
    Prog.Le (verifyBusBalance ev layout) (verifyBusBalance ev' layout) := by
  unfold verifyBusBalance
  refine .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦ .bind (.refl _) fun x ↦ ?_
  obtain ⟨_, _, _⟩ := x
  refine .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦
    .bind (.refl _) fun _ ↦ .bind (hev _) fun _ ↦ .refl _

/-- **The matrices' value is a value or a refusal**: whatever follows it at every value refines
`q`, it followed by that refines `q`. -/
def Evaluations.MatricesNoMove (ev : Evaluations) : Prop :=
  ∀ (alpha zSkip : E) (chiIn chiInPrime s : List E) {β : Type} (g : E → Prog β) (q : Prog β),
    (∀ v, Prog.Le (g v) q) → Prog.Le (ev.matrices alpha zSkip chiIn chiInPrime s >>= g) q

/-- The computed matrices' value is a value. -/
theorem computed_matricesNoMove : Evaluations.computed.MatricesNoMove :=
  fun _ _ _ _ _ _ _ _ hg ↦ hg _

/-- A claimed matrices' value is a value or a refusal. -/
theorem claimed_matricesNoMove (c : FixedClaims) : (Evaluations.claimed c).MatricesNoMove := by
  intro alpha zSkip chiIn chiInPrime s β g q hg
  simp only [Evaluations.claimed, Prog.require]
  split
  · exact hg _
  · exact .fail _

/-- A check followed by a return refines the return. -/
theorem require_ret_le {β : Type} (c : Prop) [Decidable c] (b : β) :
    Prog.Le (Prog.require c >>= fun _ ↦ Prog.ret b) (Prog.ret b) := by
  unfold Prog.require
  split
  · exact .ret _
  · exact .fail _

/-- **The lincheck refines its Flock-blind version**, for evaluations whose matrices' value is a
value or a refusal: the matrices' value and the terminal check only add failures. -/
theorem verifyFlockLincheck_le_blind {ev : Evaluations} (hev : ev.MatricesNoMove)
    (zc : ZerocheckResult) :
    Prog.Le (verifyFlockLincheck ev zc) (verifyFlockLincheckBlind zc) := by
  unfold verifyFlockLincheck verifyFlockLincheckBlind
  refine .bind (.refl _) fun _ ↦ .bind (.refl _) fun x ↦ ?_
  obtain ⟨_, _⟩ := x
  exact .bind (.refl _) fun _ ↦ hev _ _ _ _ _ _ _ fun _ ↦ require_ret_le _ _

/-- Flock refines its Flock-blind version. -/
theorem verifyFlock_le_blind {ev : Evaluations} (hev : ev.MatricesNoMove) (logN : ℕ) :
    Prog.Le (verifyFlock ev logN) (verifyFlockBlind logN) :=
  .bind (.refl _) fun zc ↦ verifyFlockLincheck_le_blind hev zc

/-- **`verify_execution` refines V°'s**, for evaluations whose bytecode value refines the computed
one and whose matrices' value is a value or a refusal. -/
theorem verifyExecution_le_blind {ev : Evaluations} {bytecode : List K}
    (hb : ∀ point, Prog.Le (ev.bytecode bytecode point)
      (Evaluations.computed.bytecode bytecode point))
    (hm : ev.MatricesNoMove) (publicInput : Digest) :
    Prog.Le (verifyExecution ev bytecode publicInput)
      (verifyExecutionBlind bytecode publicInput) := by
  unfold verifyExecution verifyExecutionBlind
  refine (Prog.Le.refl _).bind_of fun x hx ↦ ?_
  obtain ⟨layout, r⟩ := x
  have hl : layout.bytecode = bytecode := readSizes_bytecode hx
  refine .bind (.refl _) fun _ ↦ .bind (verifyBusBalance_le_of_bytecode (hl ▸ hb)) fun _ ↦
    .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦ .bind (verifyFlock_le_blind hm _) fun x ↦ ?_
  obtain ⟨_, _⟩ := x
  exact .bind (.refl _) fun x ↦ by obtain ⟨_, _⟩ := x; exact .refl _

/-- **The deferring program, its bytecode claim true, refines V°.** -/
theorem deferredProgram_le_blind {bytecode : List K} {c : FixedClaims}
    (hc : c.BytecodeHolds bytecode) (publicInput : Digest) :
    Prog.Le (deferredProgram c bytecode publicInput) (blindProgram bytecode publicInput) :=
  .bind (verifyExecution_le_blind (claimed_bytecode_le hc) (claimed_matricesNoMove c) publicInput)
    fun _ ↦ .refl _

/-- **The deployed program refines V°.** -/
theorem leanVmProgram_le_blind (bytecode : List K) (publicInput : Digest) :
    Prog.Le (leanVmProgram bytecode publicInput) (blindProgram bytecode publicInput) :=
  .bind (verifyExecution_le_blind (fun _ ↦ .refl _) computed_matricesNoMove publicInput)
    fun _ ↦ .refl _

section Option

variable {H : Bytes → Option Digest} {bytecode : List K} {publicInput : Digest}

/-- **The deferring verifier's accepted proof, its bytecode claim true, is V°'s**, from the same
seed, every hash answered (in `Option`). -/
theorem runProof_blind_of_deferred {c : FixedClaims} (hc : c.BytecodeHolds bytecode)
    {seed : Digest} {π : Proof}
    (h : runProof H (deferredProgram c bytecode publicInput) seed π = some true) :
    runProof H (blindProgram bytecode publicInput) seed π = some true :=
  runProof_of_le_option H (deferredProgram_le_blind hc publicInput) h

/-- **The deployed verifier's accepted proof is V°'s**, from the same seed, every hash answered. -/
theorem runProof_blind_of_deployed {seed : Digest} {π : Proof}
    (h : runProof H (leanVmProgram bytecode publicInput) seed π = some true) :
    runProof H (blindProgram bytecode publicInput) seed π = some true :=
  runProof_of_le_option H (leanVmProgram_le_blind bytecode publicInput) h

/-- The deployed seed is the IV's, then the public input's. -/
theorem seedWith_eq_bind (H' : Bytes → Option Digest) (bytecode : List K) (publicInput : Digest) :
    seedWith H' bytecode publicInput =
      (fiatShamirIvWith H' bytecode).bind fun iv ↦
        H' (digestBytes iv ++ digestBytes publicInput) := by
  simp only [seedWith, fiatShamirIvWith, Option.bind_eq_bind, Option.bind_assoc]

/-- **D3: the deferring verifier's accepted proof, its bytecode claim true and its IV the one
hashed from the bytecode, V° accepts**, every hash answered. -/
theorem verifyBlindWith_of_verifyDeferredWith {c : FixedClaims} (hc : c.BytecodeHolds bytecode)
    {iv : Digest} (hiv : fiatShamirIvWith H bytecode = some iv) {π : Proof}
    (h : verifyDeferredWith H bytecode iv publicInput c π = some true) :
    verifyBlindWith H bytecode publicInput π = some true := by
  unfold verifyDeferredWith at h
  unfold verifyBlindWith
  rw [seedWith_eq_bind, hiv, Option.bind_some]
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨seed, hseed, runProof_blind_of_deferred hc h⟩

/-- **D3: the deployed verifier's accepted proof V° accepts**, every hash answered. -/
theorem verifyBlindWith_of_verifyWith {π : Proof}
    (h : verifyWith H bytecode publicInput π = some true) :
    verifyBlindWith H bytecode publicInput π = some true := by
  unfold verifyWith at h
  unfold verifyBlindWith
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨seed, hseed, runProof_blind_of_deployed h⟩

end Option

/-- **The deployed verifier's accepted proof V° accepts, with BLAKE2s.** -/
theorem verifyBlind_of_verify {bytecode : List K} {publicInput : Digest} {π : Proof}
    (h : verify bytecode publicInput π = true) :
    Id.run (verifyBlindWith blake2sBytes bytecode publicInput π) = true :=
  runProof_of_le blake2sBytes (leanVmProgram_le_blind bytecode publicInput) h

end
end LeanVM.Protocol.Verifier
