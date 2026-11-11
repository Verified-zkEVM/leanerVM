/-
  LeanerVM.Protocol.ToArkLib.CachedSteps

  Cached forms of the components with no round or with an oracle message: mapping the witness,
  recording an answer of the input oracles, the pass check, sending an oracle beside the inputs,
  and challenges pushed onto a vector with the cache carried through. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.CachedProver
public import LeanerVM.Protocol.ToArkLib.MapWitness
public import LeanerVM.Protocol.ToArkLib.QueryRecord
public import LeanerVM.Protocol.ToArkLib.PassCheck
public import LeanerVM.Protocol.ToArkLib.SendOracleBeside
public import LeanerVM.Protocol.ToArkLib.SendEncoded

/-!
# Cached forms of the remaining one-step components

`LeanerVM.Protocol.ToArkLib.CachedProver` has the cached forms of a checked message, a challenge
and the pass-through. These are the others a protocol built of components meets, each a prover
whose run from the cache of its input is the component's honest run (`Component.Cached`):

* `Cached.mapWitness`: the new witness read off the cache, where it may be computed already;
* `Cached.queryRecord`, `Cached.passCheck`: the cache updated, the run the honest one;
* `Cached.sendOracleBeside`: the oracle message read off the cache, as a value equal to the honest
  one (a table whose entries are stored, where the honest message computes them on demand);
* `Cached.sendEncoded`: the encoded witness read off the cache likewise, and handed on as the
  oracle;
* `Cached.drawPushesKeep`: challenges pushed onto a vector, a cache read off the statement before
  them carried through.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Component

variable {ιi : Type} (O : ιi → Type) [∀ i, OracleInterface (O i)] {S T W W' : Type}
  {CIn COut : Type}

/-! ## Mapping the witness -/

section MapWitness

variable (f : S → T) (g : (S × ∀ i, O i) × W → W')
  (g' : (S × ∀ i, O i) × W → CIn → W') (upd : (S × ∀ i, O i) × W → CIn → COut)

/-- The cached prover of a witness map: the new witness and the cache read off the cache. -/
def cachedMapProver : OracleProver []ₒ S O (W × CIn) T O (W' × COut) !p[] where
  PrvState := fun _ ↦ (S × ∀ i, O i) × (W × CIn)
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦
    pure ((f p.1.1, p.1.2), (g' (p.1, p.2.1) p.2.2, upd (p.1, p.2.1) p.2.2))

variable {O f g g' upd} {cin : (S × ∀ i, O i) × W → CIn} {cout : (T × ∀ i, O i) × W' → COut}

/-- The cached form of `Component.mapWitness`: the new witness read off the cache, which must give
the witness map's, and the cache updated, which must give the cache of the output. -/
def Cached.mapWitness (hg : ∀ p, g' p (cin p) = g p)
    (hupd : ∀ p, upd p (cin p) = cout ((f p.1.1, p.1.2), g p)) :
    Cached (Component.mapWitness O f g) cin cout where
  prover := cachedMapProver O f g' upd
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedMapProver, Component.mapWitness, Component.mapWitnessProver, _root_.id, hg,
      hupd]

end MapWitness

/-! ## No message: the pass check and the recorded answer -/

section NoMessage

variable (f : S → T) (upd : (S × ∀ i, O i) × W → CIn → COut)

variable {O f upd} {check : S → Bool} {cin : (S × ∀ i, O i) × W → CIn}
  {cout : (T × ∀ i, O i) × W → COut}

/-- The cached form of `Component.passCheck`: the pass-through prover with the cache updated. -/
def Cached.passCheck (hupd : ∀ p, upd p (cin p) = cout ((f p.1.1, p.1.2), p.2)) :
    Cached (Component.passCheck (W := W) O check f) cin cout where
  prover := cachedPassProver O upd f
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedPassProver, Component.passCheck, Component.passThroughProver, _root_.id,
      hupd]

end NoMessage

section QueryRecord

variable {ι' : Type} (keep : ι' ↪ ιi) (query : S → [O]ₒ.Domain)
  (out : (s : S) → [O]ₒ.Range (query s) → T)
  (upd : (S × ∀ i, O i) × W → CIn → COut)

/-- The cached prover of a recorded answer: the honest record, the cache updated. -/
def cachedQueryProver :
    OracleProver []ₒ S O (W × CIn) T (keptOracles O keep) (W × COut) !p[] where
  PrvState := fun _ ↦ (S × ∀ i, O i) × (W × CIn)
  input := _root_.id
  sendMessage := fun i ↦ Fin.elim0 i.1
  receiveChallenge := fun i ↦ Fin.elim0 i.1
  output := fun p ↦
    pure ((out p.1.1 (answerOf O p.1.2 (query p.1.1)), fun i ↦ p.1.2 (keep i)),
      (p.2.1, upd (p.1, p.2.1) p.2.2))

variable {O keep query out upd} {check : (s : S) → [O]ₒ.Range (query s) → Bool}
  {cin : (S × ∀ i, O i) × W → CIn} {cout : (T × ∀ i, keptOracles O keep i) × W → COut}

/-- The cached form of `Component.queryRecord`: the honest record, the cache updated, which must
give the cache of the output. -/
def Cached.queryRecord
    (hupd : ∀ p, upd p (cin p) =
      cout ((out p.1.1 (answerOf O p.1.2 (query p.1.1)), fun i ↦ p.1.2 (keep i)), p.2)) :
    Cached (Component.queryRecord O keep query check out) cin cout where
  prover := cachedQueryProver O keep query out upd
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedQueryProver, Component.queryRecord, Component.queryRecordProver, _root_.id,
      hupd]

end QueryRecord

/-! ## An oracle message beside the inputs -/

section Beside

variable (M : Type) [OracleInterface M] (msg : (S × ∀ i, O i) × W → CIn → M) (out : S → T)
  (upd : (S × ∀ i, O i) × W → CIn → COut)

/-- The cached prover of an oracle message: the message read off the cache once. -/
def cachedBesideProver :
    OracleProver []ₒ S O (W × CIn) T (besideOracles O M) (W × COut) (sayO M) where
  PrvState := fun _ ↦ ((S × ∀ i, O i) × (W × CIn)) × M
  input := fun p ↦ (p, msg (p.1, p.2.1) p.2.2)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦
    pure ((out st.1.1.1, besideData O M st.1.1.2 st.2),
      (st.1.2.1, upd (st.1.1, st.1.2.1) st.1.2.2))

variable {O M msg out upd} {honest : (S × ∀ i, O i) × W → M} {cin : (S × ∀ i, O i) × W → CIn}
  {cout : (T × ∀ i, besideOracles O M i) × W → COut}

/-- The cached form of `Component.sendOracleBeside`: the message read off the cache, which must be
the honest message, and the cache updated, which must give the cache of the output. -/
def Cached.sendOracleBeside (hmsg : ∀ p, msg p (cin p) = honest p)
    (hupd : ∀ p, upd p (cin p) = cout ((out p.1.1, besideData O M p.1.2 (honest p)), p.2)) :
    Cached (Component.sendOracleBeside O M honest out) cin cout where
  prover := cachedBesideProver O M msg out upd
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedBesideProver, Component.sendOracleBeside, Component.sendBesideProver,
      hmsg, hupd]

end Beside

/-! ## An encoded witness sent as the oracle -/

section Encoded

variable {S M W CIn : Type} [OracleInterface M] (msg : W → CIn → M)

/-- The cached prover of an encoded witness: the message read off the cache once, sent, and handed
on as the oracle. -/
def cachedEncodedProver :
    OracleProver []ₒ S NoOracle (W × CIn) S (OneOracle M) (W × Unit) (sendSpec M) where
  PrvState := fun _ ↦ (S × W) × M
  input := fun p ↦ ((p.1.1, p.2.1), msg p.2.1 p.2.2)
  sendMessage | ⟨0, _⟩ => fun st ↦ pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st ↦ pure ((st.1.1, fun _ ↦ st.2), (st.1.2, ()))

variable {msg} {enc : W → M} {cin : (S × ∀ i, NoOracle i) × W → CIn}

/-- The cached form of `Component.sendEncoded`: the message read off the cache, which must be the
encoding of the witness. -/
def Cached.sendEncoded (hmsg : ∀ p, msg p.2 (cin p) = enc p.2) :
    Cached (Component.sendEncoded S M W enc) cin (fun _ ↦ ()) where
  prover := cachedEncodedProver msg
  run_eq s w := by
    change (pure _ : OracleComp _ _) = _ <$> (pure _ : OracleComp _ _)
    rw [map_pure]
    simp only [cachedEncodedProver, Component.sendEncoded, Component.sendEncodedProver,
      hmsg (s, w)]

end Encoded

/-! ## Challenges pushed onto a vector -/

section Pushes

variable (C : Type) [SampleableType C] {S : Type} (G : (S × ∀ i, O i) × W → CIn)

/-- `j` challenges pushed onto a vector, with a cache read off the statement before them
carried through. -/
def Cached.drawPushesKeep : (j : ℕ) →
    Cached (drawPushes (S := S) (W := W) O C j) G (fun p ↦ G ((p.1.1.1, p.1.2), p.2))
  | 0 => Cached.passThrough (upd := fun _ c ↦ c) fun _ ↦ rfl
  | j + 1 => (Cached.drawPushesKeep j).append
      (Cached.sample (upd := fun _ c _ ↦ c) fun _ _ ↦ rfl)

end Pushes

end Component

end
end LeanerVM.Protocol
