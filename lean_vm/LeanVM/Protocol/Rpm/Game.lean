/-
  LeanVM.Protocol.Rpm.Game

  The random-permutation experiment of `LeanVM/Spec/Rpm.lean` as a game of `lean_rpm`'s
  two-oracle transfer: the honest part before the adversary (nothing), the adversary on byte
  states with its transcript, the verifier with the hash and the direct permutation calls; and
  the random-oracle adversary the transfer gives back, on lane states.
-/

import LeanVM.Protocol.Rpm.Bytes
import LeanVM.Protocol.Rpm.Coins
import LeanRpm.Keccak

/-!
# The experiment as a transfer game

`lean_rpm`'s two-oracle transfer (`LeanRpm.keccak256_transfer2`) is stated for games
`rpmGame2 pre A post` on byte states (`LeanRpm.KState`), with the hash returning 32 bytes
(`LeanRpm.KDigest`). Here:

* `relP`, `logRel`, `advR`: the adversary of `LeanVM/Spec/Rpm.lean`, its queries read on bytes
  (`permQueryToRpm`) and its answers on lanes (`KState.ofRpm`), recording its transcript;
* `toRHF`, `postR`: the verifier, its hash and permutation queries read on bytes;
* `game`: the transfer game (`pre` does nothing);
* `ofRHF`, `romAdv`: the random-oracle adversary of the transfer (`LeanRpm.advS2`, the adversary
  with the indifferentiability simulator), its queries read back on lanes, as an adversary with
  coins against the two oracles of `Statement.lean`;
* `cmap`: a cache of the byte oracles read on lanes.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- The adversary's oracles in `lean_rpm` (coins, the hash, `π` and `π⁻¹`), on bytes. -/
abbrev RSpec := LeanRpm.dSpec Bytes LeanRpm.KDigest LeanRpm.KState

/-- The two random oracles of `lean_rpm`, on bytes, with coins. -/
abbrev HFSpec := unifSpec + LeanRpm.hfSpec Bytes LeanRpm.KDigest LeanRpm.KState

/-- The game's oracles in `lean_rpm`'s two-oracle model. -/
abbrev D2Spec := LeanRpm.dSpec2 Bytes LeanRpm.KDigest LeanRpm.KState

/-- The two random oracles of `lean_rpm`, on bytes: the hash and the permutation calls. -/
abbrev HFS := LeanRpm.hfSpec Bytes LeanRpm.KDigest LeanRpm.KState

/-- The two oracles of `Statement.lean`, with coins. -/
abbrev CSpec := unifSpec + HashSpec

/-- A query on lanes, from a query on bytes. -/
def permQueryOfRpm : LeanRpm.PermQuery LeanRpm.KState → LeanRpm.PermQuery KState
  | .fwd x => .fwd (KState.ofRpm x)
  | .inv y => .inv (KState.ofRpm y)

/-- A permutation query of the adversary, read on bytes. -/
def relP : QueryImpl PermSpec (OracleComp RSpec) := fun q ↦
  KState.ofRpm <$> (liftM (RSpec.query (.inr (.inr (permQueryToRpm q)))) :
    OracleComp RSpec LeanRpm.KState)

/-- A permutation query of the adversary, read on bytes, recorded in the transcript. -/
def logRel : QueryImpl PermSpec (StateT Transcript (OracleComp RSpec)) := fun q ↦
  StateT.mk fun T ↦ (fun a ↦ (a, T ++ [(q, a)])) <$> relP q

/-- The adversary of the transfer: the adversary on bytes, with its transcript. -/
def advR (A : RpmAdversary) : OracleComp RSpec ((Statement × Proof) × Transcript) :=
  (simulateQ logRel A).run []

/-- The two oracles of `Statement.lean`, read on bytes. -/
def toRHF : QueryImpl HashSpec (OracleComp HFSpec)
  | .inl m => Digest.ofRpm <$> LeanRpm.hQuery (E := LeanRpm.KRest) (C := LeanRpm.KCap) m
  | .inr s => KState.ofRpm <$> LeanRpm.fQuery (Msg := Bytes) (KState.toRpm s)

/-- The verifier on the adversary's statement and proof, its queries read on bytes, with the
adversary's transcript. -/
def postR (z : (Statement × Proof) × Transcript) : OracleComp HFSpec RpmOutcome :=
  (fun v ↦ ((z.1, v), z.2)) <$> simulateQ toRHF (verifier queryH queryF z.1.1.1 z.1.1.2 z.1.2)

/-- **The transfer game** of the random-permutation experiment. -/
def game (A : RpmAdversary) : OracleComp D2Spec RpmOutcome :=
  LeanRpm.rpmGame2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)

/-- The transfer's oracles read on lanes: coins, the hash (its 32 bytes), the permutation. -/
def ofRHF : QueryImpl HFSpec (OracleComp CSpec)
  | .inl n => liftM (CSpec.query (.inl n))
  | .inr (.inl m) => Digest.toRpm <$> (liftM (CSpec.query (.inr (.inl m))) : OracleComp CSpec Digest)
  | .inr (.inr x) =>
    KState.toRpm <$> (liftM (CSpec.query (.inr (.inr (KState.ofRpm x)))) : OracleComp CSpec KState)

/-- **The random-oracle adversary of the transfer**: the adversary with the indifferentiability
simulator (`LeanRpm.advS2`), its oracle queries read on lanes, its transcript dropped. -/
noncomputable def romAdv (A : RpmAdversary) : OracleComp CSpec (Statement × Proof) :=
  (fun z ↦ z.1) <$> simulateQ ofRHF
    (LeanRpm.advS2 LeanRpm.keccakPadding LeanRpm.KState.zero (advR A))

/-- A cache of the byte oracles, read on lanes. -/
def cmap (c : HFS.QueryCache) :
    HashSpec.QueryCache :=
  QueryCache.ofFn fun
    | .inl m => (c (.inl m)).map Digest.ofRpm
    | .inr s => (c (.inr (KState.toRpm s))).map KState.ofRpm

end LeanVM.Rpm
