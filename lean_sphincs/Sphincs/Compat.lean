module

public import Statement.LeanSphincs
public import Common.WithHash
public import Sphincs.WithHash

/-!
# The hash inputs by name

`Statement/LeanSphincs.lean` hashes through the tweakable hash both schemes share (`thInput`, `th`,
`thPair`, `taggedSeed`, `Statement/LeanXmss.lean`). The proofs name the inputs of leanSPHINCS's
calls and its seed derivations.
-/

@[expose] public section

namespace Sphincs

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The hash input `P || A || payload` of every tweakable hash call and of the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- `P || A(7, 0, 0) || S || m` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  thInput parameter (tweakFields 7 0 0 0) (bytesLE 32 seed ++ bytesLE 32 message)

/-- `leanSPHINCS || S0` (`scheme_seed`), 43 bytes. -/
def schemeSeedInput (seed : MasterSeed) : HashInput :=
  seedTag ++ bytesLE 32 seed

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-- The leaf index of the untruncated digest call. -/
def blockIndex (first : HashOutput) : Index :=
  Concrete.digestIndex (truncateMessageDigest first)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One seed derivation, first 16 bytes. -/
abbrev deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m Digest :=
  Concrete.thWithHash parameter (keygenDomainFields domain) (bytesLE 32 seed)

/-- One seed derivation, all 32 bytes. -/
abbrev deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m HashOutput :=
  Concrete.thPairWithHash parameter (keygenDomainFields domain) (bytesLE 32 seed)

/-- The randomizer base of a message, first 16 bytes. -/
abbrev deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (message : Message) :
    m Randomness :=
  Concrete.thWithHash parameter (tweakFields 7 0 0 0) (bytesLE 32 seed ++ bytesLE 32 message)

/-- `scheme_seed`: the scheme seed `S`, the whole hash of `leanSPHINCS || S0`. -/
abbrev schemeSeed (seed : MasterSeed) : m MasterSeed :=
  Concrete.taggedSeedWithHash seedTag seed

/-- The signer returned the forgery (`Common.SufCma.SignerReturned`, a request being its message). -/
abbrev SigningTranscript.Contains (log : OracleSpec.QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  Common.SufCma.SignerReturned id log forgery.message forgery.signature

end Sphincs
