import Sphincs.ModelSigner
import Sphincs.ModelRpm
import Sphincs.Transport

/-!
# The statement's end statement from the model's

The statement's leanSPHINCS in the random-permutation model
(`Sphincs.RandomPermutationModel.sufCmaScheme`) is the model's (`Sphincs.Model.modelScheme`), each
hash query answered by Keccak-256 over `π`, through the maps of the keys, the signatures and the
forgeries: key generation (`simulateQ_keygen`), the signer (`simulateQ_sign`) and the verifier
(`simulateQ_verify`) correspond, and so do the winning conditions (`win_eq`). So the statement's
game is the model's against the adversary read through the maps (`Sphincs.Transport`), and the
model's 127 bits in the random-permutation model are the statement's
(`stronglyUnforgeable_of_model`).
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/-- A statement forgery as the model's. -/
def toModelForgery (forgery : Forgery) : FORS.Forgery :=
  ⟨forgery.message, toModelSignature forgery.signature⟩

theorem toModelPublicKey_ofModelPublicKey (publicKey : FORS.PublicKey) :
    toModelPublicKey (ofModelPublicKey publicKey) = publicKey := rfl

theorem map_eq_some_iff (answer : Option FORS.Signature) (signature : Signature) :
    Option.map ofModelSignature answer = some signature ↔
      answer = some (toModelSignature signature) := by
  rcases answer with _ | answer
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl
      exact (signatureEquiv.left_inv answer).symm
    · rintro rfl
      exact signatureEquiv.right_inv signature

/-- **The same winning condition**, the log read through the signatures' map. -/
theorem win_eq (log : QueryLog (FORS.Message →ₒ Option FORS.Signature)) (forgery : Forgery) :
    RandomPermutationModel.sufCmaScheme.winningCondition
        (Transport.mapLog (Option.map ofModelSignature) log) forgery =
      modelScheme.win log (toModelForgery forgery) := by
  simp only [RandomPermutationModel.sufCmaScheme, modelScheme, SigningTranscript.WithinSignatureLimit,
    FORS.SigningTranscript.Valid, FORS.SigningTranscript.Contains, toModelForgery]
  have hlength : List.length (Transport.mapLog (Option.map ofModelSignature) log) = List.length log :=
    Transport.mapLog_length _ _
  congr 1
  apply propext
  refine and_congr ⟨fun h ↦ hlength.symm.le.trans h, fun h ↦ hlength.le.trans h⟩ (not_congr ?_)
  constructor
  · rintro ⟨entry, hentry, hmessage, hanswer⟩
    obtain ⟨original, horiginal, rfl⟩ := Transport.mem_mapLog.mp hentry
    exact ⟨original, horiginal, hmessage, (map_eq_some_iff _ _).mp hanswer⟩
  · rintro ⟨entry, hentry, hmessage, hanswer⟩
    exact ⟨⟨entry.1, Option.map ofModelSignature entry.2⟩,
      Transport.mem_mapLog.mpr ⟨entry, hentry, rfl⟩, hmessage, (map_eq_some_iff _ _).mpr hanswer⟩

/-- **The statement's end statement from the model's 127 bits in the random-oracle model.** -/
theorem stronglyUnforgeable_of_model (h : FORS.SecurityBits params 127) :
    LeanSphincsStronglyUnforgeable :=
  Transport.stronglyUnforgeable_of_map modelSchemeFromSeed RandomPermutationModel.sufCmaScheme
    ofModelPublicKey id (Option.map ofModelSignature) toModelForgery rfl
    (fun seed ↦ by
      simp only [modelSchemeFromSeed, SeedKeyed.scheme, simulateQ_map, Functor.map_map]
      exact (simulateQ_keygen seed).symm)
    (fun sk message ↦ (simulateQ_sign sk message).symm)
    (fun publicKey forgery ↦ (simulateQ_verify (ofModelPublicKey publicKey) forgery.message
      forgery.signature).symm) win_eq (modelScheme_stronglyUnforgeable h)

end Sphincs.Model
