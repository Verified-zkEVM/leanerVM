import XmssSecurity.Proof.Deterministic.DerivationTable
import XmssSecurity.Proof.Seeded.Erasure
import XmssSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def tableSignFrom (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := (randomizers (⟨leafIndex, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits
      match ← Concrete.precomputedSignAttempt secretKey leafIndex message randomness with
      | some signature => return some signature
      | none => tableSignFrom randomizers secretKey leafIndex message attempts (trial + 1)

def tableSign (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) : m (Option Signature) :=
  tableSignFrom randomizers secretKey leafIndex message signingAttemptLimit 0

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme XmssSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk leafIndex message => liftM (tableSign randomizers sk leafIndex message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

theorem erases_signFrom (known : QueryCache HashSpec)
    (seed : MasterSeed) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    Erases known (signFrom ⟨seed, sk⟩ leafIndex message attempts trial : OracleComp HashSpec _)
      (tableSignFrom randomizers sk leafIndex message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signFrom tableSignFrom deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (⟨leafIndex, message⟩, BitVec.ofNat 32 trial))
      change Erases known (Concrete.precomputedSignAttempt sk leafIndex message
        ((randomizers (⟨leafIndex, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits) >>= _)
          (Concrete.precomputedSignAttempt sk leafIndex message
            ((randomizers (⟨leafIndex, message⟩, BitVec.ofNat 32 trial)).extractLsb' 0 randomnessBits) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _

theorem erases_sign (known : QueryCache HashSpec)
    (seed : MasterSeed) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (leafIndex : LeafIndex) (message : Message) :
    Erases known (sign ⟨seed, sk⟩ leafIndex message : OracleComp HashSpec _)
      (tableSign randomizers sk leafIndex message) :=
  erases_signFrom known seed sk randomizers hknown leafIndex message _ _

end XmssSecurity.Seeded
