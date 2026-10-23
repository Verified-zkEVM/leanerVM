import LeanerVM.Protocol.ListBinding
import LeanerVM.Protocol.Piop
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Whir.Exact

/-!
# List binding: tests

* **The decoders run.** On a word of one lane and four positions (`κ = 1`, rate `2⁻¹`) the brute
  force decoder returns the codeword at every threshold from `2` to `4`; on the word with one
  symbol changed it returns the codeword at threshold `3`, nothing at exact agreement, and at
  threshold `2`, below unique decoding, several codewords. On a word of two lanes and eight
  positions (`κ = 2`) the exact path returns the messages of a codeword and nothing on the word
  with one symbol changed; brute force at exact agreement returns the codeword; and the exact path
  in front of brute force at threshold `6` (`ListDecoder.exactFirst`) returns the codeword on both,
  on the second by the fallback.
* **The compilation applies at the toy.** The toy's stack has height `2 ^ 3`, the WHIR chain of
  two levels at rate `2⁻¹` folds one lane from `κ = 2`, at exact agreement (list bound `1`), and
  `listBinding_compile`, with the decoder at exact agreement (`ListDecoder.exact`), is the
  security of the compiled protocol from `M3Rel toy` to acceptance, and
  `listBinding_perfectCompleteness` its completeness from the phases'. Its extractor is a
  definition with no `noncomputable`. These examples are statements that type-check at the toy;
  they run nothing.
* **The commitment's extractor decodes.** On the honest word of the toy's honest stack it returns
  that stack; on the word of a stack that fails `M3Holds` and on a word one symbol away from the
  honest one at exact agreement it returns nothing.
* **Relisting needs a front component.** A component that reads its oracle (a query check on a
  bit) has no `Component.Front` witness, so `Component.Front.relist` does not apply to it: its
  verdict depends on the oracle, which the compilation replaces.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.ListBinding

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir LeanerVM.Protocol.Toy CompPoly
  OracleComp OracleSpec ProtocolSpec

/-! ## Decoding -/

/-- The message of one lane, two coefficients. -/
def msg1 : Msgs 0 1 := fun _ ↦ (#v[ofK (K.ofBits 3), ofK (K.ofBits 5)] : Vector E 2)

/-- Its codeword on four positions, as a table. -/
def code1 : Vector E 4 := Vector.ofFn fun y ↦ encode (algebraMap K E) 1 1 (msg1 0) y

/-- The codeword as a lane word. -/
def word1 : LW (1 + 1) := fun y _ ↦ code1[y]

/-- The codeword with the symbol at position `2` changed. -/
def word1' : LW (1 + 1) := fun y _ ↦ if y.val = 2 then code1[y] + 1 else code1[y]

#guard bruteForceList 1 1 4 0 word1 = [msg1]
#guard bruteForceList 1 1 3 0 word1 = [msg1]
#guard bruteForceList 1 1 2 0 word1 = [msg1]
#guard bruteForceList 1 1 3 0 word1' = [msg1]
#guard bruteForceList 1 1 4 0 word1' = []
#guard (bruteForceList 1 1 2 0 word1').length > 1
#guard exactFast 1 1 0 word1 = some msg1
#guard exactFast 1 1 0 word1' = none

/-- The messages of two lanes, four coefficients each. -/
def msg2 : Msgs 1 2 := fun u ↦
  (Vector.ofFn fun i : Fin 4 ↦ ofK (K.ofBits (3 * i.val + u.val + 1)) : Vector E 4)

/-- Their codeword on eight positions, as a table. -/
def code2 : Vector (Vector E 2) 8 := Vector.ofFn fun y ↦ Vector.ofFn fun u ↦
  encode (algebraMap K E) 2 1 (msg2 u) y

/-- The codeword as a lane word. -/
def word2 : LW (2 + 1) := fun y u ↦ if h : u < 2 then code2[y][u] else 0

/-- The codeword with the symbol at position `5` of lane `1` changed. -/
def word2' : LW (2 + 1) := fun y u ↦ if y.val = 5 ∧ u = 1 then word2 y u + 1 else word2 y u

#guard exactFast 2 1 1 word2 = some msg2
#guard exactFast 2 1 1 word2' = none
#guard bruteForceList 2 1 8 1 word2 = [msg2]

/-- The exact path in front of brute force, at threshold `6` of `8`. -/
def decoder6 : ListDecoder 2 1 6 1 :=
  (ListDecoder.bruteForce (by decide) (by decide)).exactFirst (by decide) (by decide) (by decide)

#guard decoder6.decode word2 = [msg2]
#guard decoder6.decode word2' = [msg2]

/-! ## The compilation at the toy -/

/-- The toy meets the bus phase's conditions. -/
theorem toy_conditions : Bus.Conditions toy where
  one_le_d := by decide
  constrained := by decide
  pull_fits := by decide
  count_fits := by decide

/-- WHIR's first level at the toy: one fold, rate `2⁻¹`, one query. -/
def lb0 : Whir.Shape := ⟨0, 1, 1⟩

/-- The last level. -/
def lb1 : Whir.Shape := ⟨0, 1, 1⟩

/-- The chain: from `κ = 2` after the first level's fold, so the stack has `2 + 1 = 3`
variables. -/
def lbLadder : Ladder lb0 (Kap lb1 (0 + 1)) := .cons lb0 (.last lb1 0)

/-- The first level's parameters, at exact agreement. -/
def lbPar0 : Par lb0 (Kap lb1 (0 + 1)) where
  a := 2 ^ (Kap lb1 (0 + 1) + lb0.R)
  L := 1
  N := 1
  hdist := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  hle := le_rfl
  hb := by decide
  hlist := listBound_exact _ (by decide)
  hmca := mcaBound_exact

/-- The last level's parameters, at exact agreement. -/
def lbPar1 : Par lb1 (0 + 1) where
  a := 2 ^ (0 + 1 + lb1.R)
  L := 1
  N := 1
  hdist := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  hle := le_rfl
  hb := by decide
  hlist := listBound_exact _ (by decide)
  hmca := mcaBound_exact

/-- The parameters of the chain. -/
def lbPars : lbLadder.Pars := (lbPar0, lbPar1)

/-- The heights agree. -/
theorem lb_height : Kap lb1 (0 + 1) + lb0.ℓ = toy.μ := rfl

/-- The decoder at level 0's threshold, exact agreement: the exact path. -/
def toyDecoder : ListDecoder (Kap lb1 (0 + 1)) lb0.R (lbLadder.headPar lbPars).a lb0.ℓ :=
  ListDecoder.exact lbPar0.hb

/-- The brute-force decoder behind the exact path is one at the same threshold. -/
example : ListDecoder (Kap lb1 (0 + 1)) lb0.R (lbLadder.headPar lbPars).a lb0.ℓ :=
  (ListDecoder.bruteForce lbPar0.hdist lbPar0.hb).exactFirst lbPar0.hdist lbPar0.hle lbPar0.hb

/-- The compilation at the toy. -/
def toyCompile :=
  listBinding_compile (leanVmPhases toy toy_conditions)
    (leanVmSecurity toy toy_conditions (by decide)) lb_height lbLadder lbPars toyDecoder

example : Component.Security (listBindingDef (leanVmPhases toy toy_conditions) lb_height lbLadder)
    (M3Rel toy) Set.univ (listBindingError toy lbLadder lbPars) :=
  toyCompile

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases toy toy_conditions) lb_height lbLadder).red.verifier.toVerifier
      |>.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel toy) Set.univ toyCompile.witMid
        toyCompile.extractor (toyCompile.kSF init impl) (listBindingError toy lbLadder lbPars) :=
  listBinding_rbrKnowledgeSoundness _ _ _ _ _ _ init impl

/-- The extractor of the compilation: a definition, so it computes. -/
def toyExtractor := toyCompile.extractor

/-- Past the commitment, the state function at the toy is the commitment's extraction. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (s : toy.Stmt × ∀ i, NoOracle i) (k : Fin _) (hk : k.val = 1)
    (tr : (listBindingSpec toy lb0 (Kap lb1 (0 + 1)) lbLadder).Transcript k)
    (w : toyCompile.witMid k) :
    (toyCompile.kSF init impl).toFun k s tr w ↔
      (commitPick toy toyDecoder lb_height s.1 (committedWord tr (by omega))).isSome :=
  listBinding_kSF_one _ _ _ _ _ _ init impl s k hk tr w

/-- The stack the compilation extracts at the toy is the commitment's pick. -/
example (s : toy.Stmt × ∀ i, NoOracle i)
    (tr : (listBindingSpec toy lb0 (Kap lb1 (0 + 1)) lbLadder).FullTranscript) (q : Column toy.μ)
    (hq : commitPick toy toyDecoder lb_height s.1 (committedWord (k := Fin.last _) tr (by simp)) =
      some q) :
    listBindingExtractedStack (leanVmPhases toy toy_conditions)
      (leanVmSecurity toy toy_conditions (by decide)) lb_height lbLadder lbPars toyDecoder s tr = q :=
  listBinding_extractedStack_eq _ _ _ _ _ _ s tr q hq

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases toy toy_conditions) lb_height lbLadder).red.perfectCompleteness
      init impl (M3Rel toy) Set.univ :=
  listBinding_perfectCompleteness toy lb_height (leanVmComplete toy toy_conditions (by decide))
    lbLadder init impl

/-! ## The commitment's extractor -/

/-- The honest word of a stack of the toy. -/
def toyWord (q : Column 3) : KWord lb0.ℓ (Kap lb1 (0 + 1) + lb0.R) lb0.t :=
  kwordOf lb0.ℓ (Kap lb1 (0 + 1)) lb0.R lb0.t q.values

/-- A stack that fails `M3Holds`: column 0 is `[1, 0]`, so the bus does not balance. -/
def badStack : Column 3 := ⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩

/-- The honest word with one symbol changed. -/
def farWord : KWord lb0.ℓ (Kap lb1 (0 + 1) + lb0.R) lb0.t :=
  ⟨fun y ↦ if y.val = 3 then (toyWord honest).row y |>.set 0 1 else (toyWord honest).row y⟩

#guard M3Holds toy (1 : K) honest
#guard ¬ M3Holds toy (1 : K) badStack
#guard (commitPick toy toyDecoder lb_height (1 : K) (toyWord honest)).map Column.values =
  some honest.values
#guard (commitPick toy toyDecoder lb_height (1 : K) (toyWord badStack)).isNone
#guard (commitPick toy toyDecoder lb_height (1 : K) farWord).isNone

/-! ## Relisting needs a front component -/

/-- A bit, read whole. -/
local instance : OracleInterface Bool := OracleInterface.instDefault

/-- The component that accepts when its one oracle, a bit, is set: it reads its oracle. -/
def readsBit : Component.Def Unit (OneOracle Bool) Unit Unit (OneOracle Bool) Unit !p[] :=
  Component.queryCheck (OneOracle Bool) (fun _ ↦ ⟨0, ()⟩) (fun _ b ↦ b) id

/-- A guarded verdict that accepts is not a rejection. -/
theorem pure_ne_failure {α : Type} (a : α) :
    (pure a : OptionT (OracleComp []ₒ) α) ≠ failure := fun h ↦ by
  have := congrArg (fun v ↦ support v.run) h
  simp at this

/-- **A component that reads its oracle is not front**: the same statement and transcript are
accepted with the bit set and rejected with it cleared, which no check on the statement and the
transcript does. -/
theorem readsBit_not_front : IsEmpty (Component.Front readsBit) := ⟨fun F ↦ by
  have h1 := F.verify_eq ((), fun _ ↦ true) (fun i ↦ Fin.elim0 i)
  have h2 := F.verify_eq ((), fun _ ↦ false) (fun i ↦ Fin.elim0 i)
  have v1 := Component.queryCheckVerifier_verify (OneOracle Bool) (fun _ ↦ ⟨0, ()⟩)
    (fun (_ : Unit) (b : Bool) ↦ b) id () (fun _ ↦ true) (fun i ↦ Fin.elim0 i)
  have v2 := Component.queryCheckVerifier_verify (OneOracle Bool) (fun _ ↦ ⟨0, ()⟩)
    (fun (_ : Unit) (b : Bool) ↦ b) id () (fun _ ↦ false) (fun i ↦ Fin.elim0 i)
  change _ = _ at h1 h2
  rw [show readsBit.red.verifier = Component.queryCheckVerifier (OneOracle Bool)
    (fun _ ↦ ⟨0, ()⟩) (fun (_ : Unit) (b : Bool) ↦ b) id from rfl] at h1 h2
  have a1 : Component.answerOf (OneOracle Bool) (fun _ ↦ true) ⟨0, ()⟩ = true := rfl
  have a2 : Component.answerOf (OneOracle Bool) (fun _ ↦ false) ⟨0, ()⟩ = false := rfl
  rw [v1] at h1
  rw [v2] at h2
  simp only [a1, a2, ite_true, Bool.false_eq_true, ite_false] at h1 h2
  by_cases hc : F.check () (fun i ↦ Fin.elim0 i) = true
  · rw [ite_eq_left hc] at h2
    exact pure_ne_failure _ h2.symm
  · rw [ite_eq_right hc] at h1
    exact pure_ne_failure _ h1⟩

end LeanerVMTests.Protocol.ListBinding
