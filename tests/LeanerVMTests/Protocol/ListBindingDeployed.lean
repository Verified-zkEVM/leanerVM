import LeanerVM.Protocol.ListBindingDeployed

/-!
# The list binding at leanVM: tests

* **The transform inverts.** `fwd` after `inv` and `inv` after `fwd` are the identity on a table
  of three variables over `K` and over `E`, on the coset of `0` and of `x_8`; `encodeFast` is
  `encode` at every position for `κ = 2, R = 1` and `κ = 3, R = 2`. A wrong twiddle (`Ŵ_j` read
  at `s + 1`) breaks the encoder, so the twiddle does the work.
* **The transform's exact path decodes.** On a word of two lanes and eight positions it returns
  the messages of a codeword, and nothing on the word with one symbol changed; on a word of four
  positions one symbol off a codeword, `ListDecoder.nttFirst` falls back to the brute force and
  finds the codeword at threshold `3`.
  The fast honest word is `kwordOf` on a stack of four variables.
* **Level 0 at leanVM.** At `μ = 15` and rate `2⁻¹` level 0 folds six variables, leaves nine,
  queries 223 positions, and its threshold is 726 of 1024 with list bound 57, in the computed
  head and in the chain alike; `deployedDecoder`, `deployedPick` and the extractor of
  `listBinding_deployed` are definitions with no `noncomputable`. `listBinding_deployed`, its two
  halves and the two facts about its extractor type-check at every admissible announcement; they
  are statements and run nothing.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.ListBindingDeployed

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir LeanerVM.Protocol.LeanIsa
  LeanerVM.Semantics CompPoly OracleComp OracleSpec

/-! ## The transform -/

/-- A table of three variables over `K`. -/
def tK : Vector K 8 := Vector.ofFn fun i ↦ K.ofBits (5 * i.val + 3)

/-- A table of three variables over `E`. -/
def tE : Vector E 8 := Vector.ofFn fun i ↦ E.ofLimbs (K.ofBits (i.val + 1)) (K.ofBits 7) 0

#guard fwd (RingHom.id K) 3 (inv (RingHom.id K) 3 tK 0) 0 = tK
#guard inv (RingHom.id K) 3 (fwd (RingHom.id K) 3 tK (domainPt 8)) (domainPt 8) = tK
#guard fwd (algebraMap K E) 3 (inv (algebraMap K E) 3 tE (domainPt 8)) (domainPt 8) = tE
#guard inv (algebraMap K E) 3 (fwd (algebraMap K E) 3 tE 0) 0 = tE

#guard (List.finRange 8).all fun y ↦
  (encodeFast (algebraMap K E) 2 1 (Vector.ofFn fun i : Fin 4 ↦ tE[i.val]))[y] =
    encode (algebraMap K E) 2 1 (Vector.ofFn fun i : Fin 4 ↦ tE[i.val]) y
#guard (List.finRange 32).all fun y ↦
  (encodeFast (RingHom.id K) 3 2 tK)[y] = encode (RingHom.id K) 3 2 tK y

/-- The transform with the twiddle read at `s + 1`: a mutation. -/
def fwdWrong : (j : ℕ) → Vector K (2 ^ j) → K → Vector K (2 ^ j)
  | 0, m, _ => m
  | j + 1, m, s =>
    let t := twiddle j (s + 1)
    let a : Vector K (2 ^ j) := Vector.ofFn fun i ↦ (lowHalf m)[i] + t * (highHalf m)[i]
    let b : Vector K (2 ^ j) := Vector.ofFn fun i ↦ a[i] + (highHalf m)[i]
    joinHalves (fwdWrong j a s) (fwdWrong j b (s + domainPt (2 ^ j)))

#guard fwdWrong 3 tK 0 ≠ fwd (RingHom.id K) 3 tK 0

/-! ## The transform's exact path -/

/-- The messages of two lanes, four coefficients each. -/
def msg2 : Msgs 1 2 := fun u ↦
  (Vector.ofFn fun i : Fin 4 ↦ ofK (K.ofBits (3 * i.val + u.val + 1)) : Vector E 4)

/-- Their codeword as a lane word. -/
def word2 : LW (2 + 1) := fun y u ↦
  if h : u < 2 then encode (algebraMap K E) 2 1 (msg2 ⟨u, h⟩) y else 0

/-- The codeword with the symbol at position `5` of lane `1` changed. -/
def word2' : LW (2 + 1) := fun y u ↦ if y.val = 5 ∧ u = 1 then word2 y u + 1 else word2 y u

#guard exactNtt 2 1 1 word2 = some msg2
#guard exactNtt 2 1 1 word2' = none

/-- The message of one lane, two coefficients. -/
def msg1 : Msgs 0 1 := fun _ ↦ (#v[ofK (K.ofBits 3), ofK (K.ofBits 5)] : Vector E 2)

/-- Its codeword on four positions with the symbol at position `2` changed. -/
def word1' : LW (1 + 1) := fun y _ ↦
  if y.val = 2 then encode (algebraMap K E) 1 1 (msg1 0) y + 1
  else encode (algebraMap K E) 1 1 (msg1 0) y

/-- The transform's exact path in front of brute force, at threshold `3` of `4`. -/
def decoder3 : ListDecoder 1 1 3 0 :=
  (ListDecoder.bruteForce (by decide) (by decide)).nttFirst (by decide) (by decide) (by decide)

#guard exactNtt 1 1 0 word1' = none
#guard decoder3.decode word1' = [msg1]

/-- A stack of four variables over `K`. -/
def stack4 : CMlPolynomialEval K 4 := Vector.ofFn fun i ↦ K.ofBits (7 * i.val + 2)

#guard (List.finRange 16).all fun y ↦
  (kwordOfFast 2 2 2 1 stack4).row y = (kwordOf 2 2 2 1 stack4).row y

/-! ## Level 0 at leanVM -/

#guard (deployedHeadShape 15 1).ℓ = 6
#guard deployedHeadKap 15 1 = 9
#guard (deployedHeadShape 15 1).R = 1
#guard (deployedHeadShape 15 1).t = 223
#guard deployedHeadThreshold 15 1 = 726

/-- The deployed chain at `μ = 15`, rate `2⁻¹`. -/
def chain15 : Chain := deployedChain 15 1 (by decide)

#guard chain15.κ = 9
#guard (chain15.ladder.headPar chain15.pars).a = 726
#guard (chain15.ladder.headPar chain15.pars).L = 57

/-- The decoder at level 0 at `μ = 15`, rate `2⁻¹`: a definition, so it computes. -/
def decoder15 := deployedDecoder (μ := 15) (r := 1) (by decide)

/-- Its computed form. -/
def headDecoder15 := deployedHeadDecoder (μ := 15) (r := 1) (by decide)

/-- The extractor of the compilation at leanVM: a definition, so it computes. -/
def deployedExtractor (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog)
    (ρ : ℕ) (hρ : validRate ρ) :=
  (listBinding_deployed F prog s hs ρ hρ).extractor

/-- The pick at leanVM's level 0: a definition, so it computes. -/
def deployedPick' (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog)
    (ρ : ℕ) (hρ : validRate ρ) :=
  deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ)

example (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
        (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder).red.verifier
      |>.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
        (M3Rel (leanIsaInstance F prog s)) Set.univ
        (listBinding_deployed F prog s hs ρ hρ).witMid
        (listBinding_deployed F prog s hs ρ hρ).extractor
        ((listBinding_deployed F prog s hs ρ hρ).kSF init impl)
        (listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
          (leanIsaChain prog s hs ρ hρ).pars) :=
  listBinding_deployed_rbrKnowledgeSoundness F prog s hs ρ hρ init impl

example (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i) (k : Fin _) (hk : k.val = 1)
    (tr : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).Transcript k)
    (w : (listBinding_deployed F prog s hs ρ hρ).witMid k) :
    ((listBinding_deployed F prog s hs ρ hρ).kSF init impl).toFun k st tr w ↔
      (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
        (headWord (admissible_of_sizes hs hρ) (committedWord tr (by omega)))).isSome :=
  listBinding_deployed_kSF_one F prog s hs ρ hρ init impl st k hk tr w

example (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (tr : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript)
    (q : Column (leanIsaInstance F prog s).μ)
    (hq : deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
      (headWord (admissible_of_sizes hs hρ) (committedWord (k := Fin.last _) tr (by simp))) = some q) :
    Extractor.RoundByRound.extractIn (listBinding_deployed F prog s hs ρ hρ).extractor st tr () =
      q :=
  listBinding_deployed_extractedStack_eq F prog s hs ρ hρ st tr q hq

example (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef (leanVmPhases (leanIsaInstance F prog s) (leanIsa_conditions F prog s))
        (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder).red
      |>.perfectCompleteness init impl (M3Rel (leanIsaInstance F prog s)) Set.univ :=
  listBinding_deployed_perfectCompleteness F prog s hs ρ hρ init impl

end LeanerVMTests.Protocol.ListBindingDeployed
