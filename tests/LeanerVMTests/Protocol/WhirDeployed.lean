import LeanerVM.Parameters.Whir
import LeanerVMTests.Protocol.WhirOpen

/-!
# The verifier of the opening of WHIR at a deployed size

The verifier of `whirOpen` run on the ladder of the deployed `(μ, R) = (28, 1)`: six levels with
the parameters' fold counts and rates, the first at a code of `2 ^ 23` positions (`κ = 22`), with
one query per level instead of the tabulated counts so that the run stays short (the cost is linear
in the queries). The stack is zero, its weight an equality kernel on `28` variables, the claim `0`,
and every prover message zero, so the transcript is honest without any prover work. The run goes
through every check up to the terminal one, which evaluates the composite weight at the tail point.

* **The run finishes and accepts.** Nothing on the verifier's path builds a `2 ^ κ` table: the
  weights' tables are lazy, and each row is folded once, with its `2 ^ ℓ` fold weights built once.
* **A nonzero claim is rejected.**
-/

namespace LeanerVMTests.Protocol.WhirDeployed

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Whir LeanerVM.Protocol.StepSchedule
  CompPoly CMlPolynomialEval
open LeanerVMTests.Protocol.WhirOpenToy

/-- A nonzero challenge from an index. -/
def ch (i : ℕ) : E :=
  ee (0x9e3779b97f4a7c15 * (i + 1) % 2 ^ 64) (0x243f6a8885a308d3 * (i + 7) % 2 ^ 64)

/-- A position from an index. -/
def posOf (b i : ℕ) : Fin (2 ^ b) :=
  ⟨0x9e3779b97f4a7c15 * (i + 3) % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The zero word. -/
def zeroWord (ℓ b t : ℕ) : Word ℓ b t := ⟨fun _ ↦ Vector.replicate (2 ^ ℓ) 0⟩

/-- The transcript of a level with zero messages. -/
def zeroLevel (sh sh' : Shape) (κ' : ℕ) {k : List Step} (rest : ValList k) :
    ValList (levelSteps sh sh' κ' k) :=
  ⟨ch 1, (fun i ↦ ((0 : SumcheckRound.Message E 2), ch (2 + i.val))),
    (0 : SumcheckRound.Message E 2), zeroWord sh'.ℓ (κ' + sh'.R) sh'.t,
    (fun i ↦ ch (20 + i.val)), (0 : E), (0 : SumcheckRound.Message E 2), (0 : E),
    (fun q ↦ posOf _ q.val), ch 50, (), (0 : SumcheckRound.Message E 2), (), rest⟩

/-- The transcript of the final level with zero messages. -/
def zeroFinal (sh : Shape) (nf : ℕ) : ValList (finalSteps sh nf) :=
  ⟨ch 1, (fun i ↦ ((0 : SumcheckRound.Message E 2), ch (2 + i.val))),
    (0 : SumcheckRound.Message E 2), (Vector.replicate (2 ^ (nf + 1)) 0 : Tab (nf + 1)), (0 : E),
    (fun q ↦ posOf _ q.val), ch 51, (), (0 : SumcheckRound.Message E 2), (), ch 60,
    (fun i ↦ ((0 : SumcheckRound.Message E 2), ch (61 + i.val))), ()⟩

/-- The zero transcript of a chain. -/
def zeroLadder : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → ValList L.steps
  | _, _, .last sh nf => zeroFinal sh nf
  | _, _, .cons sh L => zeroLevel sh _ _ (zeroLadder L)

/-- The chain of the parameters' levels on `μ` variables, with one query per level. -/
def ofLevels : ℕ → List Whir.Level → Option (Σ (sh : Shape) (κ : ℕ), Ladder sh κ)
  | _, [] => none
  | rem, [l] =>
    match rem - l.fold with
    | 0 => none
    | nf + 1 => some ⟨Shape.ofFold l.fold l.logInvRate 1, nf + 1, .last _ nf⟩
  | rem, l :: rest =>
    (ofLevels (rem - l.fold) rest).map fun L ↦
      ⟨Shape.ofFold l.fold l.logInvRate 1, Kap L.1 L.2.1, .cons _ L.2.2⟩

/-- The verifier of the opening on the zero stack with an equality-kernel weight and the claim
`c`, on the zero transcript of the chain of `(μ, R)`. -/
def run (μ R : ℕ) (c : E) : Option Bool :=
  (Whir.ladder μ R).bind fun ls ↦ (ofLevels μ ls).map fun ⟨sh, κ, L⟩ ↦
    (whirOpenComplete sh κ L).guarded.check
      ((eqWeight (Vector.ofFn fun i ↦ ch (100 + i.val)), c),
        fun _ ↦ zeroWord sh.ℓ (κ + sh.R) sh.t)
      (seqTr _ ⟨(), (0 : SumcheckRound.Message E 2), zeroLadder L⟩)

/-- The first level of the chain of `(28, 1)` folds six lanes, and its code has `κ = 22`. -/
#guard ((Whir.ladder 28 1).bind (ofLevels 28)).map (fun L ↦ (L.1.ℓ, L.2.1)) == some (6, 22)

#guard run 28 1 0 == some true
#guard run 28 1 1 == some false

end LeanerVMTests.Protocol.WhirDeployed
