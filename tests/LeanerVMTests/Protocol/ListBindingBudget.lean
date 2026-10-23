import LeanerVM.Protocol.ListBindingBudget
import LeanerVMTests.Protocol.ListBinding

/-!
# The compiled protocol's errors challenge by challenge: tests

* **The marks.** At the toy, whose WHIR chain has two levels, exactly two challenges are marked,
  the query positions of each level.
* **The deployed levels.** The query positions' error counts `a - 1` agreements. Counting `a`
  would leave 48 of the 224 levels of the 56 admissible chains above `2^-111`, the worst at stack
  size `16`, rate `2⁻¹`, level `2` (`t = 30`, `a = 40`, `n = 2^9`: `(40/512)^30 ≈ 2^-110.34`);
  with `a - 1` every level is below `2^-111`, the least margin `0.00024` bits, so `2^-128` after
  the 17 bits of grinding: `Whir.budget` gives the positions `2^-111`.
* **The list bound of level 0** ranges over `23..122` on the window, within the `128` the front's
  bound uses.
* **The statements** type-check at every admissible announcement and rate.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.ListBindingBudget

open LeanerVM.Parameters LeanerVM.Parameters.Whir LeanerVM.Protocol LeanerVM.Protocol.Whir
  LeanerVM.Protocol.Toy
open LeanerVMTests.Protocol.ListBinding (lbLadder)

/-! ## The marks -/

#guard (Finset.univ.filter fun i ↦ listBindingMark toy lbLadder i = true).card = 2

/-! ## The deployed levels -/

/-- A level's numbers: fold count, message variables `κ`, rate exponent `R`, queries `t`,
threshold `a`. -/
structure LevelNumbers where
  fold : ℕ
  κ : ℕ
  R : ℕ
  t : ℕ
  a : ℕ
  deriving DecidableEq

/-- Every level of a chain, first to last. -/
def levels : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Pars → List LevelNumbers
  | sh, _, .last _ nf, P => [⟨sh.ℓ, nf + 1, sh.R, sh.t, P.a⟩]
  | sh, _, @Ladder.cons _ sh' κ' L, P => ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, P.1.a⟩ :: levels L P.2

/-- The levels of every admissible chain. -/
def window : List LevelNumbers :=
  (List.range 14).flatMap fun i ↦ (List.range 4).flatMap fun r ↦
    ((deployed (i + 15) (r + 1)).map fun c ↦ levels c.ladder c.pars).getD []

/-- The rejected count: the positions of a level at `2^-111` had they counted `a` agreements,
`a^t · 2^111 ≤ n^t`. It fails at 48 levels, which is why the error counts `a - 1`. -/
def positionsAtA111 (x : LevelNumbers) : Bool := x.a ^ x.t * 2 ^ 111 ≤ (2 ^ (x.κ + x.R)) ^ x.t

example : window.length = 224 := by decide +kernel

example : (window.filter fun x ↦ !positionsAtA111 x).length = 48 := by decide +kernel

/-- The worst level: stack size `16`, rate `2⁻¹`, level `2`. -/
example : ((deployed 16 1).map fun c ↦ (levels c.ladder c.pars)[2]?) =
    some (some ⟨4, 2, 7, 30, 40⟩) := by
  decide +kernel

/-- There `a` agreements exceed `2^-111`, and `a - 1` do not. -/
example : ¬ 40 ^ 30 * 2 ^ 111 ≤ (2 ^ (2 + 7)) ^ 30 ∧ 39 ^ 30 * 2 ^ 111 ≤ (2 ^ (2 + 7)) ^ 30 := by
  decide

/-- With `a - 1` agreements every level is below `2^-111`. -/
example : window.all fun x ↦ (x.a - 1) ^ x.t * 2 ^ 111 ≤ (2 ^ (x.κ + x.R)) ^ x.t := by
  decide +kernel

/-- The budget is tight: some level is above `2^-112`. -/
example : ¬ window.all fun x ↦ (x.a - 1) ^ x.t * 2 ^ 112 ≤ (2 ^ (x.κ + x.R)) ^ x.t := by
  decide +kernel

/-- The level-0 list bound over the window. -/
example : ((List.range 14).flatMap fun i ↦ (List.range 4).flatMap fun r ↦
      ((deployed (i + 15) (r + 1)).map fun c ↦ [(c.ladder.headPar c.pars).L]).getD []).max? =
    some 122 := by
  decide +kernel

example : ((List.range 14).flatMap fun i ↦ (List.range 4).flatMap fun r ↦
      ((deployed (i + 15) (r + 1)).map fun c ↦ [(c.ladder.headPar c.pars).L]).getD []).min? =
    some 23 := by
  decide +kernel

/-! ## The statements at leanVM -/

section Deployed

variable (F : FlockSpec) (prog : LeanerVM.Semantics.Program) (s : LeanIsa.Sizes)
  (hs : s.Admissible prog) (ρ : ℕ) (hρ : LeanIsa.validRate ρ)

example (i : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).ChallengeIdx)
    (hi : listBindingMark _ (leanIsaChain prog s hs ρ hρ).ladder i = false) :
    listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
      (leanIsaChain prog s hs ρ hρ).pars i ≤ (2 ^ 128)⁻¹ :=
  listBindingError_deployed_le_of_not_mark F prog s hs ρ hρ i hi

example (i : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).ChallengeIdx)
    (hi : listBindingMark _ (leanIsaChain prog s hs ρ hρ).ladder i = true) :
    (2 ^ queryGrindingBits)⁻¹ * listBindingError (leanIsaInstance F prog s)
      (leanIsaChain prog s hs ρ hρ).ladder (leanIsaChain prog s hs ρ hρ).pars i ≤ (2 ^ 128)⁻¹ :=
  (listBindingError_deployed_le_of_mark F prog s hs ρ hρ i hi).2

example : (leanIsaInstance F prog s).μBus ≤ 55 := leanIsa_μBus_le F hs

end Deployed

end LeanerVMTests.Protocol.ListBindingBudget
