/-
  LeanerVM.Protocol.PublicInput

  The public-input phase: the verifier draws a challenge, the prover sends the values it claims
  for the public columns on the line through their first two cells, and the verifier checks
  those values against the public statement and pools the claims. Both halves proved, at the
  slot's schedule and error, for the specification's check and for the check of the deployed
  verifiers.
-/

module

public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.Spine.Errors
public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
public import LeanerVM.Protocol.ToArkLib.KeepOracles
import LeanerVM.Protocol.ToCompPoly.Multilinear
import LeanerVM.Protocol.ToVCVio.UniformSample
import Mathlib.Algebra.CharP.Two

/-!
# The public-input phase

Specification §8.2 (`doc/leanvm/body/08-end-to-end-protocol.tex:27-33`, and the paragraph
"Public input" of the unrolled protocol, `:80-85`, at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`): the public input is the first two memory cells,
both parties know them, and

1. the verifier samples `r ∈ E`;
2. the prover sends `c₀, c₁`, claiming `c_ℓ` is the extension of memory limb `ℓ` at
   `(r, 0, …, 0)`;
3. the verifier checks `c_ℓ = (1 + r)·mem[g⁰]_ℓ + r·mem[g¹]_ℓ` for `ℓ ∈ {0, 1}`, rejecting
   otherwise, and pools `c₀, c₁`, with `0` for the top limb, as claims on the three memory limbs
   at `(r, 0, …, 0)`.

Over an abstract instance the memory limbs are the instance's public lines, columns whose cells
0 and 1 the statement fixes; each line says whether its value is sent. The prover sends the
values of the lines that are, in order, as one message. The verifier rejects a message that
does not have one value per sent line, checks the rest against the lines' values, and pools one
claim per line: for a line whose value was sent, at the value *sent*, read off the message
(`pooledFrom`), and for the others at the value the verifier computes. Pooling the values sent
is what makes the check load-bearing: a verifier that pooled the values it computes would be
knowledge sound with no check at all. The length is not a check that can be dropped: a pool
exists only for a message of that length (`pooledFrom` takes the proof), so no weakened check
pools a value the prover did not send. When the check passes the verdict is the computed pool
(`verdict_pooledFrom_of_check`), and the proofs reason about that one, `pooled`. The verifier
reads the transcript and never the stack: it is a front verifier, `verifierWith` at the check
and the pool, a shape the tests reuse for the verifiers that omit or weaken the check.

Perfect completeness: on a stack whose lines hold, every pooled claim is true, by the identity
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)` and `-1 = 1` in `E`. Knowledge soundness at `1/|E|`,
the slot's error: the extractor keeps the trivial witness, since the stack is the oracle; if the
pooled claims hold and some line's cells differ from the statement's, that line's claim is a
nonzero polynomial of degree one in `r`, true at one challenge at most, whatever the number of
lines.

Written from the specification; the Rust verifier was read afterwards. It reads the same
transcript and checks one equation on the two public words instead of one per limb,
`c₀ + y·c₁ = (1 + r)·w₀ + r·w₁` (`crates/lean_vm/src/cpu/mod.rs:752-755`), as do the Python
verifier and the recursion guest (`checkWords`, transcribed from the sources at the pin). The
two equations here imply that one (`checkWords_of_check`), and it accepts transcripts they
reject, so the theorems up to `rbr` are about the specification's verifier.

The deployed verifier (`deployedVerifier`) is the same shape, `verifierWith` at `checkWords` and
the pool from the values sent, and its phase (`deployedPublicInputPhase`) is the specification's
prover with it, at the same slot and error. The completeness is the specification's argument
(`deployed_complete`). For the knowledge soundness the message is no function of the statement
and the challenge, so the state after the challenge is that some message is accepted
(`deployedStateFunction`). Outside the table seam, one challenge at most has such a message
(`bad_challenge_unique_words`): the claims on the two sent lines are true of the stack, so the
equation on the words is one on its cells, which `accepts_two_challenges` shows two challenges
would fix to the statement's, with the top limb zero by its own claim. The bound is the
specification's, `1/|E|` (`deployed_rbr`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace PublicInput

/-! ## The line through cells 0 and 1 -/

/-- The point `(r, 0, …, 0)` of `E^n`, at which §8.2 evaluates the memory limbs. -/
def linePoint {n : ℕ} (hn : 0 < n) (r : E) : Vector E n :=
  Vector.cast (by omega : 1 + (n - 1) = n) (#v[r] ++ Vector.replicate (n - 1) (0 : E))

/-- The extension of a column on the line through its cells 0 and 1:
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)`. The zero coordinates select the first two cells, and
the first coordinate interpolates between them. -/
theorem eval₂Mle_linePoint {n : ℕ} (hn : 0 < n) (q : CMlPolynomialEval K n) (r : E) :
    CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      (1 - r) * ofK (q.get ⟨0, Nat.two_pow_pos n⟩) +
        r * ofK (q.get ⟨1, Nat.one_lt_two_pow hn.ne'⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 1 + m = m + 1 := Nat.add_comm 1 m
  -- The column as a table on `1 + m` variables, and the point as `(r)` followed by `m` zeros.
  have hq : CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      CMlPolynomialEval.eval₂Mle
        (Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) q))
        (algebraMap K E) (Vector.cast h (#v[r] ++ Vector.replicate m (0 : E))) := by
    simp only [linePoint, Nat.add_one_sub_one, Vector.cast_cast, Vector.cast_rfl]
  -- The zero coordinates select the slice at index zero; one variable is left.
  rw [hq, eval₂Mle_cast (algebraMap K E) h, CMlPolynomialEval.eval₂Mle, ← boolVec_zero,
    evalMle_append_boolVec, CMlPolynomialEval.evalMle_succ, CMlPolynomialEval.evalMle_zero,
    CMlPolynomialEval.evalMleLayer_get]
  simp only [Vector.head, Nat.reduceAdd, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reducePow, slice, CMlPolynomialEval.map,
    Extension.Ext.algebraMap_eq_ofBase, cubeIndex, pow_one, mul_zero, add_zero, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_cast, Fin.zero_eta, Fin.isValue, Vector.get_eq_getElem,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Vector.getElem_ofFn, zero_add, Fin.mk_one, Nat.mod_succ,
    Fin.mk_zero']

/-! ## Values, check and claims -/

variable (I : M3Instance)

/-- The value of a public line at the challenge `r`: the line through the statement's two
cells, `(1 + r)·cell0 + r·cell1`. -/
def lineValue (r : E) (l : PublicLine I.toShape) : E :=
  (1 + r) * ofK l.cell0 + r * ofK l.cell1

/-- The claim that a line's column takes the line's value at `(r, 0, …, 0)`. -/
def lineClaim (r : E) (l : PublicLine I.toShape) : ColumnClaim I :=
  ⟨l.col, linePoint l.pos r, lineValue I r l⟩

/-- What the verifier pools: the claims it received, then one claim per public line. -/
def pooled (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)

/-- The values the verifier expects in the prover's message: the values at the challenge of the
lines whose value is sent, in order. -/
def expectedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).toList.filter (·.sent)).map (lineValue I r)

/-- The verifier's check: the prover's message is the expected values. -/
def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = expectedValues I s.1 r)

private theorem check_eq_true_iff (s : I.Stmt × TableOut I) (r : E) (cs : List E) :
    check I s r cs = true ↔ cs = expectedValues I s.1 r :=
  decide_eq_true_iff

/-! ## The check on the words -/

/-- The check of the deployed verifiers, at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`
(`crates/lean_vm/src/cpu/mod.rs:752-755`, `python-verifier/verifier.py:1400`,
`crates/rec_aggregation/guests/aggregate.py:1680-1683`): one equation on the two public words in
`E`, `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁`, where `y` is the adjoined root of `y³ + y + 1`. The
words are the two sent lines' cells, `w₀ = E.ofLimbs l₀.cell0 l₁.cell0 0` and
`w₁ = E.ofLimbs l₀.cell1 l₁.cell1 0`, so a line's limb is the coefficient of `y^i` in the word.
The message must be the two values `[c₀, c₁]` and a message of another length is rejected. The
definition is transcribed from those sources, not written from the specification.

The deployed verifiers have this one shape. For any other number of sent lines there is nothing
to transcribe, and the check is the specification's, one equation per limb: that keeps
`checkWords_of_check` true of every instance. -/
def checkWords (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  match (I.publicLines s.1).toList.filter (·.sent), cs with
  | [l₀, l₁], [c₀, c₁] =>
    decide (c₀ + y * c₁ =
      (1 + r) * E.ofLimbs l₀.cell0 l₁.cell0 0 + r * E.ofLimbs l₀.cell1 l₁.cell1 0)
  | [_, _], _ => false
  | _, _ => check I s r cs

/-- The two lines' values combined by `y` are the two words' line: `(1 + r)·w₀ + r·w₁`. -/
private theorem lineValue_pair (r : E) (l₀ l₁ : PublicLine I.toShape) :
    lineValue I r l₀ + y * lineValue I r l₁ =
      (1 + r) * E.ofLimbs l₀.cell0 l₁.cell0 0 + r * E.ofLimbs l₀.cell1 l₁.cell1 0 := by
  simp only [lineValue, ofLimbs_eq]
  ring_nf
  simp

/-- The specification's check implies the deployed one: the limb equations give the equation on
the words, whatever the lines. The converse is false: the tests of the public-input phase have a
challenge where only the deployed check holds. -/
theorem checkWords_of_check {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (h : check I s r cs = true) : checkWords I s r cs = true := by
  have hcs := (check_eq_true_iff I s r cs).mp h
  subst hcs
  unfold checkWords expectedValues
  rcases hf : (I.publicLines s.1).toList.filter (·.sent) with _ | ⟨l₀, _ | ⟨l₁, _ | ⟨l₂, ls⟩⟩⟩
  · simpa [checkWords, expectedValues, hf] using h
  · simpa [checkWords, expectedValues, hf] using h
  · rw [hf]
    simp only [List.map_cons, List.map_nil]
    exact decide_eq_true (lineValue_pair I r l₀ l₁)
  · simpa [checkWords, expectedValues, hf] using h

/-- The number of lines whose value is sent: the length of the prover's message. -/
def sentCount {n : ℕ} (ls : Vector (PublicLine I.toShape) n) : ℕ :=
  (ls.toList.filter (·.sent)).length

/-- The expected values are one per sent line. -/
theorem expectedValues_length (input : I.Stmt) (r : E) :
    (expectedValues I input r).length = sentCount I (I.publicLines input) :=
  List.length_map ..

/-- The number of lines before line `i` whose value is sent: the position of line `i`'s value
in the message, when it is sent. -/
def sentBefore {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (i : Fin n) : ℕ :=
  ((ls.toList.take i.val).filter (·.sent)).length

/-- In a filtered list, the element that comes from position `i` of the original sits at the
number of kept elements before `i`. -/
private theorem getElem?_filter_length_take {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length), p l[i] = true →
      (l.filter p)[((l.take i).filter p).length]? = some l[i]
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | a :: _, 0, _, h => by
    have ha : p a = true := by simpa using h
    simp [ha]
  | a :: l, i + 1, hi, h => by
    have ih := getElem?_filter_length_take p l i (Nat.lt_of_succ_lt_succ hi) (by simpa using h)
    by_cases hpa : p a = true
    · simp [hpa, ih]
    · simp [hpa, ih]

/-- A sent line's position is inside a message with one value per sent line. -/
theorem sentBefore_lt {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (i : Fin n)
    (hs : ls[i].sent = true) : sentBefore I ls i < sentCount I ls :=
  (List.getElem?_eq_some_iff.mp (getElem?_filter_length_take
    (fun l : PublicLine I.toShape ↦ l.sent) ls.toList i.val (by simp) (by simpa using hs))).1

/-- The claims built from a message with one value per sent line, one per line, on the line's
column at `(r, 0, …, 0)`: a line whose value is sent takes it from the message, at its position
among the sent lines, and an unsent line takes `unsent` of it. -/
def claimsWith (r : E) (unsent : PublicLine I.toShape → E) {n : ℕ}
    (ls : Vector (PublicLine I.toShape) n) (cs : List E) (h : cs.length = sentCount I ls) :
    Vector (ColumnClaim I) n :=
  Vector.ofFn fun i ↦
    ⟨ls[i].col, linePoint ls[i].pos r,
      if hs : ls[i].sent then
        cs[sentBefore I ls i]'(lt_of_lt_of_eq (sentBefore_lt I ls i hs) h.symm)
      else unsent ls[i]⟩

/-- The claims from the message: an unsent line takes the value the verifier computes. -/
abbrev claimsFrom (r : E) {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (cs : List E)
    (h : cs.length = sentCount I ls) : Vector (ColumnClaim I) n :=
  claimsWith I r (lineValue I r) ls cs h

/-- What the verifier pools from a message with one value per sent line: the claims it
received, then one claim per public line, from the values sent. No pool exists for another
message. -/
def pooledFrom (s : I.Stmt × TableOut I) (r : E) (cs : List E)
    (h : cs.length = sentCount I (I.publicLines s.1)) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs h⟩)

/-- The claims from the expected values are the lines' claims: the value sent for a line is
its line value. -/
private theorem claimsFrom_expected (r : E) (input : I.Stmt)
    (h : (expectedValues I input r).length = sentCount I (I.publicLines input)) :
    claimsFrom I r (I.publicLines input) (expectedValues I input r) h =
      (I.publicLines input).map (lineClaim I r) := by
  apply Vector.ext
  intro i hi
  simp only [claimsFrom, claimsWith, Vector.getElem_ofFn, Vector.getElem_map, lineClaim,
    Fin.getElem_fin]
  split_ifs with hsent
  · congr 1
    simp only [expectedValues, sentBefore]
    rw [List.getElem_eq_iff, List.getElem?_map,
      getElem?_filter_length_take (fun l : PublicLine I.toShape ↦ l.sent)
        (I.publicLines input).toList i (by simpa using hi) (by simpa using hsent)]
    simp
  · rfl

/-- The pool from the expected values is the pool of the lines' claims. -/
theorem pooledFrom_expected (s : I.Stmt × TableOut I) (r : E)
    (h : (expectedValues I s.1 r).length = sentCount I (I.publicLines s.1)) :
    pooledFrom I s r (expectedValues I s.1 r) h = pooled I s r := by
  simp only [pooledFrom, pooled, claimsFrom_expected]

/-- A claim is in the pool exactly when it was received or is a line's claim. -/
private theorem mem_pooled (s : I.Stmt × TableOut I) (r : E) (c : ColumnClaim I) :
    c ∈ (pooled I s r).2.columns.toList ↔
      c ∈ s.2.columns.toList ∨ ∃ l ∈ (I.publicLines s.1).toList, lineClaim I r l = c := by
  simp only [pooled, Vector.toList_append, Vector.toList_map, List.mem_append, List.mem_map]

/-- A line's claim holds of the stack exactly when the line through the stack's two cells,
evaluated at `r`, is the line through the statement's. -/
private theorem lineClaim_holds_iff (q : Column I.μ) (r : E) (l : PublicLine I.toShape) :
    (lineClaim I r l).Holds q ↔
      (1 - r) * ofK ((I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩) +
          r * ofK ((I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩) =
        (1 + r) * ofK l.cell0 + r * ofK l.cell1 := by
  unfold ColumnClaim.Holds lineClaim
  rw [eval₂Mle_linePoint l.pos]
  exact Iff.rfl

/-- Two lines through cells in `K` that differ agree at one challenge at most: the difference is
a polynomial of degree one in `r` with a nonzero coefficient. -/
private theorem line_challenge_unique {a b c0 c1 : K} (hne : ¬ (a = c0 ∧ b = c1)) {r₁ r₂ : E}
    (h₁ : (1 - r₁) * ofK a + r₁ * ofK b = (1 + r₁) * ofK c0 + r₁ * ofK c1)
    (h₂ : (1 - r₂) * ofK a + r₂ * ofK b = (1 + r₂) * ofK c0 + r₂ * ofK c1) : r₁ = r₂ := by
  have e₁ : (ofK a - ofK c0) + r₁ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₁
  have e₂ : (ofK a - ofK c0) + r₂ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₂
  by_cases hβ : ofK b - ofK a - ofK c0 - ofK c1 = 0
  · exfalso
    apply hne
    have hα : ofK a = ofK c0 := by
      rw [hβ, mul_zero, add_zero, sub_eq_zero] at e₁
      exact e₁
    refine ⟨ofK_injective hα, ofK_injective ?_⟩
    have hb : ofK b = ofK c0 + ofK c0 + ofK c1 := by linear_combination hβ + hα
    rw [hb, CharTwo.add_self_eq_zero, zero_add]
  · have h : (r₁ - r₂) * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
      linear_combination e₁ - e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hβ)

/-- Acceptance of the deployed check at two distinct challenges fixes the memory. The cells `a`
and `b` are cells 0 and 1 of the three memory limbs and `w₀`, `w₁` the two public words. At the
challenge `r` the three claims on the limbs' lines read `c_ℓ = (1 - r)·a_ℓ + r·b_ℓ` for the two
sent limbs and `0 = (1 - r)·a₂ + r·b₂` for the top limb, whose claim the verifier pools at `0`
(the third limb is `F192::ZERO` at `cpu/mod.rs:746`, and `bind_pi_claim` pools it, `:674-682`),
and the check on the words reads `c₀ + y·c₁ = (1 + r)·w₀ + r·w₁`.
Both hold at two challenges `r₁ ≠ r₂` only if the cells are the words' limbs and the top limb's
cells are zero. -/
theorem accepts_two_challenges {a b : Fin 3 → K} {w₀ w₁ r₁ r₂ c₀ c₁ d₀ d₁ : E} (hr : r₁ ≠ r₂)
    (h₁ : c₀ = (1 - r₁) * ofK (a 0) + r₁ * ofK (b 0) ∧
      c₁ = (1 - r₁) * ofK (a 1) + r₁ * ofK (b 1) ∧
      0 = (1 - r₁) * ofK (a 2) + r₁ * ofK (b 2) ∧
      c₀ + y * c₁ = (1 + r₁) * w₀ + r₁ * w₁)
    (h₂ : d₀ = (1 - r₂) * ofK (a 0) + r₂ * ofK (b 0) ∧
      d₁ = (1 - r₂) * ofK (a 1) + r₂ * ofK (b 1) ∧
      0 = (1 - r₂) * ofK (a 2) + r₂ * ofK (b 2) ∧
      d₀ + y * d₁ = (1 + r₂) * w₀ + r₂ * w₁) :
    w₀ = E.ofLimbs (a 0) (a 1) 0 ∧ w₁ = E.ofLimbs (b 0) (b 1) 0 ∧ a 2 = 0 ∧ b 2 = 0 := by
  obtain ⟨e₀, e₁, e₂, e₃⟩ := h₁
  obtain ⟨f₀, f₁, f₂, f₃⟩ := h₂
  have hr' : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hr
  -- On the words: `α + r·β = 0` at both challenges, with `α = A - w₀`, `β = B - A - w₀ - w₁`.
  have g₁ : (ofK (a 0) + y * ofK (a 1) - w₀) +
      r₁ * (ofK (b 0) + y * ofK (b 1) - (ofK (a 0) + y * ofK (a 1)) - w₀ - w₁) = 0 := by
    linear_combination e₃ - e₀ - y * e₁
  have g₂ : (ofK (a 0) + y * ofK (a 1) - w₀) +
      r₂ * (ofK (b 0) + y * ofK (b 1) - (ofK (a 0) + y * ofK (a 1)) - w₀ - w₁) = 0 := by
    linear_combination f₃ - f₀ - y * f₁
  have hβ : ofK (b 0) + y * ofK (b 1) - (ofK (a 0) + y * ofK (a 1)) - w₀ - w₁ = 0 :=
    (mul_eq_zero.mp (show (r₁ - r₂) * (ofK (b 0) + y * ofK (b 1) -
      (ofK (a 0) + y * ofK (a 1)) - w₀ - w₁) = 0 by linear_combination g₁ - g₂)).resolve_left hr'
  have hα : ofK (a 0) + y * ofK (a 1) - w₀ = 0 := by linear_combination g₁ - r₁ * hβ
  -- On the top limb: `a₂ + r·(b₂ - a₂) = 0` at both challenges.
  have hc : ofK (b 2) - ofK (a 2) = 0 :=
    (mul_eq_zero.mp (show (r₁ - r₂) * (ofK (b 2) - ofK (a 2)) = 0 by
      linear_combination f₂ - e₂)).resolve_left hr'
  have ha : ofK (a 2) = 0 := by linear_combination -e₂ - r₁ * hc
  have hb : ofK (b 2) = 0 := by linear_combination hc + ha
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  refine ⟨?_, ?_, ofK_injective (ha.trans h0.symm), ofK_injective (hb.trans h0.symm)⟩
  · rw [ofLimbs_eq, h0]
    linear_combination -hα
  · rw [ofLimbs_eq, h0]
    linear_combination -hβ - hα - CharTwo.add_self_eq_zero w₀

/-- On a stack in the table seam, the pool is in the public seam: the received claims still
hold, and each line's claim holds by the line identity. -/
private theorem pooled_mem_pub (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (h : ((s, o), ()) ∈ Seam.table I) (r : E) : ((pooled I s r, o), ()) ∈ Seam.pub I := by
  obtain ⟨hcols, hlines, haux⟩ := h
  refine ⟨fun c hc ↦ ?_, haux⟩
  rcases (mem_pooled I s r c).mp hc with hc | ⟨l, hl, rfl⟩
  · exact hcols c hc
  · obtain ⟨h0, h1⟩ := hlines l hl
    rw [lineClaim_holds_iff, h0, h1, CharTwo.sub_eq_add]

/-- A challenge is bad for a stack and statement outside the table seam when the pool at that
challenge is inside the public seam; two bad challenges are equal. -/
private theorem bad_challenge_unique (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (hin : ((s, o), ()) ∉ Seam.table I) {r₁ r₂ : E}
    (h₁ : ((pooled I s r₁, o), ()) ∈ Seam.pub I)
    (h₂ : ((pooled I s r₂, o), ()) ∈ Seam.pub I) : r₁ = r₂ := by
  obtain ⟨hcols₁, haux⟩ := h₁
  obtain ⟨hcols₂, -⟩ := h₂
  have hold : ∀ c ∈ s.2.columns.toList, c.Holds (theStack o) := fun c hc ↦
    hcols₁ c ((mem_pooled I s r₁ c).mpr (Or.inl hc))
  have hlines : ¬ I.PublicLinesHold s.1 (theStack o) := fun hl ↦ hin ⟨hold, hl, haux⟩
  simp only [M3Instance.PublicLinesHold, not_forall] at hlines
  obtain ⟨l, hl, hne⟩ := hlines
  have hc₁ := hcols₁ _ ((mem_pooled I s r₁ _).mpr (Or.inr ⟨l, hl, rfl⟩))
  have hc₂ := hcols₂ _ ((mem_pooled I s r₂ _).mpr (Or.inr ⟨l, hl, rfl⟩))
  rw [lineClaim_holds_iff] at hc₁ hc₂
  exact line_challenge_unique hne hc₁ hc₂

/-! ## The reduction -/

/-- The prover: receives the challenge, sends the values of the lines whose value is sent,
keeps the stack, and outputs the pool. The values are functions of the public statement and the
challenge; on a stack whose lines hold they are the extensions of its columns at
`(r, 0, …, 0)`. -/
def prover : OracleProver []ₒ (I.Stmt × TableOut I) (TheOracle I) Unit
    (I.Stmt × PubOut I) (TheOracle I) Unit pubSpec where
  PrvState
    | ⟨0, _⟩ => ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit
    | _ => E × (((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit)
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun r ↦ (r, st)
    | ⟨1, h⟩ => nomatch h
  sendMessage
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st ↦ pure (expectedValues I st.2.1.1.1 st.1, st)
  output := fun st ↦ pure ((pooled I st.2.1.1 st.1, st.2.1.2), ())

/-- The verifier reads the prover's message. -/
def queryValues : OracleComp [pubSpec.Message]ₒ (List E) :=
  liftM <| OracleSpec.query
    (show [pubSpec.Message]ₒ.Domain from ⟨⟨1, by rfl⟩, (by change Unit; exact ())⟩)

/-- A verifier of the phase's shape: it reads the prover's values, rejects unless the message
has one value per sent line and `accept` holds of it at the challenge, and outputs `pool` of
it. It never reads the stack. The length is no check `accept` can drop: no pool exists
without it. -/
def verifierWith (accept : (I.Stmt × TableOut I) → E → List E → Bool)
    (pool : (s : I.Stmt × TableOut I) → E → (cs : List E) →
      cs.length = sentCount I (I.publicLines s.1) → I.Stmt × PubOut I) :
    FrontVerifier []ₒ (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if h : cs.length = sentCount I (I.publicLines s.1) then
      if accept s (chals ⟨0, rfl⟩) cs then pure (pool s (chals ⟨0, rfl⟩) cs h) else failure
    else failure

/-- The verifier: the check on the prover's values, then the pool from the values sent. -/
abbrev verifier : FrontVerifier []ₒ (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec :=
  verifierWith I (check I) (pooledFrom I)

/-- The deployed verifier: the check on the words, then the pool from the values sent. It is
the specification's verifier with `checkWords` for `check`: the schedule, the length of the
message and the pool are the same, and it never reads the stack. -/
abbrev deployedVerifier : FrontVerifier []ₒ (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec :=
  verifierWith I (checkWords I) (pooledFrom I)

/-! ## The verifier's verdict -/

/-- Reading the prover's message returns the transcript's entry. -/
private theorem simulateQ_queryValues (tr : pubSpec.FullTranscript) :
    simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      (OptionT.lift (liftM queryValues :
        OracleComp ([]ₒ + [pubSpec.Message]ₒ) (List E))).run =
      (pure (tr 1) : OptionT (OracleComp []ₒ) (List E)) := by
  have h : simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      (liftM queryValues : OracleComp ([]ₒ + [pubSpec.Message]ₒ) (List E)) =
      pure (tr 1) := rfl
  rw [OptionT.run_lift, simulateQ_bind, h, pure_bind, simulateQ_pure]
  rfl

variable (accept : (I.Stmt × TableOut I) → E → List E → Bool)
  (pool : (s : I.Stmt × TableOut I) → E → (cs : List E) →
    cs.length = sentCount I (I.publicLines s.1) → I.Stmt × PubOut I)

/-- The check of a verifier of the phase's shape, as one Boolean: the message has one value
per sent line, and `accept` holds of it at the challenge. -/
def accepts (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs.length = sentCount I (I.publicLines s.1)) && accept s r cs

/-- The verdict of a verifier of the phase's shape: `pool` of a message with one value per
sent line. On any other message the verifier rejects, so the value here, the computed pool, is
never output. -/
def verdict (s : I.Stmt × TableOut I) (r : E) (cs : List E) : I.Stmt × PubOut I :=
  if h : cs.length = sentCount I (I.publicLines s.1) then pool s r cs h else pooled I s r

/-- The computation of a verifier of the phase's shape, once the message is read off the
transcript: the verdict at the transcript's values and challenge if the check holds of them, a
rejection otherwise. -/
theorem verify_simulated (s : I.Stmt × TableOut I) (tr : pubSpec.FullTranscript) :
    OptionT.mk (simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      ((verifierWith I accept pool).verify s tr.challenges).run) =
      if accepts I accept s (tr 0) (tr 1) then pure (verdict I pool s (tr 0) (tr 1))
      else failure := by
  simp only [verifierWith]
  rw [show (liftM queryValues : OptionT (OracleComp ([]ₒ + [pubSpec.Message]ₒ)) (List E)) =
      OptionT.lift (liftM queryValues : OracleComp ([]ₒ + [pubSpec.Message]ₒ) (List E)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  unfold accepts verdict
  by_cases hl : (tr 1).length = sentCount I (I.publicLines s.1)
  · rw [dite_eq_left hl, dite_eq_left hl, decide_eq_true hl, Bool.true_and]
    by_cases h : accept s (tr 0) (tr 1) = true
    · rw [ite_eq_left h, ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
      rfl
  · rw [dite_eq_right hl, decide_eq_false hl, Bool.false_and, ite_eq_right Bool.false_ne_true]
    rfl

/-- A verifier of the phase's shape is a check followed by a verdict, as data. -/
def guardedWith :
    ((verifierWith I accept pool).toOracleVerifier (TheOracle I)).toVerifier.GuardedForm :=
  (verifierWith I accept pool).guardedForm (TheOracle I)
    (fun s tr ↦ accepts I accept s (tr 0) (tr 1)) (fun s tr ↦ verdict I pool s (tr 0) (tr 1))
    (verify_simulated I accept pool)

/-- The verifier is the check followed by the pool from the values sent, as data. -/
def guarded : ((verifier I).toOracleVerifier (TheOracle I)).toVerifier.GuardedForm :=
  guardedWith I (check I) (pooledFrom I)

/-- The deployed verifier is the check on the words followed by the pool from the values sent,
as data. -/
def deployedGuarded :
    ((deployedVerifier I).toOracleVerifier (TheOracle I)).toVerifier.GuardedForm :=
  guardedWith I (checkWords I) (pooledFrom I)

/-- The verifier's check holds exactly when the specification's check does: that check fixes
the length. -/
theorem accepts_check_iff (s : I.Stmt × TableOut I) (r : E) (cs : List E) :
    accepts I (check I) s r cs = true ↔ check I s r cs = true := by
  unfold accepts
  rw [Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨And.right, fun hc ↦
    ⟨by rw [(check_eq_true_iff I s r cs).mp hc, expectedValues_length], hc⟩⟩

/-- When the check passes, the verdict is the pool of the lines' claims. -/
theorem verdict_pooledFrom_of_check {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (hc : check I s r cs = true) : verdict I (pooledFrom I) s r cs = pooled I s r := by
  have hl : cs.length = sentCount I (I.publicLines s.1) := by
    rw [(check_eq_true_iff I s r cs).mp hc, expectedValues_length]
  rw [verdict, dite_eq_left hl]
  obtain rfl := (check_eq_true_iff I s r cs).mp hc
  exact pooledFrom_expected I s r hl

/-! ## Completeness -/

/-- In every run of the prover, the message is the expected values at the transcript's
challenge and the output is the pool at that challenge, with the stack. -/
private theorem prover_run_support (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (pr : pubSpec.FullTranscript × ((I.Stmt × PubOut I) × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((prover I).run (s, o) ())) :
    pr.1 1 = expectedValues I s.1 (pr.1 0) ∧ pr.2 = ((pooled I s (pr.1 0), o), ()) := by
  have h0 : pubSpec.dir 0 = .V_to_P := rfl
  have h1 : pubSpec.dir 1 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1] at hpr
  simp only [ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Challenge, Fin.reduceLast, prover,
    Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, id_eq, HasQuery.instOfMonadLift_query, toPFunctor_emptySpec, liftM_pure,
    bind_pure_comp, map_pure, pure_bind, Functor.map_map, support_map, Set.mem_image] at hpr
  obtain ⟨r, -, rfl⟩ := hpr
  -- The transcript is the challenge followed by the message; its two entries are read off.
  exact ⟨rfl, rfl⟩

/-- For every challenge, some run of the prover receives it, sends the expected values at it
and outputs the pool at it, with the stack. -/
theorem exists_mem_support_prover_run (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (r : E) :
    ∃ pr ∈ support ((prover I).run (s, o) ()),
      pr.1 0 = r ∧ pr.1 1 = expectedValues I s.1 r ∧ pr.2 = ((pooled I s r, o), ()) := by
  have h0 : pubSpec.dir 0 = .V_to_P := rfl
  have h1 : pubSpec.dir 1 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1]
  simp only [ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Challenge, Fin.reduceLast, prover,
    Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, id_eq, HasQuery.instOfMonadLift_query, toPFunctor_emptySpec, liftM_pure,
    bind_pure_comp, map_pure, pure_bind, Functor.map_map, support_map, Set.mem_image]
  refine ⟨_, ⟨r, ?_, rfl⟩, rfl, rfl, rfl⟩
  exact mem_support_query _ r

/-- Perfect completeness of a verifier of the phase's shape that pools the values sent, given
that its check accepts what the specification's does: from the table seam, the prover's values
pass the specification's check at every challenge, so they pass `accept`, and the pool lands in
the public seam. -/
private theorem complete_with
    (hacc : ∀ s r cs, check I s r cs = true → accepts I accept s r cs = true)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (prover I)
      ((verifierWith I accept (pooledFrom I)).toOracleVerifier (TheOracle I))).perfectCompleteness
        init impl (Seam.table I) (Seam.pub I) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ :=
    Reduction.mem_support_run_of_guarded _ (guardedWith I accept (pooledFrom I)) (s, o) witIn hx
  obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
  have hc : check I s (pr.1 0) (pr.1 1) = true := decide_eq_true hmsg
  have hacc' : (guardedWith I accept (pooledFrom I)).check (s, o) pr.1 = true := hacc _ _ _ hc
  have hpool : verdict I (pooledFrom I) s (pr.1 0) (pr.1 1) = pooled I s (pr.1 0) :=
    verdict_pooledFrom_of_check I hc
  rw [ite_eq_left hacc']
  refine ⟨_, rfl, ?_, ?_⟩
  · show ((verdict I (pooledFrom I) s (pr.1 0) (pr.1 1), o), ()) ∈ Seam.pub I
    rw [hpool]
    exact pooled_mem_pub I s o hIn (pr.1 0)
  · show pr.2.1 = (verdict I (pooledFrom I) s (pr.1 0) (pr.1 1), o)
    rw [hpool]
    exact congrArg Prod.fst hout

/-- Perfect completeness: from the table seam, the prover's values pass the check at every
challenge and the pool lands in the public seam. -/
theorem complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (prover I)
      ((verifier I).toOracleVerifier (TheOracle I))).perfectCompleteness init impl (Seam.table I)
      (Seam.pub I) :=
  complete_with I (check I) (fun _ _ _ hc ↦ (accepts_check_iff I _ _ _).mpr hc) init impl

/-- The deployed verifier's check holds wherever the specification's does, and it too fixes the
length. -/
private theorem accepts_checkWords_of_check {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (hc : check I s r cs = true) : accepts I (checkWords I) s r cs = true := by
  have h := (accepts_check_iff I s r cs).mpr hc
  unfold accepts at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, checkWords_of_check I hc⟩

/-- Perfect completeness of the deployed phase: its prover is the specification's, whose values
pass the specification's check and so the check on the words, and its pool is the same. -/
theorem deployed_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (prover I)
      ((deployedVerifier I).toOracleVerifier (TheOracle I))).perfectCompleteness init impl
      (Seam.table I) (Seam.pub I) :=
  complete_with I (checkWords I) (fun _ _ _ ↦ accepts_checkWords_of_check I) init impl

/-! ## Knowledge soundness -/

/-! ### The bad challenge of the deployed check -/

/-- An element of a filtered list comes from a position of the original, and its index in the
filtered list is the number of kept elements before that position: the converse of
`getElem?_filter_length_take`. -/
private theorem exists_index_of_getElem?_filter {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : ℕ) (a : α), (l.filter p)[k]? = some a →
      ∃ (i : ℕ) (hi : i < l.length),
        p l[i] = true ∧ ((l.take i).filter p).length = k ∧ l[i] = a
  | [], k, a, h => by simp at h
  | b :: l, k, a, h => by
    by_cases hb : p b = true
    · cases k with
      | zero =>
        simp only [List.filter_cons_of_pos hb, List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, by simp, hb, by simp, by simp [h]⟩
      | succ k =>
        simp only [List.filter_cons_of_pos hb, List.getElem?_cons_succ] at h
        obtain ⟨i, hi, hpi, hk, hia⟩ := exists_index_of_getElem?_filter p l k a h
        exact ⟨i + 1, by simpa using hi, by simpa using hpi,
          by simp [List.filter_cons_of_pos hb, hk], by simpa using hia⟩
    · simp only [List.filter_cons_of_neg hb] at h
      obtain ⟨i, hi, hpi, hk, hia⟩ := exists_index_of_getElem?_filter p l k a h
      exact ⟨i + 1, by simpa using hi, by simpa using hpi,
        by simp [List.filter_cons_of_neg hb, hk], by simpa using hia⟩

/-- The `k`-th sent line is some line `i` of the statement whose value is sent, with `k` sent
lines before it. -/
private theorem exists_sent_index {n : ℕ} (ls : Vector (PublicLine I.toShape) n) {k : ℕ}
    {l : PublicLine I.toShape} (h : (ls.toList.filter (·.sent))[k]? = some l) :
    ∃ i : Fin n, ls[i].sent = true ∧ sentBefore I ls i = k ∧ ls[i] = l := by
  obtain ⟨i, hi, hp, hk, hl⟩ := exists_index_of_getElem?_filter
    (fun l : PublicLine I.toShape ↦ l.sent) ls.toList k l h
  exact ⟨⟨i, by simpa using hi⟩, by simpa using hp, hk, by simpa using hl⟩

/-- A claim on a line's column at `(r, 0, …, 0)` holds of a stack exactly when the line through
the stack's two cells, evaluated at `r`, is the claimed value. -/
private theorem claim_holds_iff (q : Column I.μ) (r v : E) (l : PublicLine I.toShape) :
    (⟨l.col, linePoint l.pos r, v⟩ : ColumnClaim I).Holds q ↔
      (1 - r) * ofK ((I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩) +
          r * ofK ((I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩) = v := by
  unfold ColumnClaim.Holds
  rw [eval₂Mle_linePoint l.pos]

/-- Two sent lines whose cells differ from the statement's agree on the words at one challenge at
most: the equation on the words is `α + r·β = 0` in `E`, and by `accepts_two_challenges` two
challenges would fix all four cells. -/
private theorem pair_challenge_unique {a₀ b₀ a₁ b₁ c₀₀ c₀₁ c₁₀ c₁₁ : K}
    (hne : ¬ (a₀ = c₀₀ ∧ b₀ = c₀₁ ∧ a₁ = c₁₀ ∧ b₁ = c₁₁)) {r₁ r₂ : E}
    (h₁ : ((1 - r₁) * ofK a₀ + r₁ * ofK b₀) + y * ((1 - r₁) * ofK a₁ + r₁ * ofK b₁) =
      (1 + r₁) * E.ofLimbs c₀₀ c₁₀ 0 + r₁ * E.ofLimbs c₀₁ c₁₁ 0)
    (h₂ : ((1 - r₂) * ofK a₀ + r₂ * ofK b₀) + y * ((1 - r₂) * ofK a₁ + r₂ * ofK b₁) =
      (1 + r₂) * E.ofLimbs c₀₀ c₁₀ 0 + r₂ * E.ofLimbs c₀₁ c₁₁ 0) : r₁ = r₂ := by
  by_contra hr
  have h0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  obtain ⟨hw₀, hw₁, -, -⟩ := accepts_two_challenges (a := ![a₀, a₁, 0]) (b := ![b₀, b₁, 0])
    (w₀ := E.ofLimbs c₀₀ c₁₀ 0) (w₁ := E.ofLimbs c₀₁ c₁₁ 0)
    (c₀ := (1 - r₁) * ofK a₀ + r₁ * ofK b₀) (c₁ := (1 - r₁) * ofK a₁ + r₁ * ofK b₁)
    (d₀ := (1 - r₂) * ofK a₀ + r₂ * ofK b₀) (d₁ := (1 - r₂) * ofK a₁ + r₂ * ofK b₁) hr
    ⟨rfl, rfl, by simp [h0], h₁⟩ ⟨rfl, rfl, by simp [h0], h₂⟩
  apply hne
  have e₀ := congrArg (·.limb 0) hw₀
  have e₁ := congrArg (·.limb 1) hw₀
  have e₂ := congrArg (·.limb 0) hw₁
  have e₃ := congrArg (·.limb 1) hw₁
  simp only [limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one] at e₀ e₁ e₂ e₃
  exact ⟨e₀.symm, e₂.symm, e₁.symm, e₃.symm⟩

/-- What the public seam says of the pool from a message with one value per sent line: the
received claims hold, and the claim on each line holds, at the value sent for a line whose value
is sent and at the value the verifier computes for the others. -/
private theorem pool_holds {s : I.Stmt × TableOut I} {o : ∀ i, TheOracle I i} {r : E}
    {cs : List E} {h : cs.length = sentCount I (I.publicLines s.1)}
    (hp : ((pooledFrom I s r cs h, o), ()) ∈ Seam.pub I) :
    (∀ c ∈ s.2.columns.toList, c.Holds (theStack o)) ∧
      ∀ i : Fin I.nLines,
        (1 - r) * ofK ((I.column (theStack o) (I.publicLines s.1)[i].col).values.get
            ⟨0, Nat.two_pow_pos _⟩) +
          r * ofK ((I.column (theStack o) (I.publicLines s.1)[i].col).values.get
            ⟨1, Nat.one_lt_two_pow (I.publicLines s.1)[i].pos.ne'⟩) =
        if hs : (I.publicLines s.1)[i].sent then
          cs[sentBefore I (I.publicLines s.1) i]'
            (lt_of_lt_of_eq (sentBefore_lt I _ i hs) h.symm)
        else lineValue I r (I.publicLines s.1)[i] := by
  obtain ⟨hcols, -⟩ := hp
  refine ⟨fun c hc ↦ hcols c ?_, fun i ↦ ?_⟩
  · simp only [pooledFrom, Vector.toList_append, List.mem_append]
    exact Or.inl hc
  · have hc := hcols _ (show _ ∈ (pooledFrom I s r cs h).2.columns.toList by
      simp only [pooledFrom, claimsFrom, claimsWith, Vector.toList_append, Vector.toList_ofFn,
        List.mem_append, List.mem_ofFn]
      exact Or.inr ⟨i, rfl⟩)
    exact (claim_holds_iff I (theStack o) r _ _).mp hc

/-- Outside the table seam, at most one challenge has a message that the check on the words
accepts with a verdict in the public seam: a line that is not sent differs, or a sent line does
and the pooled claims turn the equation on the words into one on the stack's cells. -/
private theorem bad_challenge_unique_words (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (hin : ((s, o), ()) ∉ Seam.table I) {r₁ r₂ : E} {cs₁ cs₂ : List E}
    (h₁ : accepts I (checkWords I) s r₁ cs₁ = true ∧
      ((verdict I (pooledFrom I) s r₁ cs₁, o), ()) ∈ Seam.pub I)
    (h₂ : accepts I (checkWords I) s r₂ cs₂ = true ∧
      ((verdict I (pooledFrom I) s r₂ cs₂, o), ()) ∈ Seam.pub I) : r₁ = r₂ := by
  obtain ⟨ha₁, hp₁⟩ := h₁
  obtain ⟨ha₂, hp₂⟩ := h₂
  unfold accepts at ha₁ ha₂
  rw [Bool.and_eq_true, decide_eq_true_iff] at ha₁ ha₂
  obtain ⟨hl₁, hw₁⟩ := ha₁
  obtain ⟨hl₂, hw₂⟩ := ha₂
  rw [verdict, dite_eq_left hl₁] at hp₁
  rw [verdict, dite_eq_left hl₂] at hp₂
  obtain ⟨hold, hline₁⟩ := pool_holds I hp₁
  obtain ⟨-, hline₂⟩ := pool_holds I hp₂
  have haux : I.aux (theStack o) := by
    have hp := hp₁
    obtain ⟨-, haux⟩ := hp
    exact haux
  have hlines : ¬ I.PublicLinesHold s.1 (theStack o) := fun hl ↦ hin ⟨hold, hl, haux⟩
  simp only [M3Instance.PublicLinesHold, not_forall] at hlines
  obtain ⟨l, hl, hne⟩ := hlines
  -- Off the deployed shape the check is the specification's.
  have fallback : (∀ r cs, checkWords I s r cs = true → check I s r cs = true) → r₁ = r₂ := by
    intro hfb
    have e₁ : pooledFrom I s r₁ cs₁ hl₁ = pooled I s r₁ := by
      have := verdict_pooledFrom_of_check I (hfb r₁ cs₁ hw₁)
      rwa [verdict, dite_eq_left hl₁] at this
    have e₂ : pooledFrom I s r₂ cs₂ hl₂ = pooled I s r₂ := by
      have := verdict_pooledFrom_of_check I (hfb r₂ cs₂ hw₂)
      rwa [verdict, dite_eq_left hl₂] at this
    rw [e₁] at hp₁
    rw [e₂] at hp₂
    exact bad_challenge_unique I s o hin hp₁ hp₂
  rcases hf : (I.publicLines s.1).toList.filter (·.sent) with _ | ⟨l₀, _ | ⟨l₁, _ | ⟨l₂, ls⟩⟩⟩
  -- No sent line, and one sent line.
  · exact fallback fun r cs hw ↦ by simpa [checkWords, hf] using hw
  · exact fallback fun r cs hw ↦ by simpa [checkWords, hf] using hw
  -- Three or more sent lines come last in the cases `rcases` gives; they are taken before the
  -- case of two, which the rest of the proof is.
  swap
  · exact fallback fun r cs hw ↦ by simpa [checkWords, hf] using hw
  -- Two sent lines, and a message of two values.
  have hlen₁ : cs₁.length = 2 := by rw [hl₁]; simp [sentCount, hf]
  have hlen₂ : cs₂.length = 2 := by rw [hl₂]; simp [sentCount, hf]
  obtain ⟨c₀, c₁, rfl⟩ := List.length_eq_two.mp hlen₁
  obtain ⟨d₀, d₁, rfl⟩ := List.length_eq_two.mp hlen₂
  have hweq₁ : c₀ + y * c₁ =
      (1 + r₁) * E.ofLimbs l₀.cell0 l₁.cell0 0 + r₁ * E.ofLimbs l₀.cell1 l₁.cell1 0 := by
    simpa [checkWords, hf] using hw₁
  have hweq₂ : d₀ + y * d₁ =
      (1 + r₂) * E.ofLimbs l₀.cell0 l₁.cell0 0 + r₂ * E.ofLimbs l₀.cell1 l₁.cell1 0 := by
    simpa [checkWords, hf] using hw₂
  obtain ⟨i₀, hs₀, hb₀, rfl⟩ :=
    exists_sent_index I (I.publicLines s.1) (k := 0) (l := l₀) (by rw [hf]; rfl)
  obtain ⟨i₁, hs₁, hb₁, rfl⟩ :=
    exists_sent_index I (I.publicLines s.1) (k := 1) (l := l₁) (by rw [hf]; rfl)
  have idx : ∀ (x z : E) (k : ℕ) (hk : k < [x, z].length),
      (k = 0 → [x, z][k] = x) ∧ (k = 1 → [x, z][k] = z) := by
    rintro x z k hk
    exact ⟨by rintro rfl; rfl, by rintro rfl; rfl⟩
  have u₀ := hline₁ i₀
  have u₁ := hline₁ i₁
  have v₀ := hline₂ i₀
  have v₁ := hline₂ i₁
  rw [dite_eq_left hs₀, (idx _ _ _ _).1 hb₀] at u₀ v₀
  rw [dite_eq_left hs₁, (idx _ _ _ _).2 hb₁] at u₁ v₁
  by_cases hA : (I.column (theStack o) (I.publicLines s.1)[i₀].col).values.get
        ⟨0, Nat.two_pow_pos _⟩ = (I.publicLines s.1)[i₀].cell0 ∧
      (I.column (theStack o) (I.publicLines s.1)[i₀].col).values.get
        ⟨1, Nat.one_lt_two_pow (I.publicLines s.1)[i₀].pos.ne'⟩ = (I.publicLines s.1)[i₀].cell1 ∧
      (I.column (theStack o) (I.publicLines s.1)[i₁].col).values.get
        ⟨0, Nat.two_pow_pos _⟩ = (I.publicLines s.1)[i₁].cell0 ∧
      (I.column (theStack o) (I.publicLines s.1)[i₁].col).values.get
        ⟨1, Nat.one_lt_two_pow (I.publicLines s.1)[i₁].pos.ne'⟩ = (I.publicLines s.1)[i₁].cell1
  · -- Both sent lines hold their cells, so the line that fails is not sent.
    by_cases hsl : l.sent = true
    · exfalso
      have hmem : l ∈ [(I.publicLines s.1)[i₀], (I.publicLines s.1)[i₁]] := by
        rw [← hf]
        exact List.mem_filter.mpr ⟨hl, hsl⟩
      rcases List.mem_pair.mp hmem with rfl | rfl
      · exact hne ⟨hA.1, hA.2.1⟩
      · exact hne ⟨hA.2.2.1, hA.2.2.2⟩
    · obtain ⟨j, hj, hjl⟩ := List.mem_iff_getElem.mp hl
      have hjl' : (I.publicLines s.1)[(⟨j, by simpa using hj⟩ : Fin I.nLines)] = l := by
        simpa using hjl
      subst hjl'
      have w₁ := hline₁ ⟨j, by simpa using hj⟩
      have w₂ := hline₂ ⟨j, by simpa using hj⟩
      rw [dite_eq_right hsl] at w₁ w₂
      exact line_challenge_unique hne w₁ w₂
  · exact pair_challenge_unique hA (by rw [u₀, u₁]; exact hweq₁) (by rw [v₀, v₁]; exact hweq₂)

/-- The extractor keeps the trivial witness: the stack is the oracle. The shared oracle is
written `OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to pin a universe
`Extractor.RoundByRound` leaves free. -/
def extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) Unit Unit pubSpec (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: before the challenge, the table seam; after the challenge,
the public seam of the pool at it; after the prover's values, that the verifier's check passes
and its verdict is in the public seam. -/
def stateFunction :
    ((verifier I).toOracleVerifier (TheOracle I)).toVerifier.KnowledgeStateFunction init impl
      (Seam.table I) (Seam.pub I) (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
    else
      accepts I (check I) stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
        ((verdict I (pooledFrom I) stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩), stmt.2), ()) ∈
          Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    obtain ⟨hc, hp⟩ := h
    rw [verdict_pooledFrom_of_check I ((accepts_check_iff I _ _ _).mp hc)] at hp
    exact hp
  toFun_full := fun stmt tr _ h ↦
    Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h

/-- Round-by-round knowledge soundness at the slot's error `1/|E|`: a bad transition is a bad
challenge, and there is at most one. -/
theorem rbr :
    ((verifier I).toOracleVerifier (TheOracle I)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (Seam.table I) (Seam.pub I) (fun _ ↦ Unit) (extractor I)
      (stateFunction I init impl) pubError := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨i, hi⟩ := i
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    · exact absurd hi (by decide)
  subst hi0
  show _ ≤ ((((1 : ℕ) : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
  rw [Nat.cast_one]
  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
  rintro r ⟨_, hin, hout⟩
  exact ⟨hin, hout⟩

/-- The knowledge state function of the deployed phase, with the specification's extractor: before
the challenge, the table seam; after the challenge, that some message passes the check on the
words with a verdict in the public seam; after the prover's values, that they pass and that their
verdict is in the public seam. For the specification's check the message is a function of the
statement and the challenge, and the state after the challenge is that its pool is in the public
seam; under the check on the words it is not, so that state is the existence of a message. -/
def deployedStateFunction :
    ((deployedVerifier I).toOracleVerifier (TheOracle I)).toVerifier.KnowledgeStateFunction init
      impl (Seam.table I) (Seam.pub I) (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ∃ cs, accepts I (checkWords I) stmt.1 (tr ⟨0, by omega⟩) cs = true ∧
        ((verdict I (pooledFrom I) stmt.1 (tr ⟨0, by omega⟩) cs, stmt.2), ()) ∈ Seam.pub I
    else
      accepts I (checkWords I) stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
        ((verdict I (pooledFrom I) stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩), stmt.2), ()) ∈
          Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    obtain ⟨hc, hp⟩ := h
    exact ⟨msg, hc, hp⟩
  toFun_full := fun stmt tr _ h ↦
    Verifier.GuardedForm.of_probEvent_pos (deployedGuarded I) init impl stmt tr _ h

/-- Round-by-round knowledge soundness of the deployed phase at the slot's error `1/|E|`: a bad
transition is a bad challenge, and there is at most one (`bad_challenge_unique_words`). -/
theorem deployed_rbr :
    ((deployedVerifier I).toOracleVerifier (TheOracle I)).toVerifier
      |>.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I) (Seam.pub I)
        (fun _ ↦ Unit) (extractor I) (deployedStateFunction I init impl) pubError := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨i, hi⟩ := i
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    · exact absurd hi (by decide)
  subst hi0
  show _ ≤ ((((1 : ℕ) : ℝ≥0) / (Fintype.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
  rw [Nat.cast_one]
  refine le_trans (prEvent_mono _ _ _ ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ∃ cs, accepts I (checkWords I) s r cs = true ∧
      ((verdict I (pooledFrom I) s r cs, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ ?_)
  · rintro r ⟨_, hin, hout⟩
    exact ⟨hin, hout⟩
  · obtain ⟨cs₁, hc₁⟩ := h₁.2
    obtain ⟨cs₂, hc₂⟩ := h₂.2
    exact bad_challenge_unique_words I s o h₁.1 hc₁ hc₂

end PublicInput

/-! ## The phase -/

variable (I : M3Instance)

/-- The public-input phase, at its slot: one challenge, one prover message, a front
verifier. -/
def publicInputPhase : Phase.FrontDef I (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec where
  prover := PublicInput.prover I
  verifier := PublicInput.verifier I

/-- The completeness half. -/
def publicInputComplete :
    Phase.Complete I (publicInputPhase I).toDef (Seam.table I) (Seam.pub I) where
  guarded := PublicInput.guarded I
  complete := PublicInput.complete I

/-- The security half, at the slot's error, with the extractor that keeps the trivial
witness. -/
def publicInputSecurity :
    Phase.Security I (publicInputPhase I).toDef (Seam.table I) (Seam.pub I) pubError where
  guarded := PublicInput.guarded I
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.stateFunction I
  rbr := PublicInput.rbr I

/-- The public-input phase of the deployed verifiers, at its slot: the specification's prover,
whose values are the lines' values, and a front verifier that checks them on the words. -/
def deployedPublicInputPhase :
    Phase.FrontDef I (I.Stmt × TableOut I) (I.Stmt × PubOut I) pubSpec where
  prover := PublicInput.prover I
  verifier := PublicInput.deployedVerifier I

/-- The completeness half of the deployed phase. -/
def deployedPublicInputComplete :
    Phase.Complete I (deployedPublicInputPhase I).toDef (Seam.table I) (Seam.pub I) where
  guarded := PublicInput.deployedGuarded I
  complete := PublicInput.deployed_complete I

/-- The security half of the deployed phase, at the slot's error, with the extractor that keeps
the trivial witness. -/
def deployedPublicInputSecurity :
    Phase.Security I (deployedPublicInputPhase I).toDef (Seam.table I) (Seam.pub I) pubError where
  guarded := PublicInput.deployedGuarded I
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.deployedStateFunction I
  rbr := PublicInput.deployed_rbr I

end
end LeanerVM.Protocol
