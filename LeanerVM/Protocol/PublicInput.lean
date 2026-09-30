/-
  LeanerVM.Protocol.PublicInput

  The public-input phase: the verifier draws a challenge, the prover sends the values it claims
  for the public columns on the line through their first two cells, and the verifier checks
  those values against the public statement and pools the claims. Both halves proved, at the
  slot's schedule and error.
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
values of the lines that are, in order, as one message. The verifier checks that message
against the lines' values, which fixes its length too, and pools one claim per line: for a
line whose value was sent, at the value *sent*, read off the message (`pooledFrom`), and for
the others at the value the verifier computes. Pooling the values sent is what makes the check
load-bearing: a verifier that pooled the values it computes would be knowledge sound with no
check at all. When the check passes the two pools agree (`pooledFrom_expected`), and the
proofs reason about the computed one, `pooled`. The verifier reads the transcript and never
the stack: it is a front verifier, `verifierWith` at the check and the pool, a shape the tests
reuse for the verifiers that omit or weaken the check.

Perfect completeness: on a stack whose lines hold, every pooled claim is true, by the identity
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)` and `-1 = 1` in `E`. Knowledge soundness at `1/|E|`,
the slot's error: the extractor keeps the trivial witness, since the stack is the oracle; if the
pooled claims hold and some line's cells differ from the statement's, that line's claim is a
nonzero polynomial of degree one in `r`, true at one challenge at most, whatever the number of
lines.

Written from the specification; the Rust verifier was read afterwards. It reads the same
transcript and checks one equation on the two public words instead of one per limb,
`c₀ + y·c₁ = (1 + r)·w₀ + r·w₁` (`crates/lean_vm/src/cpu/mod.rs:752-755`). The two equations
here imply that one, and it accepts transcripts they reject, so the theorems below are about
the specification's verifier.
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

/-! ## The schedule -/

/-- The schedule: the slot's, the verifier's challenge in `E`, then the prover's values as a
list; the verifier's check fixes its length, one value per line whose value is sent. -/
abbrev pSpec : ProtocolSpec 2 := pubSpec

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

theorem check_eq_true_iff (s : I.Stmt × TableOut I) (r : E) (cs : List E) :
    check I s r cs = true ↔ cs = expectedValues I s.1 r :=
  decide_eq_true_iff

/-- The number of lines before line `i` whose value is sent: the position of line `i`'s value
in the message, when it is sent. -/
def sentBefore {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (i : Fin n) : ℕ :=
  ((ls.toList.take i.val).filter (·.sent)).length

/-- The claims built from the message, one per line, on the line's column at `(r, 0, …, 0)`: a
line whose value is sent takes its value from the message, at its position among the sent
lines, and an unsent line takes the value the verifier computes. A missing value, which the
check never lets through, is the computed value. -/
def claimsFrom (r : E) {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (cs : List E) :
    Vector (ColumnClaim I) n :=
  Vector.ofFn fun i ↦
    ⟨ls[i].col, linePoint ls[i].pos r,
      if ls[i].sent then cs.getD (sentBefore I ls i) (lineValue I r ls[i])
      else lineValue I r ls[i]⟩

/-- What the verifier pools from the message: the claims it received, then one claim per
public line, from the values sent. -/
def pooledFrom (s : I.Stmt × TableOut I) (r : E) (cs : List E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs⟩)

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

/-- The claims from the expected values are the lines' claims: the value sent for a line is
its line value. -/
theorem claimsFrom_expected (r : E) (input : I.Stmt) :
    claimsFrom I r (I.publicLines input) (expectedValues I input r) =
      (I.publicLines input).map (lineClaim I r) := by
  apply Vector.ext
  intro i hi
  simp only [claimsFrom, Vector.getElem_ofFn, Vector.getElem_map, lineClaim, expectedValues,
    sentBefore, Fin.getElem_fin]
  split_ifs with hsent
  · congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      getElem?_filter_length_take (fun l : PublicLine I.toShape ↦ l.sent)
        (I.publicLines input).toList i (by simpa using hi) (by simpa using hsent)]
    simp
  · rfl

/-- The pool from the expected values is the pool of the lines' claims. -/
theorem pooledFrom_expected (s : I.Stmt × TableOut I) (r : E) :
    pooledFrom I s r (expectedValues I s.1 r) = pooled I s r := by
  simp only [pooledFrom, pooled, claimsFrom_expected]

/-- A claim is in the pool exactly when it was received or is a line's claim. -/
theorem mem_pooled (s : I.Stmt × TableOut I) (r : E) (c : ColumnClaim I) :
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
    (I.Stmt × PubOut I) (TheOracle I) Unit pSpec where
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
def queryValues : OracleComp [pSpec.Message]ₒ (List E) :=
  liftM <| OracleSpec.query
    (show [pSpec.Message]ₒ.Domain from ⟨⟨1, by rfl⟩, (by change Unit; exact ())⟩)

/-- A verifier of the phase's shape: it reads the prover's values, rejects unless `accept`
holds of them at the challenge, and outputs `pool` of them. It never reads the stack. -/
def verifierWith (accept : (I.Stmt × TableOut I) → E → List E → Bool)
    (pool : (I.Stmt × TableOut I) → E → List E → I.Stmt × PubOut I) :
    FrontVerifier []ₒ (I.Stmt × TableOut I) (I.Stmt × PubOut I) pSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if accept s (chals ⟨0, rfl⟩) cs then pure (pool s (chals ⟨0, rfl⟩) cs) else failure

/-- The verifier: the check on the prover's values, then the pool from the values sent. -/
abbrev verifier : FrontVerifier []ₒ (I.Stmt × TableOut I) (I.Stmt × PubOut I) pSpec :=
  verifierWith I (check I) (pooledFrom I)

/-! ## The verifier's verdict -/

/-- Reading the prover's message returns the transcript's entry. -/
private theorem simulateQ_queryValues (tr : pSpec.FullTranscript) :
    simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      (OptionT.lift (liftM queryValues :
        OracleComp ([]ₒ + [pSpec.Message]ₒ) (List E))).run =
      (pure (tr 1) : OptionT (OracleComp []ₒ) (List E)) := by
  have h : simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      (liftM queryValues : OracleComp ([]ₒ + [pSpec.Message]ₒ) (List E)) =
      pure (tr 1) := rfl
  rw [OptionT.run_lift, simulateQ_bind, h, pure_bind, simulateQ_pure]
  rfl

variable (accept : (I.Stmt × TableOut I) → E → List E → Bool)
  (pool : (I.Stmt × TableOut I) → E → List E → I.Stmt × PubOut I)

/-- The computation of a verifier of the phase's shape, once the message is read off the
transcript: `pool` of the transcript's values at its challenge if `accept` holds of them, a
rejection otherwise. -/
theorem verify_simulated (s : I.Stmt × TableOut I) (tr : pSpec.FullTranscript) :
    OptionT.mk (simulateQ (OracleInterface.simOracle []ₒ tr.messages)
      ((verifierWith I accept pool).verify s tr.challenges).run) =
      if accept s (tr 0) (tr 1) then pure (pool s (tr 0) (tr 1)) else failure := by
  simp only [verifierWith]
  rw [show (liftM queryValues : OptionT (OracleComp ([]ₒ + [pSpec.Message]ₒ)) (List E)) =
      OptionT.lift (liftM queryValues : OracleComp ([]ₒ + [pSpec.Message]ₒ) (List E)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  by_cases h : accept s (tr 0) (tr 1) = true
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- As an ordinary verifier: if `accept` holds of the transcript's values at its challenge, the
verdict is `pool` of them and the stack; otherwise it rejects. -/
theorem verifierWith_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (tr : pSpec.FullTranscript) :
    ((verifierWith I accept pool).toOracleVerifier (TheOracle I)).toVerifier.verify (s, o) tr =
      if accept s (tr 0) (tr 1) then pure (pool s (tr 0) (tr 1), o) else failure :=
  FrontVerifier.toVerifier_verify_of_check (verifierWith I accept pool)
    (fun s tr ↦ accept s (tr 0) (tr 1)) (fun s tr ↦ pool s (tr 0) (tr 1))
    (verify_simulated I accept pool) s o tr

/-- A verifier of the phase's shape is a check followed by a verdict, as data. -/
def guardedWith :
    ((verifierWith I accept pool).toOracleVerifier (TheOracle I)).toVerifier.GuardedForm :=
  (verifierWith I accept pool).guardedForm (TheOracle I) (fun s tr ↦ accept s (tr 0) (tr 1))
    (fun s tr ↦ pool s (tr 0) (tr 1)) (verify_simulated I accept pool)

/-- The verifier is the check followed by the pool from the values sent, as data. -/
def guarded : ((verifier I).toOracleVerifier (TheOracle I)).toVerifier.GuardedForm :=
  guardedWith I (check I) (pooledFrom I)

/-! ## Completeness -/

/-- In every run of the prover, the message is the expected values at the transcript's
challenge and the output is the pool at that challenge, with the stack. -/
private theorem prover_run_support (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (pr : pSpec.FullTranscript × ((I.Stmt × PubOut I) × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((prover I).run (s, o) ())) :
    pr.1 1 = expectedValues I s.1 (pr.1 0) ∧ pr.2 = ((pooled I s (pr.1 0), o), ()) := by
  have h0 : pSpec.dir 0 = .V_to_P := rfl
  have h1 : pSpec.dir 1 = .P_to_V := rfl
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
  have h0 : pSpec.dir 0 = .V_to_P := rfl
  have h1 : pSpec.dir 1 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1]
  simp only [ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Challenge, Fin.reduceLast, prover,
    Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, id_eq, HasQuery.instOfMonadLift_query, toPFunctor_emptySpec, liftM_pure,
    bind_pure_comp, map_pure, pure_bind, Functor.map_map, support_map, Set.mem_image]
  refine ⟨_, ⟨r, ?_, rfl⟩, rfl, rfl, rfl⟩
  exact mem_support_query _ r

/-- Perfect completeness: from the table seam, the prover's values pass the check at every
challenge and the pool lands in the public seam. -/
theorem complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (prover I)
      ((verifier I).toOracleVerifier (TheOracle I))).perfectCompleteness init impl (Seam.table I)
      (Seam.pub I) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded I) (s, o) witIn hx
  obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
  have hpool : pooledFrom I s (pr.1 0) (pr.1 1) = pooled I s (pr.1 0) := by
    rw [hmsg, pooledFrom_expected]
  rw [ite_eq_left hc]
  refine ⟨_, rfl, ?_, ?_⟩
  · show ((pooledFrom I s (pr.1 0) (pr.1 1), o), ()) ∈ Seam.pub I
    rw [hpool]
    exact pooled_mem_pub I s o hIn (pr.1 0)
  · show pr.2.1 = (pooledFrom I s (pr.1 0) (pr.1 1), o)
    rw [hpool]
    exact congrArg Prod.fst hout

/-! ## Knowledge soundness -/

/-- The extractor keeps the trivial witness: the stack is the oracle. The shared oracle is
written `OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to pin a universe
`Extractor.RoundByRound` leaves free. -/
def extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) Unit Unit pSpec (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: before the challenge, the table seam; after the challenge,
the public seam of the pool at it; after the prover's values, that the check passes and the
pool from those values is in the public seam. -/
def stateFunction :
    ((verifier I).toOracleVerifier (TheOracle I)).toVerifier.KnowledgeStateFunction init impl
      (Seam.table I) (Seam.pub I) (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
    else
      check I stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
        ((pooledFrom I stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩), stmt.2), ()) ∈ Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    obtain ⟨hc, hp⟩ := h
    have hpool := pooledFrom_expected I stmt.1 (tr.concat msg ⟨0, Nat.succ_pos _⟩)
    rw [(check_eq_true_iff I _ _ _).mp hc, hpool] at hp
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

end
end LeanerVM.Protocol
