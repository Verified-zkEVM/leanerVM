/-
  LeanerVM.Protocol.ToArkLib.Whir.Final

  The last level of WHIR's opening: the fold rounds, the plaintext table, the queries of the last
  word, and the sumcheck over the plaintext table with the verifier's terminal check; definition
  and perfect completeness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Whir.Level
public import LeanerVM.Protocol.ToArkLib.PassCheck

/-!
# The final level of WHIR's opening

Category B: Annex B, Protocol 1, final round, and `verify_whir` (`python-verifier/verifier.py`).
The last level starts like the others (`LeanerVM.Protocol.ToArkLib.Whir.Level`): a
running claim `<W, f> = c` on its table `f` of `ℓ + κ` variables, the first round polynomial of
its sumcheck received, and the honest word of `f` as the one oracle. Its rounds
(`finalSteps`):

1. the `ℓ` fold rounds and the residual claim's first-round polynomial, as at every level;
2. the folded table, `κ` variables, sent in the clear (`sendTable`): the opening commits to no
   further word;
3. the grinding nonce, the sampled positions and the batching challenge, as at every level;
4. the reading of the last word at the positions, each row folded at the fold point (`readFinal`,
   no round);
5. the query batch's first-round polynomial (`sendQueryPoly`);
6. the glue (`glueFinal`, no round): the residual and query claims summed with the scalars `1, λ`
   (there is no out-of-domain claim, and query `q` takes `λ^(1+q)`), the weight, the plaintext
   table and the claim now the statement of the tail;
7. the tail: the `κ` rounds of the sumcheck of the glued weight against the plaintext table, the
   first challenge (the polynomial is received) then each next polynomial and challenge
   (`tailFirst`, `tailRest`), the verifier computing nothing it does not receive;
8. the terminal check (`terminal`, no round): the running claim is the glued weight's extension at
   the tail's point times the plaintext table's, `W̃(t) · f̃(t)`. The weight's extension is the
   evaluator the statement carries (`Weight.mle`): a level's weight is the opening claim's, the
   out-of-domain and query weights of every level before, each at the suffix of the challenges
   the folds left it, and that composite evaluator is what `foldWeight` and `Weight.batch` build.

The terminal check is not a check against an oracle: the table is the prover's message and the
statement holds it.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Whir

/-- What the tail's sumcheck is about: the glued weight and the plaintext table. -/
abbrev TX (κ : ℕ) : Type := Weight E κ × Tab κ

section Final

variable (sh : Shape) (nf : ℕ)

/-- The family of claims of the tail: the plain sumcheck of the weight and the plaintext table
the statement holds. -/
def tailFamily : SumcheckRound.Family E (TX (nf + 1)) (OneW sh (nf + 1)) Unit 2 :=
  WhirSum.family fun ctx ↦ (ctx.1.1.1.onCube, ctx.1.1.2)

/-- The tail's family is honest up to its last variable. -/
theorem tailHonest : (tailFamily sh nf).Honest (nf + 1) :=
  WhirSum.family_honest _ le_rfl

/-- The folded table, sent in the clear. -/
def sendTable :=
  Component.sendChecked (StmtIn := Bd sh (nf + 1)) (StmtOut := Bd sh (nf + 1))
    (W := Tab (sh.ℓ + (nf + 1))) (OneW sh (nf + 1)) (Tab (nf + 1))
    (fun p ↦ foldTable p.2 p.1.1.r) (fun _ _ ↦ true) (fun s m ↦ { s with ff := m })

/-- The question to the last word: the sampled positions. -/
def readFinalQuery (s : Bd sh (nf + 1)) : [OneW sh (nf + 1)]ₒ.Domain := ⟨0, s.pos⟩

/-- The record of the answer: each row folded by the fold point. -/
def readFinalOut (s : Bd sh (nf + 1))
    (a : [OneW sh (nf + 1)]ₒ.Range (readFinalQuery sh nf s)) : Bd sh (nf + 1) :=
  { s with cq := fun q ↦ foldRow s.r ((a : Fin sh.t → Vector E (2 ^ sh.ℓ)) q) }

/-- The reading of the last word at the positions. -/
def readFinal :=
  Component.queryRecord (StmtIn := Bd sh (nf + 1)) (StmtOut := Bd sh (nf + 1))
    (W := Tab (sh.ℓ + (nf + 1))) (OneW sh (nf + 1)) (Function.Embedding.refl (Fin 1))
    (readFinalQuery sh nf) (fun _ _ ↦ true) (readFinalOut sh nf)

/-- The glued claim of the tail: the residual and query weights at `1, λ`, the plaintext table,
the claim's value and its first-round polynomial. The prover has no witness left. -/
def glueFinal :=
  Component.mapWitness (StmtIn := Bd sh (nf + 1))
    (StmtOut := SumcheckRound.MidStmt (TX (nf + 1)) E 0 2) (W := Tab (sh.ℓ + (nf + 1)))
    (W' := Unit)
    (Component.keptOracles (OneW sh (nf + 1)) (Function.Embedding.refl (Fin 1)))
    (fun s ↦ (((Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam] s.lam, s.ff),
      (#v[], powerBatch ![s.c, powerBatch s.cq s.lam] s.lam)),
      batchMessage ![s.p1, s.p3] s.lam))
    (fun _ ↦ ())

/-- The first challenge of the tail: the polynomial of the first round is already received. -/
def tailFirst : Component.Def (SumcheckRound.MidStmt (TX (nf + 1)) E 0 2) (OneW sh (nf + 1)) Unit
    (SumcheckRound.Stmt (TX (nf + 1)) E 1) (OneW sh (nf + 1)) Unit (draw E) :=
  SumcheckRound.drawChallenge 0 (tailFamily sh nf).weight

/-- The remaining rounds of the tail. -/
def tailRest : Component.Def (SumcheckRound.Stmt (TX (nf + 1)) E 1) (OneW sh (nf + 1)) Unit
    (SumcheckRound.Stmt (TX (nf + 1)) E (nf + 1)) (OneW sh (nf + 1)) Unit (roundsSpec E 2 nf) :=
  SumcheckRound.rounds (tailFamily sh nf).poly (tailFamily sh nf).weight (nf + 1) nf 1
    (by omega)

/-- The terminal check: the running claim is the weight's extension at the tail's point times the
plaintext table's. -/
def terminal :=
  Component.passCheck (StmtIn := SumcheckRound.Stmt (TX (nf + 1)) E (nf + 1)) (StmtOut := Unit)
    (W := Unit) (OneW sh (nf + 1))
    (fun s ↦ decide (s.1.1.mle s.2.1 * evalMle s.1.2 s.2.1 = s.2.2)) (fun _ ↦ ())

/-- Completeness of the folded table: it is the fold of the table. -/
def sendTableComplete : Component.Complete (sendTable sh nf)
    (relOld sh (nf + 1) Bd.F1) (relOld sh (nf + 1) Bd.G2) :=
  Component.sendCheckedComplete _ _ _ _ _ fun _ _ _ h ↦ ⟨rfl, h.1, h.2, rfl⟩

/-- Completeness of the reading: the last word's rows at the positions, folded, are the folded
table's encodings there. -/
def readFinalComplete : Component.Complete (readFinal sh nf)
    (relOld sh (nf + 1) Bd.G2) (relOld sh (nf + 1) Bd.G3) :=
  Component.queryRecordComplete _ _ _ _ _ fun s o w h ↦ by
    obtain ⟨h1, h2⟩ := h
    have h1' : (o 0 : Word sh.ℓ (nf + 1 + sh.R) sh.t) =
        wordOf sh.ℓ (nf + 1) sh.R sh.t w := h1
    have hans : (Component.answerOf (OneW sh (nf + 1)) o (readFinalQuery sh nf s) :
        Fin sh.t → Vector E (2 ^ sh.ℓ)) =
        fun k ↦ (wordOf sh.ℓ (nf + 1) sh.R sh.t w).row (s.pos k) := by
      have h0 : (Component.answerOf (OneW sh (nf + 1)) o (readFinalQuery sh nf s) :
          Fin sh.t → Vector E (2 ^ sh.ℓ)) =
          fun k ↦ (o 0 : Word sh.ℓ (nf + 1 + sh.R) sh.t).row (s.pos k) := rfl
      rw [h0, h1']
    refine ⟨rfl, h1, h2, fun q ↦ ?_⟩
    show foldRow s.r ((Component.answerOf _ o (readFinalQuery sh nf s) :
      Fin sh.t → Vector E (2 ^ sh.ℓ)) q) = _
    rw [hans]
    exact foldRow_wordOf sh.R sh.t w s.r (s.pos q)

/-- Completeness of the glue: the glued claim, polynomial and weight are those of the residual and
query claims on the folded table, which the statement holds. -/
def glueFinalComplete : Component.Complete (glueFinal sh nf) (relOld sh (nf + 1) Bd.G4)
    (SumcheckRound.relMid (tailFamily sh nf) 0) :=
  Component.mapWitnessComplete _ _ _ fun s o w h ↦ by
    obtain ⟨-, ⟨⟨⟨⟨hc, hp1⟩, hff⟩, hcq⟩, hp3⟩⟩ := h
    have hcqf : s.cq = fun q ↦ encode (algebraMap K E) (nf + 1) sh.R (foldTable w s.r)
        (s.pos q) := funext hcq
    refine ⟨⟨trivial, ?_⟩, ?_⟩
    · show powerBatch ![s.c, powerBatch s.cq s.lam] s.lam =
        WhirSum.claim (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam] s.lam).onCube
          s.ff 0 #v[]
      rw [claim_zero, Weight.pair_batch, hff, hc, hcqf]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact (pair_queryWeight _ _ _).symm
    · show batchMessage ![s.p1, s.p3] s.lam =
        WhirSum.roundPoly (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam]
          s.lam).onCube s.ff 0 #v[]
      rw [show (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam] s.lam).onCube =
        batchWeight (fun j ↦
          (![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam] j).onCube) s.lam from rfl,
        roundPoly_batch, hff]
      congr 1
      funext i
      fin_cases i
      · exact hp1
      · exact hp3

/-- Completeness of the first challenge of the tail. -/
def tailFirstComplete : Component.Complete (tailFirst sh nf)
    (SumcheckRound.relMid (tailFamily sh nf) 0) (SumcheckRound.rel (tailFamily sh nf) 1) :=
  SumcheckRound.drawChallengeComplete 0 _ (tailHonest sh nf) (by omega)

/-- Completeness of the remaining rounds of the tail. -/
def tailRestComplete : Component.Complete (tailRest sh nf)
    (SumcheckRound.rel (tailFamily sh nf) 1) (SumcheckRound.rel (tailFamily sh nf) (nf + 1)) :=
  SumcheckRound.roundsComplete (tailFamily sh nf) (nf + 1) (tailHonest sh nf) nf 1 (by omega)

/-- Completeness of the terminal check: the tail's claim after all its rounds is the product of
the weight's and the table's extensions at the point, `plainSum_self`. -/
def terminalComplete : Component.Complete (terminal sh nf)
    (SumcheckRound.rel (tailFamily sh nf) (nf + 1)) Set.univ :=
  Component.passCheckComplete _ _ _ fun s o w h ↦ by
    refine ⟨?_, trivial⟩
    have hcl : s.2.2 = evalMle s.1.1.onCube s.2.1 * evalMle s.1.2 s.2.1 := by
      rw [h.2, ← WhirSum.summand]
      exact plainSum_self (WhirSum.summand s.1.1.onCube s.1.2) s.2.1
    show decide (s.1.1.mle s.2.1 * evalMle s.1.2 s.2.1 = s.2.2) = true
    rw [decide_eq_true_eq, hcl, s.1.1.mle_eq]

/-! ## The level -/

/-- The steps of the final level: the first fold challenge, the other fold rounds, the residual
claim's polynomial, the plaintext table, the grinding nonce, the positions and the batching
challenge, the reading of the last word (no round), the query batch's polynomial, the glue (no
round), and the tail: its first challenge and the remaining rounds. The terminal check has no
round. -/
abbrev finalSteps : List Step :=
  [.chal E inferInstance, .rds E inferInstance 2 sh.lm1, .msg (SumcheckRound.Message E 2),
    .msg (Tab (nf + 1)), .msg E, .chal (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R))) inferInstance,
    .chal E inferInstance, .skip, .msg (SumcheckRound.Message E 2), .skip, .chal E inferInstance,
    .rds E inferInstance 2 nf]

/-- The final level of WHIR's opening: from the running claim with its first-round polynomial
received to the verifier's acceptance. -/
def finalDef : Component.Def (SumcheckRound.MidStmt (Weight E (sh.ℓ + (nf + 1))) E 0 2)
    (OneW sh (nf + 1)) (Tab (sh.ℓ + (nf + 1))) Unit (OneW sh (nf + 1)) Unit
    (seqSpec (finalSteps sh nf)) :=
  (foldFirst sh (nf + 1)).append <| (foldRest sh (nf + 1)).append <|
  (sendResidual sh (nf + 1)).append <| (sendTable sh nf).append <|
  (sendNonce _ sh (nf + 1)).append <| (drawPositions _ sh (nf + 1)).append <|
  (drawBatch _ sh (nf + 1)).append <| (readFinal sh nf).append <|
  (sendQueryPoly _ sh (nf + 1)).append <| (glueFinal sh nf).append <|
  (tailFirst sh nf).append <| (tailRest sh nf).append <| terminal sh nf

/-- Perfect completeness of the final level: from an honest running claim on a table and its
honest word, the verifier accepts. -/
def finalComplete : Component.Complete (finalDef sh nf) (startRel sh (nf + 1)) Set.univ :=
  (foldFirstComplete sh (nf + 1)).append <| (foldRestComplete sh (nf + 1)).append <|
  (sendResidualComplete sh (nf + 1) (Nat.succ_pos nf)).append <| (sendTableComplete sh nf).append <|
  (sendNonceComplete _ sh (nf + 1) (rel := relOld sh (nf + 1) Bd.G2)
    (rel' := relOld sh (nf + 1) Bd.G2) (fun _ _ _ _ h ↦ h)).append <|
  (drawPositionsComplete _ sh (nf + 1) (rel := relOld sh (nf + 1) Bd.G2)
    (rel' := relOld sh (nf + 1) Bd.G2) (fun _ _ _ _ h ↦ h)).append <|
  (drawBatchComplete _ sh (nf + 1) (rel := relOld sh (nf + 1) Bd.G2)
    (rel' := relOld sh (nf + 1) Bd.G2) (fun _ _ _ _ h ↦ h)).append <|
  (readFinalComplete sh nf).append <|
  (sendQueryPolyComplete _ sh (nf + 1) (Nat.succ_pos nf) (rel := relOld sh (nf + 1) Bd.G3)
    (rel' := relOld sh (nf + 1) Bd.G4) (fun _ _ _ h ↦ ⟨h.2.2, h.1, h.2, rfl⟩)).append <|
  (glueFinalComplete sh nf).append <| (tailFirstComplete sh nf).append <|
  (tailRestComplete sh nf).append <| terminalComplete sh nf

end Final

end Whir

end

end LeanerVM.Protocol
