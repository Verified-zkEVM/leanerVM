/-
  LeanerVM.Protocol.Compile.Whir

  WHIR's opening on the wire and in the compiled oracle protocol: on a transcript of the opening
  that the oracle verifier accepts, the executable verifier's WHIR algebra accepts the
  transcript's wire and the rows its words have at the transcript's positions.
-/

module

public import LeanerVM.Protocol.Compile.Rounds
public import LeanerVM.Protocol.Prove.Openings

/-!
# WHIR's opening on the wire

The oracle verifier of WHIR's opening (`Whir.whirOpen`, its levels `Whir.levelDef` and the final
level `Whir.finalDef`) is a guarded verifier: a check and a verdict on its statement, its oracles
and its transcript (`whirOpenGuarded`, from the steps' own guarded forms). Its oracles are the
committed words; it reads them only at the sampled positions (`Whir.readOld`, `Whir.readFinal`).
The executable verifier's algebra (`Verify.whirCheck`) reads the transcript's wire
(`DecodeChain.whirWireOf`) and the words' rows at the positions (`Prove.ladderRows`), each row as
the leaf image the opening carries.

* `replayFolds_foldsWire`: fold rounds the oracle verifier accepts replay on their wire, with the
  oracle verifier's final claim and challenges;
* `whirLevels_cons`, `whirLevels_final`: a level of the algebra, when its wire decodes;
* `levelGuarded_run`, `finalGuarded_run`: a level's guarded run that accepts, step by step, read
  off the transcript as the wire reads it (`seqHead`, `seqTail`);
* `whirLevels_levelWire`, `whirLevels_finalWire`, `whirLevels_ladder`: on a level's transcript
  the oracle verifier accepts, the algebra's level accepts the level's wire and rows and goes on
  from the glued claim the oracle verifier hands on, on the level's new word;
* **`whirCheck_of_run`**: on a transcript of the opening the oracle verifier accepts, from a claim
  on a word whose rows read as the leaves, the algebra accepts.

The direction is the completeness half: the algebra decodes every round polynomial against its
claim, so it never rejects a polynomial the oracle verifier accepts. The converse is not an
equation in the shape of the front phases' (`busStep_eq`): the algebra reads rows, the oracle
verifier whole words, and rows that disagree at a repeated position are no word's.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval ProtocolSpec StepSchedule Verify Whir
  DecodeChain

@[expose] public section

open RoundPoly (ofList?_toList)

namespace Compile

/-! ## Fold rounds on the wire -/

/-- A plain round polynomial's wire is not empty. -/
theorem polyWire_ne_nil (p : Vector E 3) : DecodeChain.polyWire 1 p ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [DecodeChain.polyWire] at this

/-- A plain round polynomial that passes its check against a claim decodes from its wire. -/
theorem decode_polyWire {claim : E} {p : Vector E 3} (h : Whir.chk p claim = true) :
    RoundPoly.decode 2 claim none (DecodeChain.polyWire 1 p) = some p := by
  rw [Whir.chk, decide_eq_true_iff, show unitDom = eqDomain none from rfl, ← check_iff] at h
  exact RoundPoly.decode_encode (by omega) h

/-- `k` draws carry `k` challenges. -/
private theorem length_drawsList : ∀ (k : ℕ) (t : (draws E k).FullTranscript),
    (drawsList k t).length = k
  | 0, _ => rfl
  | k + 1, t => by simp [drawsList, length_drawsList k]

/-- The challenges of `k` draws, as a vector. -/
def drawsVec (k : ℕ) (t : (draws E k).FullTranscript) : Vector E k :=
  ⟨(drawsList k t).toArray, by simp [length_drawsList]⟩

/-- The draws' challenges read as their vector. -/
theorem ofList?_drawsList (k : ℕ) (t : (draws E k).FullTranscript) :
    RoundPoly.ofList? k (drawsList k t) = some (drawsVec k t) := by
  rw [RoundPoly.ofList?, dite_eq_left_of_eq_true (eq_true (length_drawsList k t))]
  rfl

/-- The draws push their challenges onto the vector beside the statement. -/
theorem run_drawPushesFront_drawsVec {S W ι : Type} (O : ι → Type) [∀ i, OracleInterface (O i)]
    (k : ℕ) (s : S) (t : (draws E k).FullTranscript) :
    (Component.drawPushesFront (S := S) (W := W) O E k).run s t = some (s, drawsVec k t) := by
  obtain ⟨f, rfl⟩ := exists_eq_chalsTr k t
  rw [Component.run_drawPushesFront]
  refine congrArg (fun v ↦ some (s, v)) (Vector.toList_inj.mp ?_)
  rw [Vector.toList_ofFn, drawsVec, Vector.toList_mk, List.toList_toArray, drawsList_chalsTr]

section Folds

variable {X ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (P : SumcheckRound.Polys E X O W 2) (wt : SumcheckRound.Weights E X) (m : ℕ)

/-- **Fold rounds on the wire**: when, after the challenge `c` of the polynomial `q`, the oracle
verifier's `i` plain rounds accept with the verdict `s'`, the executable replays the wire of the
challenge, the rounds and a last wire `w` from `q`: the oracle verifier's final claim, the
challenges after the statement's, and the last wire decoded against that claim (`q'`, the last
round's polynomial, when `w` is empty). -/
theorem replayFolds_foldsWire (hwt : ∀ x k, wt x k = eqDomain none) (w : List E) :
    ∀ (i j : ℕ) (h : j + 1 + i = m) (s : SumcheckRound.Stmt X E j)
      (q : SumcheckRound.Message E 2) (c : E) (rt : (roundsSpec E 2 i).FullTranscript)
      (s' : SumcheckRound.Stmt X E m),
      (SumcheckRound.roundsFront P wt m i (j + 1) h).run
          (SumcheckRound.next j s (SumcheckRound.evaluate 2 q c) c) rt = some s' →
      s'.1 = s.1 ∧ ∃ cs, s'.2.1.toList = s.2.1.toList ++ cs ∧ ∃ q', ∀ claim,
        replayFolds claim q (foldsWire c (DecodeChain.roundsWire 1 i rt) w) =
          (if w = [] then some q' else RoundPoly.decode 2 s'.2.2 none w).map
            fun p ↦ (s'.2.2, p, cs)
  | 0, j, h, s, q, c, rt, s', hrun => by
    rw [SumcheckRound.run_roundsFront_zero, Option.some.injEq] at hrun
    subst hrun
    refine ⟨rfl, [c], by simp [SumcheckRound.next, Vector.toList_cast, Vector.toList_push], q,
      fun claim ↦ ?_⟩
    simp only [DecodeChain.roundsWire, foldsWire, replayFolds, SumcheckRound.next,
      ← eval_eq_evaluate]
    by_cases hw : w = []
    · subst hw
      rfl
    · simp only [hw, ↓reduceIte]
      cases RoundPoly.decode 2 (RoundPoly.eval q c) none w <;> rfl
  | i + 1, j, h, s, q, c, rt, s', hrun => by
    obtain ⟨q₁, c₁, rt', rfl⟩ : ∃ q₁ c₁ rt', rt = SumcheckRound.roundsCons q₁ c₁ rt' :=
      ⟨_, _, _, SumcheckRound.eq_roundsCons rt⟩
    rw [SumcheckRound.run_roundsFront_succ] at hrun
    split at hrun
    · rename_i hcheck
      obtain ⟨h₁, cs, hcs, q', hrep⟩ := replayFolds_foldsWire hwt w i (j + 1) (by omega)
        (SumcheckRound.next j s (SumcheckRound.evaluate 2 q c) c) q₁ c₁ rt' s' hrun
      refine ⟨h₁, c :: cs, ?_, q', fun claim ↦ ?_⟩
      · rw [hcs]
        simp [SumcheckRound.next, Vector.toList_push]
      · have hdec : RoundPoly.decode 2 (RoundPoly.eval q c) none (DecodeChain.polyWire 1 q₁) =
            some q₁ := by
          rw [SumcheckRound.check, decide_eq_true_iff, hwt, ← check_iff] at hcheck
          rw [eval_eq_evaluate]
          exact RoundPoly.decode_encode (by omega) hcheck
        have hw : DecodeChain.roundsWire 1 (i + 1) (SumcheckRound.roundsCons q₁ c₁ rt') =
            ⟨DecodeChain.polyWire 1 q₁, c₁⟩ :: DecodeChain.roundsWire 1 i rt' := by
          simp only [DecodeChain.roundsWire, DecodeChain.roundWire, SumcheckRound.roundsCons,
            SumcheckRound.roundTr, FullTranscript.append_fst, FullTranscript.append_snd,
            msgTr_zero, chalTr_zero]
        rw [hw]
        simp only [foldsWire, replayFolds, polyWire_ne_nil, ↓reduceIte, hdec, Option.bind_eq_bind,
          Option.bind_some, hrep (RoundPoly.eval q c)]
        cases (if w = [] then some q' else RoundPoly.decode 2 s'.2.2 none w) <;> rfl
    · nomatch hrun

end Folds

/-! ## A level of the algebra -/

/-- **A level with a successor in the algebra**: when its folds replay, its rows read and its
round polynomials decode, the algebra goes on from the glued claim on the next level. -/
theorem whirLevels_cons {first : Bool} {n : ℕ} {W : Weight E n} {claim : E} {quad : Vector E 3}
    {sh : LevelShape} {shs : List LevelShape} {l : WhirLevel} {ls : List WhirLevel}
    {rows : List (List K)} {rs : List (List (List K))} {claim' : E} {quad' p2 p3 : Vector E 3}
    {r : List E} {lanes : List (Vector E (2 ^ sh.fold))} {z : Vector E sh.msgLog}
    (hf : replayFolds claim quad l.folds = some (claim', quad', r))
    (hn : sh.fold + sh.msgLog = n) (hr : r.length = sh.fold) (hq : rows.length = sh.queries)
    (hl : rows.mapM (Verify.laneRow first sh.fold) = some lanes)
    (hp3 : RoundPoly.decode 2 (powerBatch (fun q : Fin sh.queries ↦
      Whir.foldRow ⟨r.toArray, by simpa using hr⟩ (lanes.getD q (Vector.replicate _ 0)))
        l.lam) none l.queryWire = some p3)
    (hfin : sh.final = false) (hz : RoundPoly.ofList? sh.msgLog l.ood = some z)
    (hp2 : RoundPoly.decode 2 l.oodValue none l.oodWire = some p2) :
    whirLevels first n W claim quad (sh :: shs) (l :: ls) (rows :: rs) =
      whirLevels false sh.msgLog
        (Whir.gluedWeight (Whir.foldWeight (castWeight hn.symm W) ⟨r.toArray, by simpa using hr⟩)
          z (positionsOf sh.queries (sh.msgLog + sh.rate) l.positions) l.lam)
        (powerBatch ![claim', l.oodValue, powerBatch (fun q : Fin sh.queries ↦
          Whir.foldRow ⟨r.toArray, by simpa using hr⟩ (lanes.getD q (Vector.replicate _ 0)))
            l.lam] l.lam)
        (Whir.batchMessage ![quad', p2, p3] l.lam) shs ls rs := by
  rw [whirLevels, hf]
  simp only [dite_eq_left_of_eq_true (eq_true (⟨hn, hr, hq⟩ : _ ∧ _ ∧ _)), hl, hp3, hfin, hz, hp2,
    Bool.false_eq_true, ↓reduceIte]

/-- **The last level in the algebra**: when its folds replay, its rows read, its query polynomial
decodes and its tail replays, the algebra's verdict is the terminal check. -/
theorem whirLevels_final {first : Bool} {n : ℕ} {W : Weight E n} {claim : E} {quad : Vector E 3}
    {sh : LevelShape} {shs : List LevelShape} {l : WhirLevel} {ls : List WhirLevel}
    {rows : List (List K)} {rs : List (List (List K))} {claim' : E} {quad' p3 : Vector E 3}
    {r : List E} {lanes : List (Vector E (2 ^ sh.fold))} {claimT : E} {quadT : Vector E 3}
    {tail : List E} {f : Vector E (2 ^ sh.msgLog)} {tv : Vector E sh.msgLog}
    (hf : replayFolds claim quad l.folds = some (claim', quad', r))
    (hn : sh.fold + sh.msgLog = n) (hr : r.length = sh.fold) (hq : rows.length = sh.queries)
    (hl : rows.mapM (Verify.laneRow first sh.fold) = some lanes)
    (hp3 : RoundPoly.decode 2 (powerBatch (fun q : Fin sh.queries ↦
      Whir.foldRow ⟨r.toArray, by simpa using hr⟩ (lanes.getD q (Vector.replicate _ 0)))
        l.lam) none l.queryWire = some p3)
    (hfin : sh.final = true)
    (ht : replayFolds (claim' + l.lam * powerBatch (fun q : Fin sh.queries ↦
      Whir.foldRow ⟨r.toArray, by simpa using hr⟩ (lanes.getD q (Vector.replicate _ 0))) l.lam)
        (Whir.batchMessage ![quad', p3] l.lam) l.tail = some (claimT, quadT, tail))
    (hres : RoundPoly.ofList? (2 ^ sh.msgLog) l.residual = some f)
    (htv : RoundPoly.ofList? sh.msgLog tail = some tv) :
    whirLevels first n W claim quad (sh :: shs) (l :: ls) (rows :: rs) =
      decide ((Weight.batch ![Whir.foldWeight (castWeight hn.symm W)
          ⟨r.toArray, by simpa using hr⟩,
        Whir.queryWeight sh.msgLog sh.rate (positionsOf sh.queries (sh.msgLog + sh.rate)
          l.positions) l.lam] l.lam).mle tv * evalMle f tv = claimT) := by
  rw [whirLevels, hf]
  simp only [dite_eq_left_of_eq_true (eq_true (⟨hn, hr, hq⟩ : _ ∧ _ ∧ _)), hl, hp3, hfin, ht, hres,
    htv, ↓reduceIte]

/-- **The algebra's opening**: when the shapes start with `sh` and the first polynomial decodes,
the algebra is its levels from the relaid opening claim, read on `sh.fold + k` variables for any
`k` the shape leaves. -/
theorem whirCheck_eq {μ : ℕ} {shs : List LevelShape} {W : Weight E μ} {target : E}
    {first : List E} {ls : List WhirLevel} {rows : List (List (List K))} {sh : LevelShape}
    {shs' : List LevelShape} {quad : Vector E 3} {k : ℕ} (hshs : shs = sh :: shs')
    (hq : RoundPoly.decode 2 target none first = some quad) (hk : μ - sh.fold = k)
    (hk' : k + sh.fold = μ) :
    whirCheck μ shs W target first ls rows =
      whirLevels true (sh.fold + k) (relayoutWeight (castWeight hk'.symm W)) target quad shs ls
        rows := by
  subst hshs hk
  simp only [whirCheck, hq]
  exact dite_eq_left_of_eq_true (eq_true hk')

/-! ## The opening's guarded forms -/

section Guarded

open Component

variable (sh sh' : Whir.Shape) (κ' : ℕ) {ι₃ : Type} {O₃ : ι₃ → Type}
  [∀ i, OracleInterface (O₃ i)] {S₃ W₃ : Type} {k : List Step}

/-- A level's guarded form, from its steps' and the rest's. -/
def levelGuarded
    {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)} (GR : Guarded R) :
    Guarded (levelDef sh sh' κ' R) :=
  (Front.toGuarded (sampleFront _ _ _ _) : Guarded (foldFirst sh (Kap sh' κ'))).append <|
  (Front.toGuarded (SumcheckRound.roundsFront _ _ _ _ _ _) :
    Guarded (foldRest sh (Kap sh' κ'))).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendResidual sh (Kap sh' κ'))).append <|
  (Guarded.ofPure (sendBesideVerifierPure _ _ _) : Guarded (commitNext sh sh' κ')).append <|
  (Front.toGuarded (drawPushesFront _ _ _) : Guarded (drawPoint sh sh' κ')).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendOod sh sh' κ')).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendOodPoly sh sh' κ')).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) :
    Guarded (sendNonce (besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh
      (Kap sh' κ'))).append <|
  (Front.toGuarded (sampleFront _ _ _ _) :
    Guarded (drawPositions (besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh
      (Kap sh' κ'))).append <|
  (Front.toGuarded (sampleFront _ _ _ _) :
    Guarded (drawBatch (besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')) sh
      (Kap sh' κ'))).append <|
  (⟨queryRecordGuarded _ _ _ _ _⟩ : Guarded (readOld sh sh' κ')).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) :
    Guarded (sendQueryPoly (keptOracles (besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ'))
      keepNew) sh (Kap sh' κ'))).append <|
  (Guarded.ofPure (passThroughPure _ _) : Guarded (glue sh sh' κ')).append GR

/-- The final level's guarded form, from its steps'. -/
def finalGuarded (nf : ℕ) : Guarded (finalDef sh nf) :=
  (Front.toGuarded (sampleFront _ _ _ _) : Guarded (foldFirst sh (nf + 1))).append <|
  (Front.toGuarded (SumcheckRound.roundsFront _ _ _ _ _ _) :
    Guarded (foldRest sh (nf + 1))).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendResidual sh (nf + 1))).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendTable sh nf)).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (finalNonce sh nf)).append <|
  (Front.toGuarded (sampleFront _ _ _ _) : Guarded (Whir.finalPositions sh nf)).append <|
  (Front.toGuarded (sampleFront _ _ _ _) : Guarded (finalBatch sh nf)).append <|
  (⟨queryRecordGuarded _ _ _ _ _⟩ : Guarded (readFinal sh nf)).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (finalQueryPoly sh nf)).append <|
  (Guarded.ofPure (passThroughPure _ _) : Guarded (glueFinal sh nf)).append <|
  (Front.toGuarded (sampleFront _ _ _ _) : Guarded (tailFirst sh nf)).append <|
  (Front.toGuarded (SumcheckRound.roundsFront _ _ _ _ _ _) : Guarded (tailRest sh nf)).append
  (⟨passCheckGuarded _ _ _⟩ : Guarded (terminal sh nf))

/-- A chain of levels' guarded form. -/
def ladderGuarded : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → Guarded L.comp
  | _, _, .last sh nf => finalGuarded sh nf
  | _, _, @Ladder.cons sh sh' κ' L => levelGuarded sh sh' κ' (ladderGuarded L)

/-- The opening's guarded form. -/
def whirOpenGuarded (κ : ℕ) (L : Ladder sh κ) : Guarded (whirOpen sh κ L) :=
  (Guarded.ofPure (passThroughPure _ _) : Guarded (stackRelayout sh κ)).append <|
  (Front.toGuarded (sendCheckedFront _ _ _ _ _) : Guarded (sendFirst sh κ)).append
    (ladderGuarded L)

end Guarded

/-! ## A level on the wire -/

/-- Values that each read as some value read as the list of those values. -/
private theorem mapM_eq_some {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_eq_some fun b hb ↦ h b (List.mem_cons_of_mem a hb)]
    rfl

/-- A word's rows at positions, read through leaves that carry them. -/
theorem mapM_laneRow {first : Bool} {ℓ b t : ℕ} {leaf : Fin (2 ^ b) → List K} {x : Word ℓ b t}
    (hleaf : ∀ p, Verify.laneRow first ℓ (leaf p) = some (x.row p)) (pos : Fin t → Fin (2 ^ b)) :
    (List.ofFn fun q ↦ leaf (pos q)).mapM (Verify.laneRow first ℓ) =
      some (List.ofFn fun q ↦ x.row (pos q)) := by
  rw [mapM_eq_some (g := fun l ↦ (Verify.laneRow first ℓ l).getD (Vector.replicate _ 0)),
    List.map_ofFn]
  · simp only [Function.comp_def, hleaf, Option.getD_some]
  · intro a ha
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp ha
    rw [hleaf, Option.getD_some]

/-- The rows read at the positions, folded at the fold point, are the oracle verifier's folded
symbols. -/
theorem foldRow_getD {ℓ b t : ℕ} (r : Vector E ℓ) (x : Word ℓ b t) (pos : Fin t → Fin (2 ^ b))
    (q : Fin t) :
    Whir.foldRow r ((List.ofFn fun q ↦ x.row (pos q)).getD q (Vector.replicate _ 0)) =
      (Whir.foldRows r fun k ↦ x.row (pos k))[q] := by
  rw [Whir.foldRows_getElem]
  congr 1
  simp [List.getD_eq_getElem?_getD]

/-- A vector read off its list. -/
private theorem mk_toArray_toList {n : ℕ} (v : Vector E n) (h : v.toList.toArray.size = n) :
    (⟨v.toList.toArray, h⟩ : Vector E n) = v := by
  rcases v with ⟨a, rfl⟩
  simp

/-- The algebra's folded symbols, from the rows read off a word at positions and the fold point
read off its list, are the oracle verifier's. -/
theorem foldRow_mk_getD {ℓ b t : ℕ} (r : Vector E ℓ) (x : Word ℓ b t) (pos : Fin t → Fin (2 ^ b))
    (h : r.toList.toArray.size = ℓ) :
    (fun q : Fin t ↦ Whir.foldRow ⟨r.toList.toArray, h⟩
      ((List.ofFn fun q ↦ x.row (pos q)).getD q (Vector.replicate _ 0))) =
      fun q ↦ (Whir.foldRows r fun k ↦ x.row (pos k))[q] := by
  funext q
  rw [mk_toArray_toList, foldRow_getD]

variable {sh sh' : Whir.Shape} {κ' : ℕ} {ι₃ : Type} {O₃ : ι₃ → Type}
  [∀ i, OracleInterface (O₃ i)] {S₃ W₃ : Type} {k : List Step}

-- The conversion of the run's transcript projections to the wire's (`seqHead`, `seqTail`) is
-- definitional but slow: their schedules are spelled as the components' and as `seqSpec`.
set_option maxHeartbeats 600000 in
open Component in
/-- **A level's guarded run, step by step**: on a level's transcript its guarded verifier accepts,
from a running claim on the word `x`, the fold rounds accept, the residual claim's, the
out-of-domain claim's and the query batch's polynomials pass their checks, and the rest runs from
the glued claim on the level's new word. -/
theorem levelGuarded_run
    {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)} (GR : Guarded R)
    (W : Weight E (sh.ℓ + Kap sh' κ')) (claim : E) (quad : SumcheckRound.Message E 2)
    (x : WordOf sh (Kap sh' κ')) (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript)
    {so : S₃ × ∀ i, O₃ i}
    (h : (levelGuarded sh sh' κ' GR).run (((W, (#v[], claim)), quad), fun _ ↦ x) t = some so) :
    ∃ s₂ : SumcheckRound.Stmt (Weight E (sh.ℓ + Kap sh' κ')) E sh.ℓ,
      (SumcheckRound.roundsFront (levelFamily sh (Kap sh' κ')).poly
          (levelFamily sh (Kap sh' κ')).weight sh.ℓ sh.lm1 (0 + 1)
          (by simp only [Whir.Shape.ℓ]; omega)).run
        (SumcheckRound.next 0 (W, (#v[], claim))
          (SumcheckRound.evaluate 2 quad (drawOf (seqHead t))) (drawOf (seqHead t)))
        (seqHead (seqTail t)) = some s₂ ∧
      Whir.chk (msgOf (seqHead (seqTail (seqTail t)))) s₂.2.2 = true ∧
      Whir.chk (msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail t))))))))
        (levelWire t).1.oodValue = true ∧
      Whir.chk (msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail (seqTail t)))))))))))))
        (powerBatch (fun q : Fin sh.t ↦
            (Whir.foldRows (t := sh.t) s₂.2.1 fun k ↦ x.row (Prove.levelPositions t k))[q])
          (levelWire t).1.lam) = true ∧
      GR.run (((Whir.gluedWeight (Whir.foldWeight s₂.1 s₂.2.1)
          (drawsVec _ (seqHead (seqTail (seqTail (seqTail (seqTail t))))))
          (Prove.levelPositions t) (levelWire t).1.lam,
        (#v[], powerBatch ![s₂.2.2, (levelWire t).1.oodValue,
          powerBatch (fun q : Fin sh.t ↦
              (Whir.foldRows (t := sh.t) s₂.2.1 fun k ↦ x.row (Prove.levelPositions t k))[q])
            (levelWire t).1.lam] (levelWire t).1.lam)),
        Whir.batchMessage ![msgOf (seqHead (seqTail (seqTail t))),
          msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail t))))))),
          msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
            (seqTail (seqTail (seqTail t))))))))))))] (levelWire t).1.lam),
        fun _ ↦ Prove.levelWord t) (levelWire t).2 = some so := by
  -- the first fold challenge
  obtain ⟨x₁, a₁, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁, b₁, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁
  obtain ⟨-, e₁⟩ := (Front.run_eq_some_iff _).mp b₁
  dsimp only [sampleFront] at e₁
  subst e₁
  -- the other fold rounds
  obtain ⟨x₂, a₂, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₂, b₂, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₂
  -- the residual claim's polynomial
  obtain ⟨x₃, a₃, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₃, b₃, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₃
  obtain ⟨hp1, e₃⟩ := (Front.run_eq_some_iff _).mp b₃
  dsimp only [sendCheckedFront, Bd.start] at hp1 e₃
  subst e₃
  -- the next word
  obtain ⟨x₄, a₄, h⟩ := Guarded.run_append_eq_some h
  have e₄ := Guarded.run_ofPure_eq_some a₄
  dsimp only [sendBesideVerifierPure] at e₄
  subst e₄
  -- the out-of-domain point
  obtain ⟨x₅, a₅, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₅, b₅, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₅
  obtain rfl := Option.some.inj ((run_drawPushesFront_drawsVec _ _ _ _).symm.trans b₅)
  -- the out-of-domain answer
  obtain ⟨x₆, a₆, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₆, b₆, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₆
  obtain ⟨-, e₆⟩ := (Front.run_eq_some_iff _).mp b₆
  dsimp only [sendCheckedFront] at e₆
  subst e₆
  -- its polynomial
  obtain ⟨x₇, a₇, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₇, b₇, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₇
  obtain ⟨hp2, e₇⟩ := (Front.run_eq_some_iff _).mp b₇
  dsimp only [sendCheckedFront] at hp2 e₇
  subst e₇
  -- the nonce
  obtain ⟨x₈, a₈, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₈, b₈, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₈
  obtain ⟨-, e₈⟩ := (Front.run_eq_some_iff _).mp b₈
  dsimp only [sendCheckedFront] at e₈
  subst e₈
  -- the positions and the batching challenge
  obtain ⟨x₉, a₉, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₉, b₉, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₉
  obtain ⟨-, e₉⟩ := (Front.run_eq_some_iff _).mp b₉
  dsimp only [sampleFront] at e₉
  subst e₉
  obtain ⟨x₁₀, a₁₀, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁₀, b₁₀, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁₀
  obtain ⟨-, e₁₀⟩ := (Front.run_eq_some_iff _).mp b₁₀
  dsimp only [sampleFront] at e₁₀
  subst e₁₀
  -- the reading of the old word
  obtain ⟨x₁₁, a₁₁, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨-, e₁₁⟩ := (Guarded.run_eq_some_iff _).mp a₁₁
  dsimp only [queryRecordGuarded, readOut] at e₁₁
  subst e₁₁
  -- the query batch's polynomial
  obtain ⟨x₁₂, a₁₂, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁₂, b₁₂, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁₂
  obtain ⟨hp3, e₁₂⟩ := (Front.run_eq_some_iff _).mp b₁₂
  dsimp only [sendCheckedFront] at hp3 e₁₂
  subst e₁₂
  -- the glue
  obtain ⟨x₁₃, a₁₃, h⟩ := Guarded.run_append_eq_some h
  have e₁₃ := Guarded.run_ofPure_eq_some a₁₃
  dsimp only [passThroughPure] at e₁₃
  subst e₁₃
  exact ⟨s₂, b₂, hp1, hp2, hp3, h⟩

/-- **A level on the wire**: on a level's transcript its guarded verifier accepts, from a running
claim on a word whose rows read as the leaves, the algebra's level accepts the level's wire and
rows and goes on from the glued claim the verifier hands on, on the level's new word. -/
theorem whirLevels_levelWire
    {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)} (GR : Component.Guarded R) (first : Bool)
    (W : Weight E (sh.ℓ + Kap sh' κ')) (claim : E) (quad : SumcheckRound.Message E 2)
    (x : WordOf sh (Kap sh' κ')) (leaf : Fin (2 ^ (Kap sh' κ' + sh.R)) → List K)
    (hleaf : ∀ p, Verify.laneRow first sh.ℓ (leaf p) = some (x.row p))
    (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript) {so : S₃ × ∀ i, O₃ i}
    (h : (levelGuarded sh sh' κ' GR).run (((W, (#v[], claim)), quad), fun _ ↦ x) t = some so)
    (shs : List LevelShape) (ls : List WhirLevel) (rs : List (List (List K))) :
    ∃ W' claim' quad', GR.run (((W', (#v[], claim')), quad'), fun _ ↦ Prove.levelWord t)
        (levelWire t).2 = some so ∧
      whirLevels first (sh.ℓ + Kap sh' κ') W claim quad
          (⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ :: shs) ((levelWire t).1 :: ls)
          ((List.ofFn fun q ↦ leaf (Prove.levelPositions t q)) :: rs) =
        whirLevels false (Kap sh' κ') W' claim' quad' shs ls rs := by
  obtain ⟨s₂, hrounds, hp1, hp2, hp3, hGR⟩ := levelGuarded_run GR W claim quad x t h
  refine ⟨_, _, _, hGR, ?_⟩
  obtain ⟨hW, cs, hcs, q', hrep⟩ := replayFolds_foldsWire (levelFamily sh (Kap sh' κ')).poly
    (levelFamily sh (Kap sh' κ')).weight sh.ℓ (fun _ _ ↦ rfl)
    (DecodeChain.polyWire 1 (msgOf (seqHead (seqTail (seqTail t))))) sh.lm1 0 _ _ _ _ _ s₂ hrounds
  obtain rfl : cs = s₂.2.1.toList := by simpa using hcs.symm
  have hf : replayFolds claim quad (levelWire t).1.folds =
      some (s₂.2.2, msgOf (seqHead (seqTail (seqTail t))), s₂.2.1.toList) := by
    refine (hrep claim).trans ?_
    simp only [polyWire_ne_nil, ↓reduceIte, decode_polyWire hp1, Option.map_some]
  have hcq := foldRow_mk_getD s₂.2.1 x (Prove.levelPositions t) (by simp)
  refine (whirLevels_cons (sh := ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩) hf rfl (by simp)
    (by simp) (mapM_laneRow hleaf (Prove.levelPositions t))
    (by rw [hcq]; exact decode_polyWire hp3) rfl (ofList?_drawsList _ _)
    (decode_polyWire hp2)).trans ?_
  dsimp only
  rw [show positionsOf sh.t (Kap sh' κ' + sh.R) (levelWire t).1.positions =
      Prove.levelPositions t from Prove.positionsOf_positionsList _, hcq, mk_toArray_toList,
    ← show s₂.1 = W from hW]
  rfl

/-- A later level's word, stored three limbs a lane, reads back as its lanes. -/
private theorem ofLimbs_flatMap : ∀ (l : List E) (i : ℕ), i < l.length →
    E.ofLimbs ((l.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2]).getD (3 * i) 0)
      ((l.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2]).getD (3 * i + 1) 0)
      ((l.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2]).getD (3 * i + 2) 0) = l.getD i 0
  | [], i, h => absurd h (by simp)
  | a :: l, 0, _ => by simp [ofLimbs_limb]
  | a :: l, i + 1, h => by
    have ih := ofLimbs_flatMap l i (by simpa using h)
    have e₁ : 3 * (i + 1) + 1 = 3 * i + 1 + 3 := by ring
    have e₂ : 3 * (i + 1) + 2 = 3 * i + 2 + 3 := by ring
    have e₀ : 3 * (i + 1) = 3 * i + 3 := by ring
    rw [e₁, e₂, e₀, List.flatMap_cons]
    simpa only [List.cons_append, List.nil_append, List.getD_cons_succ] using ih

/-- **A later level's leaf reads back as the word's row**: the leaf image of a row stored three
limbs a lane is the row. -/
theorem laneRow_laterRows {ℓ b t : ℕ} (x : Word ℓ b t) (p : Fin (2 ^ b)) :
    Verify.laneRow false ℓ (leafImage (3 * 2 ^ ℓ) (Prove.laterRows x)[p]) = some (x.row p) := by
  have hrow : (Prove.laterRows x)[p] =
      (x.row p).toList.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2] := by
    simp [Prove.laterRows]
  have hlen : ((x.row p).toList.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2]).length =
      3 * 2 ^ ℓ := by
    simp [List.length_flatMap, Nat.mul_comm]
  rw [hrow, leafImage, hlen, Nat.sub_self, List.replicate_zero, List.nil_append]
  simp only [Verify.laneRow, Bool.false_eq_true, ↓reduceIte]
  rw [← ofList?_toList (x.row p)]
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [ofLimbs_flatMap _ i (by simpa using h₂)]
  exact List.getD_eq_getElem _ _ h₂

open Component in
/-- **The final level's guarded run, step by step**: on the final level's transcript its guarded
verifier accepts, from a running claim on the word `x`, the fold rounds accept, the residual
claim's and the query batch's polynomials pass their checks, the tail's rounds accept from the
glued claim, and the terminal check passes. -/
theorem finalGuarded_run {sh : Whir.Shape} {nf : ℕ} (W : Weight E (sh.ℓ + (nf + 1))) (claim : E)
    (quad : SumcheckRound.Message E 2) (x : WordOf sh (nf + 1))
    (t : (seqSpec (finalSteps sh nf)).FullTranscript) {so : Unit × ∀ i, OneW sh (nf + 1) i}
    (h : (finalGuarded sh nf).run (((W, (#v[], claim)), quad), fun _ ↦ x) t = some so) :
    ∃ (s₂ : SumcheckRound.Stmt (Weight E (sh.ℓ + (nf + 1))) E sh.ℓ)
      (s₁₂ : SumcheckRound.Stmt (TX (nf + 1)) E (nf + 1)),
      (SumcheckRound.roundsFront (levelFamily sh (nf + 1)).poly
          (levelFamily sh (nf + 1)).weight sh.ℓ sh.lm1 (0 + 1)
          (by simp only [Whir.Shape.ℓ]; omega)).run
        (SumcheckRound.next 0 (W, (#v[], claim))
          (SumcheckRound.evaluate 2 quad (drawOf (seqHead t))) (drawOf (seqHead t)))
        (seqHead (seqTail t)) = some s₂ ∧
      Whir.chk (msgOf (seqHead (seqTail (seqTail t)))) s₂.2.2 = true ∧
      Whir.chk (msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail t))))))))))
        (powerBatch (fun q : Fin sh.t ↦
            (Whir.foldRows (t := sh.t) s₂.2.1 fun k ↦ x.row (Prove.finalPositions t k))[q])
          (finalWire t).lam) = true ∧
      (SumcheckRound.roundsFront (tailFamily sh nf).poly (tailFamily sh nf).weight (nf + 1) nf
          (0 + 1) (by omega)).run
        (SumcheckRound.next 0
          ((Weight.batch ![Whir.foldWeight s₂.1 s₂.2.1,
              queryWeight (nf + 1) sh.R (Prove.finalPositions t) (finalWire t).lam]
              (finalWire t).lam,
            msgOf (seqHead (seqTail (seqTail (seqTail t))))),
            (#v[], powerBatch ![s₂.2.2, powerBatch (fun q : Fin sh.t ↦
              (Whir.foldRows (t := sh.t) s₂.2.1 fun k ↦ x.row (Prove.finalPositions t k))[q])
              (finalWire t).lam] (finalWire t).lam))
          (SumcheckRound.evaluate 2 (Whir.batchMessage ![msgOf (seqHead (seqTail (seqTail t))),
              msgOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
                (seqTail t)))))))))] (finalWire t).lam)
            (drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
              (seqTail (seqTail (seqTail t)))))))))))))
          (drawOf (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
            (seqTail (seqTail (seqTail t)))))))))))))
        (seqHead (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail t)))))))))))) = some s₁₂ ∧
      decide (s₁₂.1.1.mle s₁₂.2.1 * evalMle s₁₂.1.2 s₁₂.2.1 = s₁₂.2.2) = true := by
  -- the first fold challenge
  obtain ⟨x₁, a₁, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁, b₁, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁
  obtain ⟨-, e₁⟩ := (Front.run_eq_some_iff _).mp b₁
  dsimp only [sampleFront] at e₁
  subst e₁
  -- the other fold rounds
  obtain ⟨x₂, a₂, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₂, b₂, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₂
  -- the residual claim's polynomial
  obtain ⟨x₃, a₃, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₃, b₃, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₃
  obtain ⟨hp1, e₃⟩ := (Front.run_eq_some_iff _).mp b₃
  dsimp only [sendCheckedFront, Bd.start] at hp1 e₃
  subst e₃
  -- the table and the nonce
  obtain ⟨x₄, a₄, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₄, b₄, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₄
  obtain ⟨-, e₄⟩ := (Front.run_eq_some_iff _).mp b₄
  dsimp only [sendCheckedFront] at e₄
  subst e₄
  obtain ⟨x₅, a₅, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₅, b₅, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₅
  obtain ⟨-, e₅⟩ := (Front.run_eq_some_iff _).mp b₅
  dsimp only [sendCheckedFront] at e₅
  subst e₅
  -- the positions and the batching challenge
  obtain ⟨x₆, a₆, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₆, b₆, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₆
  obtain ⟨-, e₆⟩ := (Front.run_eq_some_iff _).mp b₆
  dsimp only [sampleFront] at e₆
  subst e₆
  obtain ⟨x₇, a₇, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₇, b₇, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₇
  obtain ⟨-, e₇⟩ := (Front.run_eq_some_iff _).mp b₇
  dsimp only [sampleFront] at e₇
  subst e₇
  -- the reading of the last word
  obtain ⟨x₈, a₈, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨-, e₈⟩ := (Guarded.run_eq_some_iff _).mp a₈
  dsimp only [queryRecordGuarded, readFinalOut] at e₈
  subst e₈
  -- the query batch's polynomial
  obtain ⟨x₉, a₉, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₉, b₉, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₉
  obtain ⟨hp3, e₉⟩ := (Front.run_eq_some_iff _).mp b₉
  dsimp only [sendCheckedFront] at hp3 e₉
  subst e₉
  -- the glue
  obtain ⟨x₁₀, a₁₀, h⟩ := Guarded.run_append_eq_some h
  have e₁₀ := Guarded.run_ofPure_eq_some a₁₀
  dsimp only [passThroughPure] at e₁₀
  subst e₁₀
  -- the tail's first challenge
  obtain ⟨x₁₁, a₁₁, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁₁, b₁₁, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁₁
  obtain ⟨-, e₁₁⟩ := (Front.run_eq_some_iff _).mp b₁₁
  dsimp only [sampleFront] at e₁₁
  subst e₁₁
  -- the tail's other rounds, and the terminal check
  obtain ⟨x₁₂, a₁₂, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₁₂, b₁₂, rfl⟩ := Guarded.run_toGuarded_eq_some _ a₁₂
  obtain ⟨hterm, -⟩ := (Guarded.run_eq_some_iff _).mp h
  exact ⟨s₂, s₁₂, b₂, hp1, hp3, b₁₂, hterm⟩

/-- **The final level on the wire**: on the final level's transcript its guarded verifier accepts,
from a running claim on a word whose rows read as the leaves, the algebra accepts the level's wire
and rows. -/
theorem whirLevels_finalWire {sh : Whir.Shape} {nf : ℕ} (first : Bool)
    (W : Weight E (sh.ℓ + (nf + 1))) (claim : E) (quad : SumcheckRound.Message E 2)
    (x : WordOf sh (nf + 1)) (leaf : Fin (2 ^ (nf + 1 + sh.R)) → List K)
    (hleaf : ∀ p, Verify.laneRow first sh.ℓ (leaf p) = some (x.row p))
    (t : (seqSpec (finalSteps sh nf)).FullTranscript) {so : Unit × ∀ i, OneW sh (nf + 1) i}
    (h : (finalGuarded sh nf).run (((W, (#v[], claim)), quad), fun _ ↦ x) t = some so)
    (shs : List LevelShape) (ls : List WhirLevel) (rs : List (List (List K))) :
    whirLevels first (sh.ℓ + (nf + 1)) W claim quad (⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩ :: shs)
      (finalWire t :: ls) ((List.ofFn fun q ↦ leaf (Prove.finalPositions t q)) :: rs) = true := by
  obtain ⟨s₂, s₁₂, hrounds, hp1, hp3, htail, hterm⟩ := finalGuarded_run W claim quad x t h
  obtain ⟨hW, cs, hcs, q', hrep⟩ := replayFolds_foldsWire (levelFamily sh (nf + 1)).poly
    (levelFamily sh (nf + 1)).weight sh.ℓ (fun _ _ ↦ rfl)
    (DecodeChain.polyWire 1 (msgOf (seqHead (seqTail (seqTail t))))) sh.lm1 0 _ _ _ _ _ s₂ hrounds
  obtain rfl : cs = s₂.2.1.toList := by simpa using hcs.symm
  have hf : replayFolds claim quad (finalWire t).folds =
      some (s₂.2.2, msgOf (seqHead (seqTail (seqTail t))), s₂.2.1.toList) := by
    refine (hrep claim).trans ?_
    simp only [polyWire_ne_nil, ↓reduceIte, decode_polyWire hp1, Option.map_some]
  obtain ⟨hWT, csT, hcsT, qT, hrepT⟩ := replayFolds_foldsWire (tailFamily sh nf).poly
    (tailFamily sh nf).weight (nf + 1) (fun _ _ ↦ rfl) [] nf 0 _ _ _ _ _ s₁₂ htail
  obtain rfl : csT = s₁₂.2.1.toList := by simpa using hcsT.symm
  have hcq := foldRow_mk_getD s₂.2.1 x (Prove.finalPositions t) (by simp)
  refine (whirLevels_final (sh := ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩) hf rfl (by simp) (by simp)
    (mapM_laneRow hleaf (Prove.finalPositions t)) (by rw [hcq]; exact decode_polyWire hp3) rfl
    ((hrepT _).trans rfl) (ofList?_toList _) (ofList?_toList s₁₂.2.1)).trans ?_
  dsimp only
  rw [show positionsOf sh.t (nf + 1 + sh.R) (finalWire t).positions = Prove.finalPositions t from
    Prove.positionsOf_positionsList _, mk_toArray_toList, ← show s₂.1 = W from hW]
  refine Eq.trans ?_ hterm
  rw [hWT]
  rfl

/-- **A chain of levels on the wire**: on the chain's transcript its guarded verifier accepts,
from a running claim on a word whose rows read as the leaves, the algebra accepts the chain's
wire and rows. -/
theorem whirLevels_ladder : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (first : Bool)
    (W : Weight E (sh.ℓ + κ)) (claim : E) (quad : SumcheckRound.Message E 2) (x : WordOf sh κ)
    (leaf : Fin (2 ^ (κ + sh.R)) → List K),
    (∀ p, Verify.laneRow first sh.ℓ (leaf p) = some (x.row p)) →
    ∀ (t : (seqSpec L.steps).FullTranscript) {so : Unit × ∀ i, OneW L.finShape L.finN i},
    (ladderGuarded L).run (((W, (#v[], claim)), quad), fun _ ↦ x) t = some so →
    whirLevels first (sh.ℓ + κ) W claim quad L.shapes (ladderWire L t) (Prove.ladderRows L leaf t) =
      true
  | _, _, .last sh nf, first, W, claim, quad, x, leaf, hleaf, t, _, h =>
    whirLevels_finalWire first W claim quad x leaf hleaf t h [] [] []
  | _, _, @Ladder.cons sh sh' κ' L, first, W, claim, quad, x, leaf, hleaf, t, _, h => by
    obtain ⟨W', claim', quad', h', heq⟩ := whirLevels_levelWire (ladderGuarded L) first W claim
      quad x leaf hleaf t h L.shapes (ladderWire L (levelWire t).2)
      (Prove.ladderRows L
        (fun p ↦ leafImage (3 * 2 ^ sh'.ℓ) (Prove.laterRows (Prove.levelWord t))[p])
        (levelWire t).2)
    exact heq.trans (whirLevels_ladder L false W' claim' quad' (Prove.levelWord t) _
      (laneRow_laterRows _) _ h')

open Component in
/-- **WHIR's opening on the wire**: on a transcript of the opening its guarded verifier accepts,
from the claim `⟨W, f⟩ = c` on a word whose rows read as the leaves, the executable's WHIR algebra
accepts the transcript's wire and the rows the leaves carry at the transcript's positions. -/
theorem whirCheck_of_run {sh : Whir.Shape} {κ μ : ℕ} (L : Ladder sh κ) (hμ : κ + sh.ℓ = μ)
    (W : Weight E μ) (c : E) (x : WordOf sh κ) (leaf : Fin (2 ^ (κ + sh.R)) → List K)
    (hleaf : ∀ p, Verify.laneRow true sh.ℓ (leaf p) = some (x.row p))
    (t : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript)
    {so : Unit × ∀ i, OneW L.finShape L.finN i}
    (h : (whirOpenGuarded sh κ L).run ((castWeight hμ.symm W, c), fun _ ↦ x) t = some so) :
    whirCheck μ L.shapes W c (whirWireOf L t).1 (whirWireOf L t).2
      (Prove.ladderRows L leaf (seqTail (seqTail t))) = true := by
  -- the relayout
  obtain ⟨x₁, h₁, h⟩ := Guarded.run_append_eq_some h
  obtain rfl := Guarded.run_ofPure_eq_some h₁
  -- the first round polynomial
  obtain ⟨x₂, h₂, h⟩ := Guarded.run_append_eq_some h
  obtain ⟨s₂, h₂', rfl⟩ := Guarded.run_toGuarded_eq_some _ h₂
  obtain ⟨hfirst, rfl⟩ := (Front.run_eq_some_iff _).mp h₂'
  obtain ⟨b, shs, hsh⟩ : ∃ b shs, L.shapes = ⟨sh.ℓ, κ, sh.R, sh.t, b⟩ :: shs := by
    cases L <;> exact ⟨_, _, rfl⟩
  refine (whirCheck_eq hsh (decode_polyWire hfirst) (by subst hμ; simp) hμ).trans ?_
  exact whirLevels_ladder L true _ c _ x leaf hleaf _ h

end Compile

end
end LeanerVM.Protocol
