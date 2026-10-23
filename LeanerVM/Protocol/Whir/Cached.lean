/-
  LeanerVM.Protocol.Whir.Cached

  WHIR's opening with a cached honest prover: the fold rounds' tables bound once per challenge,
  each level's folded table computed once and carried to its messages and its glue, the next
  level's word encoded once by the additive transform; proved to run as the honest prover.
-/

module

public import LeanerVM.Protocol.Whir.Open
public import LeanerVM.Protocol.Whir.Transform
public import LeanerVM.Protocol.ToArkLib.CachedSteps
public import LeanerVM.Protocol.ToArkLib.ProductSumCached

/-!
# The opening of WHIR, cached

The honest prover of `whirOpen` computes every message from the statement and the table: each
fold round binds the weight's and the table's cubes to all the challenges so far, every message
after the folds folds the table again (`foldTable`), and the committed word of the next level is
`wordOf`, whose rows encode the lanes on demand, `2 ^ κ` products a symbol, at every query.
`whirOpenCached` is a cached prover of it (`Component.Cached`):

* the fold rounds' two tables bound one challenge at a time (`foldCache`, by
  `ProductSum.roundCache`); after the folds the table bound on the lane coordinates is the folded
  table (`cast_lowCache_eq_foldTable`), carried to the level's messages and its glue;
* the next level's word is the folded table's lanes encoded by the additive transform, its rows
  stored (`wordFast`, equal to `wordOf` on `κ + R ≤ 64` positions' bits, `wordFast_eq`);
* the final level's tail, its glued weight's and the plaintext table's cubes bound one challenge
  at a time (`tailCache`).

Every message read off the cache is the honest one, so the cached prover runs as `whirOpen`'s
honest prover (`Component.Cached.run_eq`). The input word is the caller's: with its rows stored,
the first level's queries read them.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
  StepSchedule

@[expose] public section

namespace Whir

/-! ## The word, encoded once -/

/-- The honest word of a table with its rows stored: the lanes encoded by the additive transform
when the positions have at most 64 bits, `wordOf` otherwise. -/
def wordFast (ℓ κ R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ)) : Word ℓ (κ + R) t :=
  if κ + R ≤ 64 then
    let lanes := Vector.ofFn fun u : Fin (2 ^ ℓ) ↦ encodeFast (algebraMap K E) κ R (sliceLow f u)
    let rows := Vector.ofFn fun y : Fin (2 ^ (κ + R)) ↦ Vector.ofFn fun u : Fin (2 ^ ℓ) ↦ lanes[u][y]
    ⟨fun y ↦ rows[y]⟩
  else wordOf ℓ κ R t f

/-- The stored word is the honest word. -/
theorem wordFast_eq (ℓ κ R t : ℕ) (f : CMlPolynomialEval E (ℓ + κ)) :
    wordFast ℓ κ R t f = wordOf ℓ κ R t f := by
  unfold wordFast
  split
  · rename_i h
    simp only [wordOf, Word.mk.injEq]
    funext y
    refine Vector.ext fun u hu ↦ ?_
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact encodeFast_getElem (algebraMap K E) h _ y
  · rfl

/-! ## The folded table from the bound one -/

/-- The table bound on its `ℓ` lane coordinates, as a table on the others. -/
def castLanes {ℓ κ : ℕ} (a : CMlPolynomialEval E (ℓ + κ - ℓ)) : CMlPolynomialEval E κ :=
  Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel_left ℓ κ)) a

/-- A table bound on its low coordinates to `r`, its free ones renamed, is the folded table. -/
private theorem cast_bindLows_eq_foldTable {ℓ κ k : ℕ} (hk : k = κ)
    (T : CMlPolynomialEval E (ℓ + κ)) (h1 : 2 ^ (ℓ + κ) = 2 ^ (ℓ + k)) (r : Vector E ℓ) :
    Vector.cast (congrArg (2 ^ ·) hk) (bindLows (k := k) (Vector.cast h1 T) r) =
      foldTable T r := by
  subst hk
  refine Vector.ext fun x hx ↦ ?_
  have hb : ∀ (t : CMlPolynomialEval E k), t[x] = evalMle t (boolVec ⟨x, hx⟩) := fun t ↦
    (evalMle_boolVec t ⟨x, hx⟩).symm
  simp only [Vector.cast_rfl]
  rw [hb, hb, ← evalMle_append_eq_bindLows, evalMle_foldTable]

/-- The table bound on its lane coordinates to the fold point is the folded table. -/
theorem castLanes_lowCache {ℓ κ : ℕ} (T : CMlPolynomialEval E (ℓ + κ)) (r : Vector E ℓ) :
    castLanes (ProductSum.lowCache T ℓ r) = foldTable T r := by
  rw [castLanes, ProductSum.lowCache, dite_eq_left (Nat.le_add_right ℓ κ)]
  exact cast_bindLows_eq_foldTable (Nat.add_sub_cancel_left ℓ κ) T _ r

/-! ## The round caches -/

/-- A level's fold rounds read the claim's weight's cube and the table. -/
abbrev levelTab (sh : Shape) (κ : ℕ) :
    SumcheckRound.Ctx (Weight E (sh.ℓ + κ)) (OneW sh κ) (Tab (sh.ℓ + κ)) →
      Tab (sh.ℓ + κ) × Tab (sh.ℓ + κ) :=
  fun ctx ↦ (ctx.1.1.onCube, ctx.2)

/-- The fold rounds' cache: the two tables bound to the fold challenges so far. -/
def foldCache (sh : Shape) (κ : ℕ) :
    SumcheckRound.RoundCache (levelFamily sh κ).poly sh.ℓ :=
  ProductSum.roundCache (levelTab sh κ) (Nat.le_add_right _ _)

/-- The tail reads the glued weight's cube and the plaintext table. -/
abbrev tailTab (sh : Shape) (nf : ℕ) :
    SumcheckRound.Ctx (TX (nf + 1)) (OneW sh (nf + 1)) Unit → Tab (nf + 1) × Tab (nf + 1) :=
  fun ctx ↦ (ctx.1.1.1.onCube, ctx.1.1.2)

/-- The tail's cache: the two tables bound to the tail's challenges so far. -/
def tailCache (sh : Shape) (nf : ℕ) :
    SumcheckRound.RoundCache (tailFamily sh nf).poly (nf + 1) :=
  ProductSum.roundCache (tailTab sh nf) le_rfl

/-! ## The folds and the residual claim -/

section Folds

variable (sh : Shape) (κ : ℕ)

/-- The first fold challenge, the tables bound at it. -/
def foldFirstCached : Component.Cached (foldFirst sh κ) ((foldCache sh κ).atMid (j := 0))
    ((foldCache sh κ).at (j := 1)) :=
  SumcheckRound.cachedDrawChallenge (foldCache sh κ) _ 0 (by simp [Shape.ℓ])

/-- The other fold rounds. -/
def foldRestCached : Component.Cached (foldRest sh κ) ((foldCache sh κ).at (j := 1))
    ((foldCache sh κ).at (j := sh.ℓ)) :=
  SumcheckRound.cachedRounds (foldCache sh κ) _ sh.lm1 1 (by simp only [Shape.ℓ]; omega)

/-- The residual claim's first-round polynomial, from the bound tables; the folded table handed
on. -/
def sendResidualCached : Component.Cached (sendResidual sh κ)
    ((foldCache sh κ).at (j := sh.ℓ)) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendResidual
  exact Component.Cached.sendChecked
      (msg := fun _ ab ↦ ProductSum.roundPoly (castLanes ab.1) (castLanes ab.2) 0 #v[])
      (upd := fun _ ab _ ↦ castLanes ab.2)
      (fun p ↦ by
        simp only [foldCache, ProductSum.roundCache, SumcheckRound.RoundCache.at,
          SumcheckRound.ctxOf, levelTab, castLanes_lowCache]
        rfl)
      fun p ↦ by
        simp only [foldCache, ProductSum.roundCache, SumcheckRound.RoundCache.at,
          SumcheckRound.ctxOf, levelTab, castLanes_lowCache]
        rfl

end Folds

/-! ## A level after its folds -/

section Level

variable (sh sh' : Shape) (κ' : ℕ)

/-- The oracles between a level's commitment and its reading: its word and the next one. -/
abbrev BO : Fin 1 ⊕ Unit → Type := Component.besideOracles (OneW sh (Kap sh' κ')) (WordOf sh' κ')

/-- The oracles after the reading: the next level's word. -/
abbrev KO : Fin 1 → Type := Component.keptOracles (BO sh sh' κ') keepNew

/-- The commitment of the next level's word read off a cache holding the folded table and its
word. -/
def commitNextPairCached : Component.Cached (commitNext sh sh' κ')
    (fun p ↦ (foldTable p.2 p.1.1.r, wordFast sh'.ℓ κ' sh'.R sh'.t (foldTable p.2 p.1.1.r)))
    (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold commitNext
  exact Component.Cached.sendOracleBeside (msg := fun _ c ↦ c.2) (upd := fun _ c ↦ c.1)
    (fun _ ↦ wordFast_eq _ _ _ _ _) fun _ ↦ rfl

/-- The commitment of the next level's word, encoded once from the folded table. The word is
built beside the table when the step starts, as data, and the message reads it: a message
computed from the table by a closure would be rebuilt at every read of a row, since compiled code
expands a closure returning a word to take the position as one more argument. -/
def commitNextCached : Component.Cached (commitNext sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) :=
  (commitNextPairCached sh sh' κ').adaptIn (fun _ g ↦ (g, wordFast sh'.ℓ κ' sh'.R sh'.t g))
    fun _ ↦ rfl

/-- The out-of-domain point, the folded table carried through. -/
def drawPointCached : Component.Cached (drawPoint sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.1.r) := by
  unfold drawPoint
  exact Component.Cached.drawPushesKeep (BO sh sh' κ') E (S := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ')) (fun p ↦ foldTable p.2 p.1.1.r) (Kap sh' κ')

/-- The out-of-domain answer, from the folded table. -/
def sendOodCached : Component.Cached (sendOod sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendOod
  exact Component.Cached.sendChecked (O := BO sh sh' κ')
      (S := Bd sh (Kap sh' κ') × Vector E (Kap sh' κ')) (W := Tab (sh.ℓ + Kap sh' κ'))
      (msg := fun p g ↦ evalMle g p.1.1.2) (upd := fun _ g _ ↦ g)
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- The out-of-domain claim's first-round polynomial, from the folded table. -/
def sendOodPolyCached : Component.Cached (sendOodPoly sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendOodPoly
  exact Component.Cached.sendChecked (O := BO sh sh' κ') (S := Bd sh (Kap sh' κ'))
      (W := Tab (sh.ℓ + Kap sh' κ')) (msg := fun p g ↦ firstPoly (eqWeight p.1.1.z) g)
      (upd := fun _ g _ ↦ g) (fun _ ↦ rfl) fun _ ↦ rfl

/-- The grinding nonce. -/
def sendNonceCached : Component.Cached (sendNonce (BO sh sh' κ') sh (Kap sh' κ'))
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendNonce
  exact Component.Cached.sendChecked (O := BO sh sh' κ') (S := Bd sh (Kap sh' κ'))
      (W := Tab (sh.ℓ + Kap sh' κ')) (msg := fun _ _ ↦ (0 : E)) (upd := fun _ g _ ↦ g)
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- The sampled positions. -/
def drawPositionsCached : Component.Cached (drawPositions (BO sh sh' κ') sh (Kap sh' κ'))
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold drawPositions
  exact Component.Cached.sample (O := BO sh sh' κ') (S := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ')) (upd := fun _ g _ ↦ g) fun _ _ ↦ rfl

/-- The batching challenge. -/
def drawBatchCached : Component.Cached (drawBatch (BO sh sh' κ') sh (Kap sh' κ'))
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold drawBatch
  exact Component.Cached.sample (O := BO sh sh' κ') (S := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ')) (upd := fun _ g _ ↦ g) fun _ _ ↦ rfl

/-- The reading of the level's word. -/
def readOldCached : Component.Cached (readOld sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold readOld
  exact Component.Cached.queryRecord (O := BO sh sh' κ') (S := Bd sh (Kap sh' κ'))
    (W := Tab (sh.ℓ + Kap sh' κ')) (upd := fun _ g ↦ g) fun _ ↦ rfl

/-- The query batch's first-round polynomial, from the folded table. -/
def sendQueryPolyCached : Component.Cached (sendQueryPoly (KO sh sh' κ') sh (Kap sh' κ'))
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendQueryPoly
  exact Component.Cached.sendChecked (O := KO sh sh' κ') (S := Bd sh (Kap sh' κ'))
      (W := Tab (sh.ℓ + Kap sh' κ'))
      (msg := fun p g ↦ firstPoly (queryWeight (Kap sh' κ') sh.R p.1.1.pos p.1.1.lam) g)
      (upd := fun _ g _ ↦ g) (fun _ ↦ rfl) fun _ ↦ rfl

/-- The glue: the folded table the next level's witness, and its fold rounds' tables started. -/
def glueCached : Component.Cached (glue sh sh' κ')
    (fun p ↦ foldTable p.2 p.1.1.r) ((foldCache sh' κ').atMid (j := 0)) := by
  unfold glue
  exact Component.Cached.mapWitness (O := KO sh sh' κ') (S := Bd sh (Kap sh' κ'))
      (W := Tab (sh.ℓ + Kap sh' κ')) (g' := fun _ g ↦ g)
      (upd := fun p g ↦
        (ProductSum.lowCache (gluedWeight p.1.1.resid p.1.1.z p.1.1.pos p.1.1.lam).onCube 0 #v[],
          ProductSum.lowCache g 0 #v[]))
      (fun _ ↦ rfl) fun _ ↦ rfl

variable {ι₃ : Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₃ i)] {S₃ W₃ : Type}
  {k : List Step}

/-- **A level, cached**, followed by a cached rest of the opening: the fold rounds on bound
tables, the folded table carried through the level, the next word encoded once. -/
def levelCached
    {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)}
    (CR : Component.Cached R ((foldCache sh' κ').atMid (j := 0)) (fun _ ↦ ())) :
    Component.Cached (levelDef sh sh' κ' R) ((foldCache sh (Kap sh' κ')).atMid (j := 0))
      (fun _ ↦ ()) :=
  (foldFirstCached sh (Kap sh' κ')).append <| (foldRestCached sh (Kap sh' κ')).append <|
  (sendResidualCached sh (Kap sh' κ')).append <| (commitNextCached sh sh' κ').append <|
  (drawPointCached sh sh' κ').append <| (sendOodCached sh sh' κ').append <|
  (sendOodPolyCached sh sh' κ').append <| (sendNonceCached sh sh' κ').append <|
  (drawPositionsCached sh sh' κ').append <| (drawBatchCached sh sh' κ').append <|
  (readOldCached sh sh' κ').append <| (sendQueryPolyCached sh sh' κ').append <|
  (glueCached sh sh' κ').append CR

end Level

/-! ## The final level -/

section Final

variable (sh : Shape) (nf : ℕ)

/-- The final level's oracles after its reading: its word. -/
abbrev KF : Fin 1 → Type :=
  Component.keptOracles (OneW sh (nf + 1)) (Function.Embedding.refl (Fin 1))

/-- The plaintext table: the folded table. -/
def sendTableCached : Component.Cached (sendTable sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold sendTable
  exact Component.Cached.sendChecked (O := OneW sh (nf + 1)) (S := Bd sh (nf + 1))
      (W := Tab (sh.ℓ + (nf + 1))) (msg := fun _ g ↦ g) (upd := fun _ g _ ↦ g)
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- The final level's nonce. -/
def finalNonceCached : Component.Cached (finalNonce sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold finalNonce
  exact Component.Cached.sendChecked (O := OneW sh (nf + 1)) (S := FBd sh (nf + 1))
      (W := Tab (sh.ℓ + (nf + 1))) (msg := fun _ _ ↦ (0 : E)) (upd := fun _ g _ ↦ g)
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- The final level's positions. -/
def finalPositionsCached : Component.Cached (finalPositions sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold finalPositions
  exact Component.Cached.sample (O := OneW sh (nf + 1)) (S := FBd sh (nf + 1))
    (W := Tab (sh.ℓ + (nf + 1))) (upd := fun _ g _ ↦ g) fun _ _ ↦ rfl

/-- The final level's batching challenge. -/
def finalBatchCached : Component.Cached (finalBatch sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold finalBatch
  exact Component.Cached.sample (O := OneW sh (nf + 1)) (S := FBd sh (nf + 1))
    (W := Tab (sh.ℓ + (nf + 1))) (upd := fun _ g _ ↦ g) fun _ _ ↦ rfl

/-- The reading of the last word. -/
def readFinalCached : Component.Cached (readFinal sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun p ↦ foldTable p.2 p.1.1.r) := by
  unfold readFinal
  exact Component.Cached.queryRecord (O := OneW sh (nf + 1)) (S := FBd sh (nf + 1))
    (W := Tab (sh.ℓ + (nf + 1))) (upd := fun _ g ↦ g) fun _ ↦ rfl

/-- The final query batch's first-round polynomial, from the folded table. -/
def finalQueryPolyCached : Component.Cached (finalQueryPoly sh nf)
    (fun p ↦ foldTable p.2 p.1.1.r) (fun _ ↦ ()) := by
  unfold finalQueryPoly
  exact Component.Cached.sendChecked (O := OneW sh (nf + 1)) (S := FBd sh (nf + 1))
      (W := Tab (sh.ℓ + (nf + 1)))
      (msg := fun p g ↦ firstPoly (queryWeight (nf + 1) sh.R p.1.1.pos p.1.1.lam) g)
      (upd := fun _ _ _ ↦ ()) (fun _ ↦ rfl) fun _ ↦ rfl

/-- The tail's glue: its tables started. -/
def glueFinalCached : Component.Cached (glueFinal sh nf) (fun _ ↦ ())
    ((tailCache sh nf).atMid (j := 0)) := by
  unfold glueFinal
  exact Component.Cached.mapWitness (O := KF sh nf) (S := FBd sh (nf + 1))
      (W := Tab (sh.ℓ + (nf + 1))) (g' := fun _ _ ↦ ())
      (upd := fun p _ ↦
        (ProductSum.lowCache
          (Weight.batch ![p.1.1.resid, queryWeight (nf + 1) sh.R p.1.1.pos p.1.1.lam]
            p.1.1.lam).onCube 0 #v[], ProductSum.lowCache p.1.1.ff 0 #v[]))
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- The terminal check. -/
def terminalCached : Component.Cached (terminal sh nf) ((tailCache sh nf).at (j := nf + 1))
    (fun _ ↦ ()) := by
  unfold terminal
  exact Component.Cached.passCheck (O := OneW sh (nf + 1))
    (S := SumcheckRound.Stmt (TX (nf + 1)) E (nf + 1)) (W := Unit) (upd := fun _ _ ↦ ())
    fun _ ↦ rfl

/-- **The final level, cached.** -/
def finalCached : Component.Cached (finalDef sh nf) ((foldCache sh (nf + 1)).atMid (j := 0))
    (fun _ ↦ ()) :=
  (foldFirstCached sh (nf + 1)).append <| (foldRestCached sh (nf + 1)).append <|
  (sendResidualCached sh (nf + 1)).append <| (sendTableCached sh nf).append <|
  (finalNonceCached sh nf).append <| (finalPositionsCached sh nf).append <|
  (finalBatchCached sh nf).append <| (readFinalCached sh nf).append <|
  (finalQueryPolyCached sh nf).append <| (glueFinalCached sh nf).append <|
  (SumcheckRound.cachedDrawChallenge (tailCache sh nf) _ 0 (Nat.succ_pos nf)).append <|
  (SumcheckRound.cachedRounds (tailCache sh nf) _ nf 1 (by omega)).append <|
  terminalCached sh nf

end Final

/-! ## The opening -/

/-- **The chain of levels, cached.** -/
def Ladder.compCached : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    Component.Cached L.comp ((foldCache sh κ).atMid (j := 0)) (fun _ ↦ ())
  | _, _, .last sh nf => finalCached sh nf
  | _, _, @Ladder.cons sh sh' κ' L => levelCached sh sh' κ' L.compCached

section Open

variable (sh : Shape) (κ : ℕ)

/-- The relayout, the first tables built. -/
def stackRelayoutCached : Component.Cached (stackRelayout sh κ) (fun _ ↦ ())
    (fun p ↦ (p.1.1.1.onCube, p.2)) := by
  unfold stackRelayout
  exact Component.Cached.mapWitness (O := OneW sh κ) (S := Weight E (κ + sh.ℓ) × E)
      (W := Tab (κ + sh.ℓ)) (g' := fun p _ ↦ relayout p.2)
      (upd := fun p _ ↦ ((relayoutWeight p.1.1.1).onCube, relayout p.2)) (fun _ ↦ rfl) fun _ ↦ rfl

/-- The first-round polynomial of the opening claim, from its tables. -/
def sendFirstCached : Component.Cached (sendFirst sh κ) (fun p ↦ (p.1.1.1.onCube, p.2))
    ((foldCache sh κ).atMid (j := 0)) := by
  unfold sendFirst
  exact Component.Cached.sendChecked (O := OneW sh κ) (S := Weight E (sh.ℓ + κ) × E)
      (W := Tab (sh.ℓ + κ)) (T := SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E 0 2)
      (M := SumcheckRound.Message E 2) (msg := fun p _ ↦ firstPoly p.1.1.1 p.2)
      (upd := fun _ ab _ ↦ (ProductSum.lowCache ab.1 0 #v[], ProductSum.lowCache ab.2 0 #v[]))
      (fun _ ↦ rfl) fun _ ↦ rfl

/-- **The opening of WHIR, cached**: the relayout, the first-round polynomial and the chain of
levels, each table built once. -/
def whirOpenCached (L : Ladder sh κ) :
    Component.Cached (whirOpen sh κ L) (fun _ ↦ ()) (fun _ ↦ ()) :=
  (stackRelayoutCached sh κ).append <| (sendFirstCached sh κ).append L.compCached

end Open

end Whir

end

end LeanerVM.Protocol
