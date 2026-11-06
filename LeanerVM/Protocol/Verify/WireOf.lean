/-
  LeanerVM.Protocol.Verify.WireOf

  The executable verifier's wire read off a transcript of the compiled oracle protocol: every
  scalar and challenge where the verifier's walk records it, each round polynomial without the
  coefficient the chain does not absorb, WHIR's query positions as numbers.
-/

module

public import LeanerVM.Protocol.Verify
public import LeanerVM.Protocol.ListBinding

/-!
# The wire of a transcript

`wireOf` reads the executable verifier's wire (`Verify.Wire`) off a full transcript of the
compiled protocol (`listBindingSpec`): every scalar and challenge where the walk records it, each
round polynomial without the coefficient the chain does not absorb (`RoundPoly.encode`), WHIR's
query positions as numbers. A transcript carries words where the chain carries roots, so the
roots read off a transcript are the default digest. `Whir.Ladder.shapes` are the levels' shapes
the verifier walks a chain of levels by.

The chain-history decoder reads the walk's wire back into a transcript by these same functions,
and the honest prover's completeness reads the prover's transcript by them.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval
  ProtocolSpec StepSchedule Verify Whir

@[expose] public section

namespace Whir.Ladder

/-- The levels' shapes of a chain of levels, as the verifier walks them. -/
def shapes : {sh : Whir.Shape} → {κ : ℕ} → Ladder sh κ → List LevelShape
  | _, _, .last sh nf => [⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩]
  | _, _, @Ladder.cons sh sh' κ' L => ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ :: L.shapes

end Whir.Ladder

namespace DecodeChain

/-! ## One-round transcripts and runs of draws -/

/-- The challenge of a schedule of one challenge. -/
abbrev drawOf {C : Type} (t : (draw C).FullTranscript) : C := t 0

/-- The message of a schedule of one message. -/
abbrev msgOf {M : Type} (t : (say M).FullTranscript) : M := t 0

/-- The challenges of a run of draws, in order. -/
def drawsList : (k : ℕ) → (draws E k).FullTranscript → List E
  | 0, _ => []
  | k + 1, t => drawsList k (FullTranscript.fst (pSpec₁ := draws E k) (pSpec₂ := draw E) t) ++
      [drawOf (FullTranscript.snd (pSpec₁ := draws E k) (pSpec₂ := draw E) t)]

/-! ## The wire of a transcript -/

/-- A round polynomial's wire, the coefficient at `drop` left out. -/
def polyWire {d : ℕ} (drop : ℕ) (p : Vector E (d + 1)) : List E := p.toList.eraseIdx drop

/-- A round's wire: its polynomial's, and its challenge. -/
def roundWire {d : ℕ} (drop : ℕ) (t : (roundSpec E d).FullTranscript) : Round :=
  ⟨polyWire drop (msgOf t.fst), drawOf t.snd⟩

/-- The wires of a run of rounds. -/
def roundsWire {d : ℕ} (drop : ℕ) : (m : ℕ) → (roundsSpec E d m).FullTranscript → List Round
  | 0, _ => []
  | m + 1, t =>
    roundWire drop (FullTranscript.fst (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t) ::
      roundsWire drop m
        (FullTranscript.snd (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t)

/-- A layer's combiner. -/
def layerCombiner {ρ m : ℕ} (t : (stepSpec E 3 ρ m).FullTranscript) : E := drawOf t.fst.fst.fst

/-- A layer of the grand product as the walk records it, with the combiner drawn after it. -/
def layerWire {ρ m : ℕ} (t : (stepSpec E 3 ρ m).FullTranscript) (next : E) : GkrLayer :=
  ⟨roundsWire 0 m t.fst.fst.snd, List.ofFn fun i ↦ (msgOf t.fst.snd i).toList,
    drawsList ρ t.snd, next⟩

/-- Layers of radix four, with the combiner drawn after the last: the first layer's combiner and the
layers as the walk records them. -/
def stepsWire : (k m : ℕ) → (stepsSpec E 3 k m).FullTranscript → E → E × List GkrLayer
  | 0, _, _, last => (last, [])
  | k + 1, m, t, last =>
    let rest := stepsWire k (m + 2)
      (FullTranscript.snd (pSpec₁ := stepSpec E 3 2 m) (pSpec₂ := stepsSpec E 3 k (m + 2)) t) last
    let l := FullTranscript.fst (pSpec₁ := stepSpec E 3 2 m) (pSpec₂ := stepsSpec E 3 k (m + 2)) t
    (layerCombiner l, layerWire l rest.1 :: rest.2)

/-- The binary layer before the others, if there is one. -/
def oddWire : (r : ℕ) → (oddSpec E 3 r).FullTranscript → E × List GkrLayer → E × List GkrLayer
  | 0, _, p => p
  | _ + 1, t, p => (layerCombiner (ρ := 1) (m := 0) t, layerWire (ρ := 1) (m := 0) t p.1 :: p.2)

/-- The grand product's combiner after the roots and its layers, as the walk records them. -/
def gkrWire (μ : ℕ) (t : (gkrSpec E 3 μ).FullTranscript) : E × List GkrLayer :=
  oddWire (μ % 2) t.fst.fst (stepsWire (μ / 2) (μ % 2) t.fst.snd (drawOf t.snd))

/-- The bus phase's wire. -/
def busWireOf (I : M3Instance) (t : (busSpec I).FullTranscript) : BusWire :=
  let t₃ := FullTranscript.fst
    (pSpec₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus)
    (pSpec₂ := say (Vector E I.busClaims)) t
  let vals := FullTranscript.snd
    (pSpec₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus)
    (pSpec₂ := say (Vector E I.busClaims)) t
  let fp := drawOf t₃.fst.fst
  let roots := msgOf t₃.fst.snd
  let g := gkrWire I.μBus t₃.snd
  ⟨List.ofFn fp.1, fp.2, roots.1, roots.2, g.1, g.2, (msgOf vals).toList⟩

/-- The table sumcheck's wire. -/
def tableWireOf (I : M3Instance) (t : (tableSpec I).FullTranscript) : TableWire :=
  let t₂ := FullTranscript.fst (pSpec₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (pSpec₂ := say (Vector E I.tableColumns)) t
  let vals := FullTranscript.snd (pSpec₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (pSpec₂ := say (Vector E I.tableColumns)) t
  ⟨drawOf t₂.fst, roundsWire 1 I.τmax t₂.snd, (msgOf vals).toList⟩

/-- The public input's wire. -/
def pubWireOf (t : pubSpec.FullTranscript) : PubWire := ⟨t 0, t 1⟩

/-- The Flock phase's wire for `2 ^ k` compressions. -/
def flockWireOf (k : ℕ) (t : (flockSpecOf k).FullTranscript) : FlockWire :=
  let t₉ := t.fst
  let t₈ := t₉.fst
  let t₇ := t₈.fst
  let t₆ := t₇.fst
  let t₅ := t₆.fst
  let t₄ := t₅.fst
  let t₃ := t₄.fst
  let t₂ := t₃.fst
  ⟨drawsList (k + 1) t₂.fst, (msgOf t₂.snd).toList, drawOf t₃.snd,
    roundsWire 0 8 t₄.snd ++ roundsWire 0 k t₅.snd, (msgOf t₆.snd).toList, drawOf t₇.snd,
    roundsWire 1 8 t₈.snd, (msgOf t₉.snd).toList, drawsList 6 t.snd⟩

/-- The Flock slot's wire. -/
def flockWireOpt (I : M3Instance) :
    (o : Option (FlockRegion I.toShape)) → (flockSpecOpt I o).FullTranscript → FlockWire
  | none, _ => default
  | some r, t => flockWireOf r.kBatch t

/-- The first step of a list's transcript. -/
abbrev seqHead {a : Step} {l : List Step} (t : (seqSpec (a :: l)).FullTranscript) :
    a.spec.FullTranscript :=
  FullTranscript.fst (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) t

/-- The rest of a list's transcript. -/
abbrev seqTail {a : Step} {l : List Step} (t : (seqSpec (a :: l)).FullTranscript) :
    (seqSpec l).FullTranscript :=
  FullTranscript.snd (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) t

/-- Fold rounds as the walk records them: each challenge with the wire of the polynomial after it,
from the first challenge, the rounds and the last polynomial's wire. -/
def foldsWire : E → List Round → List E → List Fold
  | c, [], w => [⟨c, w⟩]
  | c, r :: rs, w => ⟨c, r.wire⟩ :: foldsWire r.chal rs w

/-- The query positions as numbers. -/
def positionsList {t b : ℕ} (pos : Fin t → Fin (2 ^ b)) : List ℕ := List.ofFn fun q ↦ (pos q).val

/-- A level with a successor as the walk records it, its root the default digest, and the rest of
the opening's transcript. -/
def levelWire {sh sh' : Whir.Shape} {κ' : ℕ} {k : List Step}
    (t : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript) :
    WhirLevel × (seqSpec k).FullTranscript :=
  let r₁ := seqTail t
  let r₂ := seqTail r₁
  let r₃ := seqTail r₂
  let r₄ := seqTail r₃
  let r₅ := seqTail r₄
  let r₆ := seqTail r₅
  let r₇ := seqTail r₆
  let r₈ := seqTail r₇
  let r₉ := seqTail r₈
  let r₁₀ := seqTail r₉
  let r₁₁ := seqTail r₁₀
  let r₁₂ := seqTail r₁₁
  (⟨foldsWire (drawOf (seqHead t)) (roundsWire 1 sh.lm1 (seqHead r₁))
      (polyWire 1 (msgOf (seqHead r₂))), some default, drawsList (Kap sh' κ') (seqHead r₄),
    msgOf (seqHead r₅), polyWire 1 (msgOf (seqHead r₆)), [], msgOf (seqHead r₇),
    positionsList (drawOf (seqHead r₈)), drawOf (seqHead r₉), polyWire 1 (msgOf (seqHead r₁₁)),
    []⟩, seqTail r₁₂)

/-- The final level as the walk records it. -/
def finalWire {sh : Whir.Shape} {nf : ℕ} (t : (seqSpec (finalSteps sh nf)).FullTranscript) :
    WhirLevel :=
  let r₁ := seqTail t
  let r₂ := seqTail r₁
  let r₃ := seqTail r₂
  let r₄ := seqTail r₃
  let r₅ := seqTail r₄
  let r₆ := seqTail r₅
  let r₇ := seqTail r₆
  let r₈ := seqTail r₇
  let r₉ := seqTail r₈
  let r₁₀ := seqTail r₉
  let r₁₁ := seqTail r₁₀
  ⟨foldsWire (drawOf (seqHead t)) (roundsWire 1 sh.lm1 (seqHead r₁))
      (polyWire 1 (msgOf (seqHead r₂))), none, [], 0, [],
    Vector.toList (msgOf (seqHead r₃) : Vector E (2 ^ (nf + 1))), msgOf (seqHead r₄),
    positionsList (drawOf (seqHead r₅)), drawOf (seqHead r₆), polyWire 1 (msgOf (seqHead r₈)),
    foldsWire (drawOf (seqHead r₁₀)) (roundsWire 1 nf (seqHead r₁₁)) []⟩

/-- A chain of levels as the walk records it. -/
def ladderWire : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    (seqSpec L.steps).FullTranscript → List WhirLevel
  | _, _, .last _ _, t => [finalWire t]
  | _, _, @Ladder.cons _ _ _ L, t => (levelWire t).1 :: ladderWire L (levelWire t).2

/-- WHIR's opening as the walk records it: the first round polynomial's wire and the levels. -/
def whirWireOf {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript) :
    List E × List WhirLevel :=
  (polyWire 1 (msgOf (seqHead (seqTail t))), ladderWire L (seqTail (seqTail t)))

/-- **The wire of a transcript of the compiled protocol**, as the verifier's walk records it: its
roots the default digest. -/
def wireOf (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t : (listBindingSpec I sh κ L).FullTranscript) : Wire :=
  let f₇ := t.fst
  let f₆ := f₇.fst
  let f₅ := f₆.fst
  let f₄ := f₅.fst
  let f₃ := f₄.fst
  let f₂ := f₃.fst
  let w := whirWireOf L t.snd
  ⟨default, busWireOf I f₂.snd, tableWireOf I f₃.snd, pubWireOf f₄.snd,
    flockWireOpt I I.flock f₅.snd, drawOf f₆.snd, w.1, w.2⟩

end DecodeChain

end
end LeanerVM.Protocol
