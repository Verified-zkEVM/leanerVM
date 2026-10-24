/-
  LeanerVM.Protocol.DecodeChain

  The chain history of leanVM's verifier read back as a transcript of the compiled oracle
  protocol: the walk's primitives on a history, the words the oracle messages take, and the slot
  decoders of every phase, with the dropped coefficient of each round polynomial rebuilt from the
  running claim.
-/

module

public import LeanerVM.Protocol.Verify
public import LeanerVM.Protocol.Verify.WireOf
public import LeanerVM.Protocol.RandomOracleGame
public import LeanerVM.Protocol.ToArkLib.DecodeSteps

/-!
# Decoding the chain history

The executable verifier (`LeanerVM.Protocol.Verify`) walks the Fiat–Shamir chain over five
primitives (`Verify.ChainOps`). A run of the chain leaves its history, the blocks it absorbed,
each with the state its step led to (`chainHistory`, `List (Block × Digest)`). This module reads
a history back as a prefix of the transcript of the compiled protocol of the list-binding
compilation at leanVM (`deployedSpec`, `listBindingSpec` of the leanISA instance at WHIR's deployed
chain).

* **The walk on a history** (`historyOps`): a scalar is an observe step, a challenge is the state
  of a squeeze step through `FsState.challengeOf`, a root is two observe steps whose scalars encode
  a digest, a nonce is a nonce step (its grinding check is not a step, and is not checked here),
  and there is no opening. Every slot of the decoder that reads the chain is the verifier's walk
  run on this reader: `walkPositions historyOps` reads WHIR's query positions, `samples
  historyOps 4` the fingerprint challenges.
* **The words** (`Words`): the oracle messages carry words, which the chain does not: level 0's
  `KWord` and the word every later level commits to. The decoder takes them as a parameter, reads
  each commitment's root off the chain, and checks nothing of it against the word. `Words.zero` is
  the supplier of zero words.
* **The rebuilt coefficients.** The compiled protocol sends every coefficient of a round
  polynomial; the chain absorbs all but one (`RoundPoly.encode`). The decoder rebuilds the dropped
  one from the running claim (`RoundPoly.decode`), carrying the claim through the rounds as the
  verifier's algebra does (`replayRounds`, `replayGkr`, `flockStep`, `replayFolds`): from the
  roots in the bus phase, from the bus phase's output in the table sumcheck, from the skip values
  and the terminal values in the Flock phase, and from the batched opening claim, the out-of-domain
  values and the folded query rows in WHIR. The statement between two phases is the compiled
  verifier's own (`Component.Front.out` of each phase of `leanVmPhases`). A query batch's claim is
  read off the level's word at the decoded positions, so it is the supplied word's.
* **Decoding** (`decoder`, `decodePrefix`, `decode`): the generic decoders of
  `LeanerVM.Protocol.ToArkLib.DecodeTranscript` at the compiled schedule; `decodePrefix` is the
  longest prefix of the transcript that reads the history exactly. The announced sizes are read
  first and must be the decoder's, so a history decodes at one announcement only.
  `decodePrefix_isSome_indep`: whether a history decodes, and to how many rounds, does not depend
  on the words, since no slot's reading does.

Transcribed for the stream order from the pinned leanVM
(`a386121f84292f6fa663aaa3e570c15bc0240ea2`), through the executable verifier's walk.

Classification: T4 in the random-oracle model, the deterministic core: the reader of chain
histories that the random-oracle bound charges (`LeanerVM.Protocol.LeanVmReader`). The core's step
from an accepted history to the compiled verifier's checks on its decoded transcript uses the
compiled protocol's per-phase equations at the same `wireOf` projections (`busWireOf`,
`tableWireOf`, `pubWireOf`, `flockWireOpt`, `whirWireOf` of the transcript's slices).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval
  ProtocolSpec StepSchedule Verify Whir SlotDecoder

@[expose] public section

namespace DecodeChain

/-- A reading of the chain's history: a block and the state its step leads to. -/
abbrev Reading : Type := Block × Digest

/-! ## The walk on a history -/

/-- The element an observe step absorbs. -/
def scalarOf : Reading → Option E
  | (.observe x, _) => some x
  | _ => none

/-- The challenge a squeeze step gives: its state's first three 64-bit words. -/
def challengeOf : Reading → Option E
  | (.squeeze, d) => some (FsState.challengeOf d)
  | _ => none

/-- The nonce a nonce step absorbs. -/
def nonceOf : Reading → Option E
  | (.nonce n, _) => some n
  | _ => none

/-- **The walk's primitives on a chain history**: a scalar is an observe step, a challenge a
squeeze step's state through `FsState.challengeOf`, a root two observe steps whose scalars encode
a digest, a nonce a nonce step, its grinding check unchecked; there is no opening. -/
def historyOps : ChainOps (Slot Reading) where
  nextScalar := Slot.next scalarOf
  sample := Slot.next challengeOf
  nextRoot := do
    let a ← Slot.next scalarOf
    let b ← Slot.next scalarOf
    match digestOfScalars (a, b) with
    | some d => pure d
    | none => Slot.fail
  checkPow _ := Slot.next nonceOf
  nextOpening _ _ _ _ _ := Slot.fail

/-! ## Slots -/

/-- A list as a vector of the given length, cut or padded with zeros. -/
def toVec (n : ℕ) (l : List E) : Vector E n := Vector.ofFn fun i ↦ l.getD i 0

/-- `n` scalars, as a vector. -/
def vecSlot (n : ℕ) : Slot Reading (Vector E n) := toVec n <$> historyOps.nextScalars n

/-- A round polynomial of degree `d`: its `d` wire coefficients, and the dropped one rebuilt from
the claim (`RoundPoly.decode`, with the equality weight `eq?` of its round). The claim and the
weight are thunks, computed only when the wire is read. -/
def polySlot (d : ℕ) (claim : Thunk E) (eq? : Thunk (Option E)) :
    Slot Reading (Vector E (d + 1)) := do
  let w ← historyOps.nextScalars d
  match RoundPoly.decode d claim.get eq?.get w with
  | some c => pure c
  | none => Slot.fail

/-- The `t` query positions of `b` bits, as WHIR's walk reads them. -/
def positionsSlot (b t : ℕ) : Slot Reading (Fin t → Fin (2 ^ b)) :=
  positionsOf t b <$> walkPositions historyOps b t t

/-! ## Runs of rounds -/

/-- After a round from the claim `σ.1` at round `σ.2`: its polynomial at its challenge, at the
next round. -/
def roundNext {d : ℕ} (σ : Thunk E × ℕ) (t : (roundSpec E d).FullTranscript) : Thunk E × ℕ :=
  (Thunk.mk fun _ ↦ RoundPoly.eval (t.fst 0) (t.snd 0), σ.2 + 1)

/-- The claim and the round after a run of rounds. -/
def roundsNext {d : ℕ} (σ : Thunk E × ℕ) :
    (m : ℕ) → (roundsSpec E d m).FullTranscript → Thunk E × ℕ
  | 0, _ => σ
  | m + 1, t => roundsNext
      (roundNext σ (FullTranscript.fst (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t))
      m (FullTranscript.snd (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t)

/-- The challenges of a run of rounds, in order. -/
def roundsChals {d : ℕ} : (m : ℕ) → (roundsSpec E d m).FullTranscript → List E
  | 0, _ => []
  | m + 1, t =>
    ((FullTranscript.fst (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t).snd 0 : E) ::
      roundsChals m (FullTranscript.snd (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d m) t)

/-- `m` sumcheck rounds of degree `d` from the claim `σ.1` at round `σ.2`: the polynomial of
round `j` rebuilt with the weight `eq? j`, each challenge evaluating it into the next claim
(`replayRounds`). -/
def roundsDec (d : ℕ) (eq? : ℕ → Option E) (σ : Thunk E × ℕ) (m : ℕ) :
    SlotDecoder Reading (roundsSpec E d m) :=
  SlotDecoder.rounds (fun σ ↦ polySlot d σ.1 (Thunk.mk fun _ ↦ eq? σ.2)) (fun _ ↦ historyOps.sample)
    roundNext σ m

/-! ## The bus phase -/

/-- The grand product between two layers: the point so far and the trees' claims there, as a
thunk. -/
abbrev GkrState : Type := Thunk (List E × (Fin 3 → E))

/-- The descendants of the three trees at a layer of radix `2 ^ ρ`. -/
def childrenSlot (ρ : ℕ) : Slot Reading (Fin 3 → Vector E (2 ^ ρ)) := do
  let c₀ ← vecSlot (2 ^ ρ)
  let c₁ ← vecSlot (2 ^ ρ)
  let c₂ ← vecSlot (2 ^ ρ)
  return ![c₀, c₁, c₂]

/-- A layer of radix `2 ^ ρ` at depth `m`: the combiner, the rounds from the combined claim with
the point's equality weights, the descendants and the combination challenges (`replayGkr`). -/
def layerDec (st : GkrState) (ρ m : ℕ) : SlotDecoder Reading (stepSpec E 3 ρ m) :=
  SlotDecoder.append
    (pSpec₁ := draw E ++ₚ roundsSpec E (2 ^ ρ) m ++ₚ say (Fin 3 → Vector E (2 ^ ρ)))
    (pSpec₂ := draws E ρ)
    (SlotDecoder.append (pSpec₁ := draw E ++ₚ roundsSpec E (2 ^ ρ) m)
      (pSpec₂ := say (Fin 3 → Vector E (2 ^ ρ)))
      (SlotDecoder.append (pSpec₁ := draw E) (pSpec₂ := roundsSpec E (2 ^ ρ) m)
        (single historyOps.sample) fun t ↦
          roundsDec (2 ^ ρ) (fun j ↦ st.get.1[j]?) (Thunk.mk fun _ ↦ powerBatch st.get.2 (t 0), 0)
            m)
      fun _ ↦ single (childrenSlot ρ))
    fun _ ↦ SlotDecoder.draws historyOps.sample ρ

/-- The state after a layer: the combination challenges before the rounds' challenges, and each
tree's descendants interpolated at the combination challenges. -/
def layerNext {ρ m : ℕ} (t : (stepSpec E 3 ρ m).FullTranscript) : GkrState := Thunk.mk fun _ ↦
  let u := drawsList ρ t.snd
  let ch : Fin 3 → Vector E (2 ^ ρ) := t.fst.snd 0
  (u ++ roundsChals m t.fst.fst.snd, fun i ↦ evalMle (ch i) (toVec ρ u))

/-- `k` layers of radix four from depth `m`. -/
def stepsDec : GkrState → (k m : ℕ) → SlotDecoder Reading (stepsSpec E 3 k m)
  | _, 0, _ => SlotDecoder.empty
  | st, k + 1, m => SlotDecoder.append (pSpec₁ := stepSpec E 3 2 m)
      (pSpec₂ := stepsSpec E 3 k (m + 2)) (layerDec st 2 m) fun t ↦
        stepsDec (layerNext t) k (m + 2)

/-- The binary layer, if there is one. -/
def oddDec (st : GkrState) : (r : ℕ) → SlotDecoder Reading (oddSpec E 3 r)
  | 0 => SlotDecoder.empty
  | _ + 1 => layerDec st 1 0

/-- The state after the binary layer, if there is one. -/
def oddNext (st : GkrState) : (r : ℕ) → (oddSpec E 3 r).FullTranscript → GkrState
  | 0, _ => st
  | _ + 1, t => layerNext t

/-- The grand product for trees of `2 ^ μ` leaves, from the roots' state: the binary layer, the
layers of radix four, and the last combiner. -/
def gkrDec (st : GkrState) (μ : ℕ) : SlotDecoder Reading (gkrSpec E 3 μ) :=
  SlotDecoder.append
    (SlotDecoder.append (oddDec st (μ % 2)) fun t ↦ stepsDec (oddNext st _ t) (μ / 2) (μ % 2))
    fun _ ↦ single historyOps.sample

/-- The fingerprint challenges `α` and `β`. -/
def fingerprintSlot : Slot Reading ((Fin 4 → E) × E) := do
  let a ← samples historyOps 4
  let b ← historyOps.sample
  return (fun i ↦ a.getD i 0, b)

/-- The two roots: the push and pull trees', then the count tree's. -/
def rootsSlot : Slot Reading (E × E) := do
  let a ← historyOps.nextScalar
  let b ← historyOps.nextScalar
  return (a, b)

/-- The bus phase: the fingerprint challenges, the roots, the grand product from the roots and the
boundary values. -/
def busDec (I : M3Instance) : SlotDecoder Reading (busSpec I) :=
  SlotDecoder.append
    (pSpec₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus)
    (pSpec₂ := say (Vector E I.busClaims))
    (SlotDecoder.append (pSpec₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E))
      (pSpec₂ := gkrSpec E 3 I.μBus)
      (SlotDecoder.append (pSpec₁ := draw ((Fin 4 → E) × E)) (pSpec₂ := say (E × E))
        (single fingerprintSlot) fun _ ↦ single rootsSlot)
      fun t ↦ gkrDec (Thunk.mk fun _ ↦ ([], ![(t.snd 0).1, (t.snd 0).1, (t.snd 0).2])) I.μBus)
    fun _ ↦ single (vecSlot I.busClaims)

/-! ## The table sumcheck and the public input -/

/-- The table sumcheck from the bus phase's output: `ξ`, the cubic rounds from the claims batched
by `ξ`, and the columns' values. -/
def tableDec (I : M3Instance) (s : Thunk (I.Stmt × BusOut I)) :
    SlotDecoder Reading (tableSpec I) :=
  SlotDecoder.append (pSpec₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (pSpec₂ := say (Vector E I.tableColumns))
    (SlotDecoder.append (pSpec₁ := draw E) (pSpec₂ := roundsSpec E 3 I.τmax)
      (single historyOps.sample) fun t ↦
        roundsDec 3 (fun _ ↦ none)
          (Thunk.mk fun _ ↦ powerBatch (TableSumcheck.claimed I s.get) (t 0), 0) I.τmax)
    fun _ ↦ single (vecSlot I.tableColumns)

/-- The public input: `r`, then `n` values. -/
def pubDec (n : ℕ) : SlotDecoder Reading pubSpec where
  slot
    | ⟨0, _⟩, _ => historyOps.sample
    | ⟨1, _⟩, _ => historyOps.nextScalars n
    | ⟨k + 2, h⟩, _ => absurd h (by omega)

/-! ## The Flock phase -/

section Flock

variable (k : ℕ)

/-- The Flock phase's first two parts, the drawn coordinates and the skip values. -/
abbrev flockSpec₂ := draws E (k + 1) ++ₚ say (Vector E 64)
/-- Then `z_skip`. -/
abbrev flockSpec₃ := flockSpec₂ k ++ₚ draw E
/-- Then the zerocheck's within-block rounds. -/
abbrev flockSpec₄ := flockSpec₃ k ++ₚ roundsSpec E 2 8
/-- Then its batch rounds. -/
abbrev flockSpec₅ := flockSpec₄ k ++ₚ roundsSpec E 2 k
/-- Then `â, b̂`. -/
abbrev flockSpec₆ := flockSpec₅ k ++ₚ say (Vector E 2)
/-- Then the lincheck's `α`. -/
abbrev flockSpec₇ := flockSpec₆ k ++ₚ draw E
/-- Then the lincheck's rounds. -/
abbrev flockSpec₈ := flockSpec₇ k ++ₚ roundsSpec E 2 8
/-- Then the slices. -/
abbrev flockSpec₉ := flockSpec₈ k ++ₚ say (Vector E 64)

/-- The zerocheck point of the drawn coordinates. -/
def flockPoint (t : (draws E (k + 1)).FullTranscript) :
    Vector E ((flockParams k).m + (flockParams k).κ) :=
  (flockParams k).point (toVec (flockParams k).nRand (drawsList (k + 1) t))

/-- The zerocheck's starting claim: `P(z_skip)` from the 64 assumed zeros and the values sent
(`Flock.skipClaim`). -/
def skipClaimOf (t : (flockSpec₃ k).FullTranscript) : E :=
  Flock.skipClaim (flockParams k).nodes (t.fst.snd 0) (t.snd 0)

/-- The zerocheck's equality weights, the point's coordinates. -/
def zcWeights (t : (flockSpec₃ k).FullTranscript) (j : ℕ) : Option E :=
  (flockPoint k t.fst.fst)[j]?

/-- The state after the zerocheck's within-block rounds. -/
def zcMid (t : (flockSpec₄ k).FullTranscript) : Thunk E × ℕ :=
  roundsNext (Thunk.mk fun _ ↦ skipClaimOf k t.fst, 0) 8 t.snd

/-- The lincheck's starting claim: `v_a + α v_b + α² v_c + α³`, with `v_c = â·b̂ − R` from the
zerocheck's final claim `R` (`Flock.termNext`, `Flock.alphaNext`). -/
def linClaimOf (t : (flockSpec₇ k).FullTranscript) : E :=
  let t₆ := t.fst
  let t₅ := t₆.fst
  let t₄ := t₅.fst
  let claimZ := (roundsNext (zcMid k t₄) k t₅.snd).1.get
  let χ : Vector E ((flockParams k).m + (flockParams k).κ) :=
    toVec _ (roundsChals 8 t₄.snd ++ roundsChals k t₅.snd)
  (Flock.alphaNext (S := Unit)
    (Flock.termNext ((((), flockPoint k t₄.fst.fst.fst, t₄.fst.snd 0), (χ, claimZ)) :
      SumcheckRound.Stmt (Flock.ZcX Unit E _) E _) (t₆.snd 0)) (t.snd 0)).2.2

/-- The Flock phase for `2 ^ k` compressions (`flockStep`): the point's coordinates, the skip
values, `z_skip`, the zerocheck's rounds with the point's equality weights from `P(z_skip)`,
`â, b̂`, `α`, the lincheck's rounds from its batched claim, the slices and the ring-switching
challenges. -/
def flockDecOf : SlotDecoder Reading (flockSpecOf k) :=
  SlotDecoder.append (pSpec₁ := flockSpec₉ k) (pSpec₂ := draws E 6)
  (SlotDecoder.append (pSpec₁ := flockSpec₈ k) (pSpec₂ := say (Vector E 64))
  (SlotDecoder.append (pSpec₁ := flockSpec₇ k) (pSpec₂ := roundsSpec E 2 8)
  (SlotDecoder.append (pSpec₁ := flockSpec₆ k) (pSpec₂ := draw E)
  (SlotDecoder.append (pSpec₁ := flockSpec₅ k) (pSpec₂ := say (Vector E 2))
  (SlotDecoder.append (pSpec₁ := flockSpec₄ k) (pSpec₂ := roundsSpec E 2 k)
  (SlotDecoder.append (pSpec₁ := flockSpec₃ k) (pSpec₂ := roundsSpec E 2 8)
  (SlotDecoder.append (pSpec₁ := flockSpec₂ k) (pSpec₂ := draw E)
  (SlotDecoder.append (pSpec₁ := draws E (k + 1)) (pSpec₂ := say (Vector E 64))
    (SlotDecoder.draws historyOps.sample (k + 1)) fun _ ↦ single (vecSlot 64))
    fun _ ↦ single historyOps.sample)
    fun t ↦ roundsDec 2 (zcWeights k t) (Thunk.mk fun _ ↦ skipClaimOf k t, 0) 8)
    fun t ↦ roundsDec 2 (zcWeights k t.fst) (zcMid k t) k)
    fun _ ↦ single (vecSlot 2))
    fun _ ↦ single historyOps.sample)
    fun t ↦ roundsDec 2 (fun _ ↦ none) (Thunk.mk fun _ ↦ linClaimOf k t, 0) 8)
    fun _ ↦ single (vecSlot 64))
    fun _ ↦ SlotDecoder.draws historyOps.sample 6

end Flock

/-- The Flock slot: the Flock phase for the region's compressions, or nothing. -/
def flockDec (I : M3Instance) : (o : Option (FlockRegion I.toShape)) →
    SlotDecoder Reading (flockSpecOpt I o)
  | none => SlotDecoder.empty
  | some r => flockDecOf r.kBatch

/-! ## WHIR's opening -/

end DecodeChain

namespace Whir.Ladder

/-- The words a chain of levels commits to after its first: one for each level that has a
successor, the successor's word. -/
def Words : {sh : Whir.Shape} → {κ : ℕ} → Ladder sh κ → Type
  | _, _, .last _ _ => PUnit
  | _, _, @Ladder.cons _ sh' κ' L => WordOf sh' κ' × L.Words

/-- The zero words. -/
def Words.zero : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Words
  | _, _, .last _ _ => ⟨⟩
  | _, _, @Ladder.cons _ _ _ L => (⟨fun _ ↦ Vector.replicate _ 0⟩, Words.zero L)

end Whir.Ladder

namespace DecodeChain

/-- The claim a level's query batch makes: the rows of its word at the positions, each folded at
the fold challenges, batched by the powers of `λ`. -/
def queryClaim {ℓ b t : ℕ} (w : Word ℓ b t) (r : Vector E ℓ) (pos : Fin t → Fin (2 ^ b))
    (lam : E) : E :=
  powerBatch (fun q ↦ foldRow r (w.row (pos q))) lam

/-- A level followed by others, from the running claim and its round polynomial, on its word `w`,
the next level's word `next` given (`whirLevels`): the fold rounds, the residual's polynomial, the
next root, the out-of-domain point, value and polynomial, the nonce, the positions, `λ`, the query
batch's polynomial from the folded rows of `w`, and the rest from the glued claim and polynomial. -/
def levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step} (σ : Thunk E × Thunk (Vector E 3))
    (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    (cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k) :
    SeqDecoder Reading (levelSteps sh sh' κ' k) :=
  (single historyOps.sample, fun t₁ ↦
    let claim₁ : Thunk E := Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁)
    (roundsDec 2 (fun _ ↦ none) (claim₁, 0) sh.lm1, fun t₂ ↦
      let claim₂ := (roundsNext (claim₁, 0) sh.lm1 t₂).1
      let r : Thunk (Vector E sh.ℓ) :=
        Thunk.mk fun _ ↦ toVec sh.ℓ (drawOf t₁ :: roundsChals sh.lm1 t₂)
      (single (polySlot 2 claim₂ (Thunk.pure none)), fun t₃ ↦
        (single ((fun _ ↦ next) <$> historyOps.nextRoot), fun _ ↦
          (SlotDecoder.draws historyOps.sample (Kap sh' κ'), fun _ ↦
            (single historyOps.nextScalar, fun t₆ ↦
              (single (polySlot 2 (Thunk.mk fun _ ↦ msgOf t₆) (Thunk.pure none)), fun t₇ ↦
                (single (historyOps.checkPow queryGrindingBits), fun _ ↦
                  (single (positionsSlot (Kap sh' κ' + sh.R) sh.t), fun t₉ ↦
                    (single historyOps.sample, fun t₁₀ ↦
                      let enforced : Thunk E :=
                        Thunk.mk fun _ ↦ queryClaim w r.get (drawOf t₉) (drawOf t₁₀)
                      (SlotDecoder.empty, fun _ ↦
                        (single (polySlot 2 enforced (Thunk.pure none)), fun t₁₂ ↦
                          (SlotDecoder.empty, fun _ ↦
                            cont (Thunk.mk fun _ ↦
                                powerBatch ![claim₂.get, msgOf t₆, enforced.get] (drawOf t₁₀),
                              Thunk.mk fun _ ↦ batchMessage ![msgOf t₃, msgOf t₇, msgOf t₁₂]
                                (drawOf t₁₀)))))))))))))))

/-- The final level, from the running claim and its round polynomial, on its word `w`
(`whirLevels` at the last level): the fold rounds, the residual's polynomial, the plaintext table,
the nonce, the positions, `λ`, the query batch's polynomial from the folded rows of `w`, and the
tail's rounds from the batched polynomial. -/
def finalDec (sh : Whir.Shape) (nf : ℕ) (σ : Thunk E × Thunk (Vector E 3))
    (w : WordOf sh (nf + 1)) :
    SeqDecoder Reading (finalSteps sh nf) :=
  (single historyOps.sample, fun t₁ ↦
    let claim₁ : Thunk E := Thunk.mk fun _ ↦ RoundPoly.eval σ.2.get (drawOf t₁)
    (roundsDec 2 (fun _ ↦ none) (claim₁, 0) sh.lm1, fun t₂ ↦
      let claim₂ := (roundsNext (claim₁, 0) sh.lm1 t₂).1
      let r : Thunk (Vector E sh.ℓ) :=
        Thunk.mk fun _ ↦ toVec sh.ℓ (drawOf t₁ :: roundsChals sh.lm1 t₂)
      (single (polySlot 2 claim₂ (Thunk.pure none)), fun t₃ ↦
        (single (vecSlot (2 ^ (nf + 1)) : Slot Reading (Tab (nf + 1))), fun _ ↦
          (single (historyOps.checkPow queryGrindingBits), fun _ ↦
            (single (positionsSlot (nf + 1 + sh.R) sh.t), fun t₆ ↦
              (single historyOps.sample, fun t₇ ↦
                let enforced : Thunk E :=
                  Thunk.mk fun _ ↦ queryClaim w r.get (drawOf t₆) (drawOf t₇)
                (SlotDecoder.empty, fun _ ↦
                  (single (polySlot 2 enforced (Thunk.pure none)), fun t₉ ↦
                    let quad : Thunk (Vector E 3) :=
                      Thunk.mk fun _ ↦ batchMessage ![msgOf t₃, msgOf t₉] (drawOf t₇)
                    (SlotDecoder.empty, fun _ ↦
                      (single historyOps.sample, fun t₁₁ ↦
                        (roundsDec 2 (fun _ ↦ none)
                          (Thunk.mk fun _ ↦ RoundPoly.eval quad.get (drawOf t₁₁), 0) nf,
                          fun _ ↦ ⟨⟩))))))))))))

/-- A chain of levels from the running claim and its round polynomial, on the first level's word
and the words of the levels after it. -/
def ladderDec : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    Thunk E × Thunk (Vector E 3) → WordOf sh κ → L.Words → SeqDecoder Reading L.steps
  | _, _, .last sh nf, σ, w, _ => finalDec sh nf σ w
  | _, _, @Ladder.cons sh sh' κ' L, σ, w, ws =>
    levelDec sh sh' κ' σ w ws.1 fun σ' ↦ ladderDec L σ' ws.1 ws.2

/-- WHIR's opening from the opening claim's value: the first round polynomial, then the levels. -/
def whirDec {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (target : Thunk E) (w : WordOf sh κ)
    (ws : L.Words) : SeqDecoder Reading (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps) :=
  (SlotDecoder.empty, fun _ ↦
    (single (polySlot 2 target (Thunk.pure none)), fun t ↦
      ladderDec L (target, Thunk.mk fun _ ↦ msgOf t) w ws))

/-! ## The compiled protocol -/

/-- The words of the compiled protocol on a chain of levels: level 0's `K` word and the word every
later level commits to. -/
structure Words (c : Chain) where
  /-- Level 0's word, the committed one. -/
  level0 : KWord c.sh.ℓ (c.κ + c.sh.R) c.sh.t
  /-- The later levels' words. -/
  later : c.ladder.Words

/-- The zero words. -/
def Words.zero (c : Chain) : Words c := ⟨⟨fun _ ↦ Vector.replicate _ 0⟩, Ladder.Words.zero _⟩

/-- The commitment: the eight announced scalars, which must be `ann`, and the root, read but not
checked against the word `w`. -/
def commitSlot {M : Type} (ann : List E) (w : M) : Slot Reading M := do
  let xs ← historyOps.nextScalars 8
  if xs = ann then (fun _ ↦ w) <$> historyOps.nextRoot else Slot.fail

section Compiled

variable (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)

/-- The statement after the bus phase, from its transcript. -/
def busOutOf (t : (busSpec I).FullTranscript) : I.Stmt × BusOut I :=
  (leanVmPhases I h).bus.front.out input t

/-- The statement after the Flock phase, from the transcript of the front phases. -/
def flockOutOf {sh : Whir.Shape} {κ : ℕ}
    (t : (commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ
      flockSpec I).FullTranscript) : I.Stmt × FlockOut I :=
  let P := leanVmPhases I h
  P.flock.front.out (P.pub.front.out (P.table.front.out (busOutOf I h input t.fst.fst.fst.snd)
    t.fst.fst.snd) t.fst.snd) t.snd

/-- The opening claim's value: the pool's values batched by the powers of `λ`. -/
def targetOf {sh : Whir.Shape} {κ : ℕ} (t : (listBindingFrontSpec I sh κ).FullTranscript) : E :=
  powerBatch (Opening.values I (flockOutOf I h input t.fst.fst)) (t.fst.snd 0)

/-- The front of the compiled protocol: the commitment, the four front phases and the opening's
batching challenge. -/
def frontDec (ann : List E) {sh : Whir.Shape} {κ : ℕ} (w₀ : KWord sh.ℓ (κ + sh.R) sh.t) :
    SlotDecoder Reading (listBindingFrontSpec I sh κ) :=
  ((((((single (pSpec := commitWordSpec sh κ) (commitSlot ann w₀)).append
    fun _ ↦ busDec I).append
    fun t ↦ tableDec I (Thunk.mk fun _ ↦ busOutOf I h input t.snd)).append
    fun _ ↦ pubDec (PublicInput.sentCount I (I.publicLines input))).append
    fun _ ↦ flockDec I I.flock).append
    fun _ ↦ single (pSpec := openingSpec) historyOps.sample).append
    fun _ ↦ SlotDecoder.empty

/-- **The decoder of the compiled protocol** on a chain of levels, at the announcement `ann`, with
the words `W`: the front, then WHIR's opening from the opening claim's value. -/
def compiledDec (ann : List E) (c : Chain) (W : Words c) :
    SlotDecoder Reading (listBindingSpec I c.sh c.κ c.ladder) :=
  (frontDec I h input ann W.level0).append fun t ↦
    (whirDec c.ladder (Thunk.mk fun _ ↦ targetOf I h input t) W.level0.lift W.later).toDecoder

end Compiled

/-! ## Decodability does not depend on the words -/

section Alike

open Slot

/-- A slot reads like itself. -/
theorem agree_self {β : Type} (s : Slot Reading β) : Agree (fun _ _ ↦ True) s s :=
  (Agree.refl s).mono fun _ _ _ ↦ trivial

/-- The failing slots read alike. -/
theorem agree_fail {β γ : Type} :
    Agree (fun _ _ ↦ True) (fail : Slot Reading β) (fail : Slot Reading γ) :=
  ⟨fun _ _ _ h ↦ (nomatch h), fun _ _ _ h ↦ (nomatch h)⟩

/-- Whether a round polynomial decodes depends on its wire alone, not on the claim or the
weight. -/
theorem isSome_decode_eq (d : ℕ) (c c' : E) (e e' : Option E) (w : List E) :
    (RoundPoly.decode d c e w).isSome = (RoundPoly.decode d c' e' w).isSome := by
  by_cases h : 0 < d ∧ w.length = d
  · rw [RoundPoly.isSome_decode h.1 c e h.2, RoundPoly.isSome_decode h.1 c' e' h.2]
  · simp [RoundPoly.decode, h]

/-- Round polynomials read alike, whatever the claims they are rebuilt from. -/
theorem agree_polySlot (d : ℕ) (c c' : Thunk E) (e e' : Thunk (Option E)) :
    Agree (fun _ _ ↦ True) (polySlot d c e) (polySlot d c' e') := by
  refine (Agree.refl (historyOps.nextScalars d)).bind fun w w' hw ↦ ?_
  subst hw
  have hs := isSome_decode_eq d c.get c'.get e.get e'.get w
  cases h₁ : RoundPoly.decode d c.get e.get w <;> cases h₂ : RoundPoly.decode d c'.get e'.get w <;>
    simp only [h₁, h₂, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      Bool.true_eq_false] at hs ⊢
  · exact agree_fail
  · exact Agree.pure trivial

/-- A slot whose value is replaced reads like it. -/
theorem agree_const {β γ δ : Type} (s : Slot Reading β) (x : γ) (y : δ) :
    Agree (fun _ _ ↦ True) ((fun _ ↦ x) <$> s) ((fun _ ↦ y) <$> s) :=
  ⟨((Agree.refl s).1.map _ _).mono fun _ _ _ ↦ trivial,
    ((Agree.refl s).2.map _ _).mono fun _ _ _ ↦ trivial⟩

theorem readsAlike_roundsDec (d : ℕ) (e e' : ℕ → Option E) (σ σ' : Thunk E × ℕ) (m : ℕ) :
    (roundsDec d e σ m).ReadsAlike (roundsDec d e' σ' m) :=
  readsAlike_rounds (fun _ _ ↦ agree_polySlot _ _ _ _ _) (fun _ _ ↦ agree_self _) σ σ' m

theorem readsAlike_layerDec (st st' : GkrState) (ρ m : ℕ) :
    (layerDec st ρ m).ReadsAlike (layerDec st' ρ m) :=
  readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_single (agree_self _))
    fun _ _ ↦ readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦ readsAlike_single (agree_self _))
    fun _ _ ↦ readsAlike_draws (agree_self _) ρ

theorem readsAlike_stepsDec : ∀ (st st' : GkrState) (k m : ℕ),
    (stepsDec st k m).ReadsAlike (stepsDec st' k m)
  | _, _, 0, _ => readsAlike_empty
  | st, st', k + 1, m => readsAlike_append (readsAlike_layerDec st st' 2 m) fun _ _ ↦
      readsAlike_stepsDec _ _ k (m + 2)

theorem readsAlike_oddDec (st st' : GkrState) : ∀ r, (oddDec st r).ReadsAlike (oddDec st' r)
  | 0 => readsAlike_empty
  | _ + 1 => readsAlike_layerDec st st' 1 0

theorem readsAlike_gkrDec (st st' : GkrState) (μ : ℕ) :
    (gkrDec st μ).ReadsAlike (gkrDec st' μ) :=
  readsAlike_append (readsAlike_append (readsAlike_oddDec st st' _) fun _ _ ↦
    readsAlike_stepsDec _ _ _ _) fun _ _ ↦ readsAlike_single (agree_self _)

theorem readsAlike_busDec (I : M3Instance) : (busDec I).ReadsAlike (busDec I) :=
  readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_single (agree_self _))
    fun _ _ ↦ readsAlike_single (agree_self _)) fun _ _ ↦ readsAlike_gkrDec _ _ _)
    fun _ _ ↦ readsAlike_single (agree_self _)

theorem readsAlike_tableDec (I : M3Instance) (s s' : Thunk (I.Stmt × BusOut I)) :
    (tableDec I s).ReadsAlike (tableDec I s') :=
  readsAlike_append (readsAlike_append (readsAlike_single (agree_self _)) fun _ _ ↦
    readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦ readsAlike_single (agree_self _)

theorem readsAlike_pubDec (n : ℕ) : (pubDec n).ReadsAlike (pubDec n) := by
  rintro ⟨_ | _ | k, hk⟩ _ _
  · exact agree_self _
  · exact agree_self _
  · exact absurd hk (by omega)

theorem readsAlike_flockDecOf (k : ℕ) : (flockDecOf k).ReadsAlike (flockDecOf k) := by
  unfold flockDecOf
  refine readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_append
    (readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_append
    (readsAlike_draws (agree_self _) _) fun _ _ ↦ readsAlike_single (agree_self _))
    fun _ _ ↦ readsAlike_single (agree_self _)) fun _ _ ↦ readsAlike_roundsDec _ _ _ _ _ _)
    fun _ _ ↦ readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦ readsAlike_single (agree_self _))
    fun _ _ ↦ readsAlike_single (agree_self _)) fun _ _ ↦ readsAlike_roundsDec _ _ _ _ _ _)
    fun _ _ ↦ readsAlike_single (agree_self _)) fun _ _ ↦ readsAlike_draws (agree_self _) _

theorem readsAlike_flockDec (I : M3Instance) :
    ∀ o, (flockDec I o).ReadsAlike (flockDec I o)
  | none => readsAlike_empty
  | some r => readsAlike_flockDecOf r.kBatch

theorem readsAlike_levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ σ' : Thunk E × Thunk (Vector E 3))
    (w w' : WordOf sh (Kap sh' κ')) (next next' : WordOf sh' κ')
    {cont cont' : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k}
    (hc : ∀ a b, (cont a).ReadsAlike (cont' b)) :
    (levelDec sh sh' κ' σ w next cont).ReadsAlike (levelDec sh sh' κ' σ' w' next' cont') :=
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
  .cons (readsAlike_single (agree_const _ _ _)) fun _ _ ↦
  .cons (readsAlike_draws (agree_self _) _) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons readsAlike_empty fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
  .cons readsAlike_empty fun _ _ ↦ hc _ _

theorem readsAlike_finalDec (sh : Whir.Shape) (nf : ℕ) (σ σ' : Thunk E × Thunk (Vector E 3))
    (w w' : WordOf sh (nf + 1)) : (finalDec sh nf σ w).ReadsAlike (finalDec sh nf σ' w') :=
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons readsAlike_empty fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
  .cons readsAlike_empty fun _ _ ↦
  .cons (readsAlike_single (agree_self _)) fun _ _ ↦
  .cons (readsAlike_roundsDec _ _ _ _ _ _) fun _ _ ↦ .nil

theorem readsAlike_ladderDec : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (σ σ' : Thunk E × Thunk (Vector E 3)) (w w' : WordOf sh κ) (ws ws' : L.Words),
    (ladderDec L σ w ws).ReadsAlike (ladderDec L σ' w' ws')
  | _, _, .last sh nf, σ, σ', w, w', _, _ => readsAlike_finalDec sh nf σ σ' w w'
  | _, _, @Ladder.cons sh sh' κ' L, σ, σ', w, w', ws, ws' =>
    readsAlike_levelDec sh sh' κ' σ σ' w w' ws.1 ws'.1 fun a b ↦
      readsAlike_ladderDec L a b ws.1 ws'.1 ws.2 ws'.2

theorem readsAlike_whirDec {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (target target' : Thunk E)
    (w w' : WordOf sh κ) (ws ws' : L.Words) :
    (whirDec L target w ws).ReadsAlike (whirDec L target' w' ws') :=
  .cons readsAlike_empty fun _ _ ↦
  .cons (readsAlike_single (agree_polySlot _ _ _ _ _)) fun _ _ ↦
    readsAlike_ladderDec L _ _ w w' ws ws'

theorem agree_commitSlot {M : Type} (ann : List E) (w w' : M) :
    Agree (fun _ _ ↦ True) (commitSlot ann w) (commitSlot ann w') := by
  refine (Agree.refl (historyOps.nextScalars 8)).bind fun xs xs' hx ↦ ?_
  subst hx
  by_cases h : xs = ann
  · simp only [h, ↓reduceIte]
    exact agree_const _ _ _
  · simp only [h, ↓reduceIte]
    exact agree_fail

/-- **The decoder reads alike at any two word suppliers.** -/
theorem readsAlike_compiledDec (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)
    (ann : List E) (c : Chain) (W W' : Words c) :
    (compiledDec I h input ann c W).ReadsAlike (compiledDec I h input ann c W') :=
  readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_append (readsAlike_append
    (readsAlike_append (readsAlike_append (readsAlike_single (agree_commitSlot _ _ _))
    fun _ _ ↦ readsAlike_busDec I) fun _ _ ↦ readsAlike_tableDec I _ _)
    fun _ _ ↦ readsAlike_pubDec _) fun _ _ ↦ readsAlike_flockDec I _)
    fun _ _ ↦ readsAlike_single (agree_self _)) fun _ _ ↦ readsAlike_empty)
    fun _ _ ↦ (readsAlike_whirDec _ _ _ _ _ _ _).toDecoder

end Alike

/-! ## At leanVM -/

section Deployed

variable (prog : Program) (input : PublicInput) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- The words of the compiled protocol at leanVM's chain. -/
abbrev LeanWords : Type := Words (leanIsaChain prog s hs ρ hρ)

/-- **The decoder of leanVM's chain history** at the announced sizes and rate: the compiled
protocol of the leanISA instance at WHIR's deployed chain, the announcement read first. -/
def decoder (W : LeanWords prog s hs ρ hρ) :
    SlotDecoder Reading (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ) :=
  compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input (announcement s ρ)
    (leanIsaChain prog s hs ρ hρ) W

/-- The longest prefix of the compiled transcript that a chain history reads exactly. -/
def decodePrefix (W : LeanWords prog s hs ρ hρ) (hist : List Reading) :
    Option (Σ i, (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).Transcript i) :=
  (decoder prog input s hs ρ hρ W).decodePrefix hist

/-- The full compiled transcript, if a chain history reads exactly it. -/
def decode (W : LeanWords prog s hs ρ hρ) (hist : List Reading) :
    Option (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).FullTranscript :=
  (decoder prog input s hs ρ hρ W).decode hist

/-- **Decodability does not depend on the words**: a chain history decodes, and to the same number
of rounds, whatever words fill the oracle messages. -/
theorem decodePrefix_isSome_indep (W W' : LeanWords prog s hs ρ hρ) (hist : List Reading) :
    (decodePrefix prog input s hs ρ hρ W hist).map Sigma.fst =
      (decodePrefix prog input s hs ρ hρ W' hist).map Sigma.fst := by
  unfold decodePrefix decoder
  exact (readsAlike_compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input
    (announcement s ρ) (leanIsaChain prog s hs ρ hρ) W W').decodePrefix hist

/-- In particular, whether a history decodes does not depend on the words. -/
theorem isSome_decodePrefix_indep (W W' : LeanWords prog s hs ρ hρ) (hist : List Reading) :
    (decodePrefix prog input s hs ρ hρ W hist).isSome =
      (decodePrefix prog input s hs ρ hρ W' hist).isSome := by
  unfold decodePrefix decoder
  exact (readsAlike_compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input
    (announcement s ρ) (leanIsaChain prog s hs ρ hρ) W W').isSome_decodePrefix hist

end Deployed

end DecodeChain

end

end LeanerVM.Protocol
