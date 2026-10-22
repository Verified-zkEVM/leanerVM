/-
  LeanerVM.Protocol.ListBinding

  The list-binding compilation: the oracle protocol with the committed stack replaced by WHIR's
  level-0 word, list-decoded by its extractor, and the opening's query replaced by WHIR's
  opening; its round-by-round knowledge soundness and its perfect completeness.
-/

module

public import LeanerVM.Protocol.Spine.Compose
public import LeanerVM.Protocol.Opening
public import LeanerVM.Protocol.Whir.OpenSound
public import LeanerVM.Protocol.Whir.Decode
public import LeanerVM.Protocol.ToArkLib.Relist
public import LeanerVM.Protocol.ToArkLib.SendEncoded
public import LeanerVM.Protocol.ToArkLib.MapOracles

/-!
# List binding

Category B: Annex B, `def:listbinding` and `thm:rbr`, with §8.5 of the specification
(`doc/leanvm/body/08-end-to-end-protocol.tex:94-101`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

The oracle protocol of the spine commits the stack itself and asks it one weighted question at
the end. The compiled protocol commits the stack's level-0 word instead: a word of `K` symbols
(`KWord`), which a cheating prover need not make a codeword. WHIR's opening is list binding: what
it establishes is the list relation `relOpen`, "some interleaved codeword within the threshold `a`
of the word satisfies the claim". The compilation turns that into extraction.

* `commitWord`: the prover sends the word of its stack (`kwordOf`). Its extractor list-decodes the
  word with a `ListDecoder` and selects the first member whose stack satisfies `M3Holds`, which is
  decidable (`commitPick`); its output relation is "some member of the list satisfies `M3Holds`".
* The front phases and the opening's batching run unchanged over the word, relisted
  (`Component.Front.relist`): the relation of a phase over the stack becomes "some stack in the list
  of the word is related", and each challenge pays the list bound `L₀` of level 0 times its error.
  The phases are front (`Phase.FrontDef`), which is what makes this possible: their verifiers never
  read the stack.
* `openInput`: the batched claim, the word and the stack read by WHIR's opening: the weight at the
  stack's height, the word's `K` symbols in `E`, the stack's table in `E`. Its security is the seam
  between the relisted batching and WHIR (`relist_of_relOpen`): a codeword of the list relation is
  a member of the decoder's list (`ListDecoder.mem_iff`, at level 0's threshold), its messages are
  `K`-valued since the word is (`isInK_of_cl`), so it is a stack, and its claim is the batched
  claim on that stack (`pair_relayoutWeight`).
* `listBinding_compile`: the security of the whole, `commitWord ⟫ fronts ⟫ batch ⟫ openInput ⟫
  whirOpen`, from `M3Rel I` to acceptance, at `L₀` times the oracle protocol's errors on its
  challenges and WHIR's own errors on WHIR's (`listBindingError`); its extractor is the
  composition of the components', and the stack it extracts at the commit round is the decoded
  member that satisfies `M3Holds`.

`listBinding_perfectCompleteness` is the other half: on every statement and stack with
`M3Holds`, the honest prover, which commits the honest word of its stack (`kwordOf`), convinces the
compiled verifier with probability one. Each phase's completeness carries over to the phase over the
word (`Component.Front.overComplete`) at its seam read on the honest word (`honestRel`), and WHIR's
opening receives the honest word of the stack in `E` (`kwordOf_lift`) and its weighted claim.

The decoder is an interface: `ListDecoder κ R a ℓ` is specified by the list relation at the
threshold `a`, which is level 0's `Par.a` by the type of `listBinding_compile`, so a decoder meets
WHIR's list relation by its specification and nothing else of it is trusted. The phases' and WHIR's
proofs are arguments: the theorem holds for every bundle of phases with its security and every
chain of WHIR levels with its parameters.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec Whir
  StepSchedule
open scoped NNReal

@[expose] public section

/-! ## The level-0 word -/

namespace Whir

/-- A word with `K` symbols on `2 ^ b` positions with `2 ^ ℓ` lanes, read `t` positions at a time:
the level-0 word the commitment binds. -/
structure KWord (ℓ b t : ℕ) where
  /-- The row at a position. -/
  row : Fin (2 ^ b) → Vector K (2 ^ ℓ)

/-- The `K` word read in `E`. -/
def KWord.lift {ℓ b t : ℕ} (w : KWord ℓ b t) : Word ℓ b t := ⟨fun y ↦ (w.row y).map ofK⟩

/-- A question to a `K` word is `t` positions; the answer is their rows, read in `E`. -/
instance (ℓ b t : ℕ) : OracleInterface (KWord ℓ b t) where
  Query := Fin t → Fin (2 ^ b)
  toOC :=
    { spec := (Fin t → Fin (2 ^ b)) →ₒ (Fin t → Vector E (2 ^ ℓ))
      impl := fun q ↦ do
        let w ← read
        return fun k ↦ (KWord.lift w).row (q k) }

/-- The lanes of a `K` word read in `E` are in `K`. -/
theorem KWord.isInK_lanes {ℓ b t : ℕ} (w : KWord ℓ b t) (y : Fin (2 ^ b)) (u : Fin (2 ^ ℓ)) :
    IsInK (w.lift.lanes y u) := by
  have h : w.lift.lanes y u = ofK (w.row y)[u] := by
    simp [Word.lanes, KWord.lift, Vector.getD, u.2]
  rw [h]
  exact (isInK_iff _).mpr ⟨_, rfl⟩

/-- The honest `K` word of a stack table: the encodings over `K` of its lanes, the top
coordinates. -/
def kwordOf (ℓ κ R t : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) : KWord ℓ (κ + R) t :=
  ⟨fun y ↦ Vector.ofFn fun u ↦ encode (RingHom.id K) κ R (sliceLow (relayout q) u) y⟩

/-- Relaying out commutes with mapping the entries. -/
private theorem relayout_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {κ ℓ : ℕ}
    (q : CMlPolynomialEval R (κ + ℓ)) :
    relayout (CMlPolynomialEval.map φ q) = CMlPolynomialEval.map φ (relayout q) := by
  apply Vector.ext
  intro i hi
  simp [relayout, CMlPolynomialEval.map]

/-- The honest `K` word of a stack, read in `E`, is the honest word of the stack in `E`. -/
theorem kwordOf_lift (ℓ κ R t : ℕ) (q : CMlPolynomialEval K (κ + ℓ)) :
    (kwordOf ℓ κ R t q).lift =
      wordOf ℓ κ R t (relayout (CMlPolynomialEval.map (algebraMap K E) q)) := by
  unfold KWord.lift kwordOf wordOf
  congr 1
  funext y
  apply Vector.ext
  intro u hu
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rw [← encode_ofK, relayout_map, sliceLow_map]

/-- The level-0 oracle: the `K` word of a level of shape `sh`. -/
abbrev KOracle (sh : Shape) (κ : ℕ) : Fin 1 → Type := OneOracle (KWord sh.ℓ (κ + sh.R) sh.t)

end Whir

/-! ## Stacks of codewords -/

section Stacks

variable (I : M3Instance) {sh : Whir.Shape} {κ : ℕ}

/-- The stack of an interleaved codeword at the instance's height: the lanes on top (the inverse
of the relayout) and the `K` limb of every symbol. -/
def stackOfMsgs (hμ : κ + sh.ℓ = I.μ) (g : Msgs sh.ℓ κ) : Column I.μ :=
  ⟨hμ ▸ (Vector.map (fun x : E ↦ x.limb 0)
    (relayout (κ := sh.ℓ) (ℓ := κ) (ofLanes g) : Vector E (2 ^ (κ + sh.ℓ))) :
      CMlPolynomialEval K (κ + sh.ℓ))⟩

/-- The stacks of the list of a word: the decoder's list of its lanes, each codeword as a
stack. -/
def stackList {a : ℕ} (D : ListDecoder κ sh.R a sh.ℓ) (hμ : κ + sh.ℓ = I.μ)
    (o : ∀ i, KOracle sh κ i) : List (∀ i, TheOracle I i) :=
  (D.decode (o 0).lift.lanes).map fun g _ ↦ stackOfMsgs I hμ g

/-- The list has at most `L` stacks, for a list bound `L` at the decoder's threshold. -/
theorem length_stackList {a L : ℕ} (D : ListDecoder κ sh.R a sh.ℓ) (hμ : κ + sh.ℓ = I.μ)
    (hL : ListBound κ sh.R a sh.ℓ L) (o : ∀ i, KOracle sh κ i) :
    (stackList I D hμ o).length ≤ L := by
  rw [stackList, List.length_map]
  exact D.length_le hL _

end Stacks

/-! ## The commitment -/

section Commit

variable (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} {a : ℕ} (D : ListDecoder κ sh.R a sh.ℓ)
  (hμ : κ + sh.ℓ = I.μ)

/-- The commitment of the level-0 word: the prover sends the `K` word of its stack. -/
def commitWord : Component.Def I.Stmt NoOracle (Column I.μ) I.Stmt (KOracle sh κ) (Column I.μ)
    (Component.sendSpec (KWord sh.ℓ (κ + sh.R) sh.t)) :=
  Component.sendEncoded I.Stmt (KWord sh.ℓ (κ + sh.R) sh.t) (Column I.μ) fun q ↦
    kwordOf sh.ℓ κ sh.R sh.t (hμ.symm ▸ q.values)

/-- The commitment's extractor: the first stack of the word's list that satisfies `M3Holds`. -/
def commitPick (s : I.Stmt) (w : KWord sh.ℓ (κ + sh.R) sh.t) : Option (Column I.μ) :=
  ((stackList I D hμ fun _ ↦ w).find? fun q ↦ decide (M3Holds I s (q 0))).map (· 0)

/-- **The commitment's security**, at error zero: from `M3Rel I` to "some stack of the word's list
satisfies `M3Holds`", with the extractor that list-decodes the word and picks the first stack of
the list satisfying `M3Holds`. -/
def commitWordSecurity :
    Component.Security (commitWord I hμ) (M3Rel I)
      (Component.relistRel (stackList I D hμ) (Seam.commit I)) (fun _ ↦ 0) :=
  Component.sendEncodedSecurity (commitPick I D hμ) fun s w _ h ↦ by
    obtain ⟨q, hq, _, hholds⟩ := h
    have hsome : ((stackList I D hμ fun _ ↦ w).find? fun q ↦ decide (M3Holds I s (q 0))).isSome :=
      List.find?_isSome.mpr ⟨q, hq, decide_eq_true hholds⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨r 0, by simp [commitPick, hr], fun _ ↦ ?_⟩
    have h1 := List.find?_some hr
    simp only [decide_eq_true_eq] at h1
    exact h1

end Commit

/-! ## The phases over the word -/

section Over

variable (I : M3Instance) {ι' : Type} (O' : ι' → Type) [∀ i, OracleInterface (O' i)]
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]

/-- A front phase over other oracles: its verifier unchanged, its prover run on the stack the
witness holds. -/
def Phase.FrontDef.over (Pf : Phase.FrontDef I StmtIn StmtOut pSpec) :
    Component.Def StmtIn O' (Column I.μ) StmtOut O' (Column I.μ) pSpec :=
  Pf.front.over (fun _ ↦ ⟨Vector.replicate _ 0⟩)
    (Component.proverVia Pf.toDef.red.prover fun q ↦ (fun _ ↦ q, ()))

/-- Its security through a list of stacks of at most `L` values, at `L` times the phase's error. -/
@[macro_inline]
def Phase.Security.relist {Pf : Phase.FrontDef I StmtIn StmtOut pSpec}
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (Sf : Phase.Security I Pf.toDef relIn relOut ε) (list : (∀ i, O' i) → List (∀ i, TheOracle I i))
    (L : ℕ) (hL : ∀ o, (list o).length ≤ L) :
    Component.Security (Pf.over I O') (Component.relistRel list relIn)
      (Component.relistRel list relOut) (fun i ↦ L • ε i) :=
  Component.Front.relist Pf.front (Pf.front.overFront _ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) list Sf
    L hL

/-- The opening's batching over other oracles, the stack the witness. -/
abbrev openingBatchOver : Component.Def (I.Stmt × FlockOut I) O' (Column I.μ) (WeightedClaim I) O'
    (Column I.μ) (draw E) :=
  Component.batch O' E (Opening.values I) (Opening.batched I)

/-- The opening's batching over the stack, at the opening's error. -/
def openingBatchSecurity :
    Component.Security (Component.batch (TheOracle I) E (Opening.values I) (Opening.batched I))
      (Seam.flock I) (Opening.BatchedHolds I) (openingError I) :=
  Component.Security.mono
    (fun _ ↦ le_of_eq (by rw [drawError, openingError, drawError, overE,
      Nat.card_eq_fintype_card]))
    (Component.batchSecurity (TheOracle I) E (Opening.values I) (Opening.batched I)
      (Opening.answers_of_not_flock I))

/-- The batching over other oracles, through a list of stacks of at most `L` values, at `L` times
the opening's error. -/
@[macro_inline]
def openingBatchOverSecurity (list : (∀ i, O' i) → List (∀ i, TheOracle I i)) (L : ℕ)
    (hL : ∀ o, (list o).length ≤ L) :
    Component.Security (openingBatchOver I O') (Component.relistRel list (Seam.flock I))
      (Component.relistRel list (Opening.BatchedHolds I)) (fun i ↦ L • openingError I i) :=
  Component.Front.relist (Component.sampleFront (TheOracle I) E (W := Unit) _ _)
    (Component.sampleFront O' E (W := Column I.μ) _ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) list
    (openingBatchSecurity I) L hL

end Over

/-! ## The opening's input -/

section Input

variable (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (hμ : κ + sh.ℓ = I.μ)

/-- The level-0 word read in `E`, each question answered by the same question. -/
def kwordMap : Component.OracleMap (KOracle sh κ) (OneW sh κ) where
  map := fun o _ ↦ (o 0).lift
  query := fun q ↦ ⟨q.1, q.2⟩
  answer := fun _ a ↦ a
  answer_eq := fun _ q ↦ by
    obtain ⟨i, q⟩ := q
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl

/-- What WHIR's opening reads: the batched claim's weight at the stack's height and its value,
the word read in `E`, and the stack read in `E`. -/
def openInput : Component.Def (WeightedClaim I) (KOracle sh κ) (Column I.μ)
    (Weight E (κ + sh.ℓ) × E) (OneW sh κ) (Tab (κ + sh.ℓ)) !p[] :=
  Component.mapOracles (KOracle sh κ) (OneW sh κ) (fun c ↦ (hμ.symm ▸ c.weight, c.value))
    (fun q ↦ CMlPolynomialEval.map (algebraMap K E) (hμ.symm ▸ q.values)) (kwordMap (sh := sh))

/-- The weighted claim of a weight against a table carried along an equality of heights. -/
private theorem pair_cast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ}
    (h : m = n) (W : Weight S n) (t : CMlPolynomialEval R m) :
    W.pair φ (h ▸ t) = (h.symm ▸ W).pair φ t := by
  subst h
  rfl

/-- The relayout undone. -/
private theorem relayout_relayout {S : Type} {ℓ κ : ℕ} (t : CMlPolynomialEval S (ℓ + κ)) :
    relayout (κ := κ) (ℓ := ℓ) (relayout (κ := ℓ) (ℓ := κ) t) = t := by
  have key : ∀ j : Fin (2 ^ (ℓ + κ)),
      (relayout (κ := κ) (ℓ := ℓ) (relayout (κ := ℓ) (ℓ := κ) t))[j] = t[j] := fun j ↦ by
    obtain ⟨⟨u, x⟩, rfl⟩ := (cubeSplit ℓ κ).surjective j
    rw [cubeSplit_apply, relayout_getElem, relayout_getElem]
  exact Vector.ext fun i hi ↦ key ⟨i, hi⟩

/-- **The seam between the relisted batching and WHIR's opening.** A statement in WHIR's list
relation at level 0's threshold, read off a batched claim and a `K` word, has a stack in the word's
list on which the batched claim holds: the codeword is a member of the decoder's list, its messages
are `K`-valued since the word is, and its claim is the batched claim on its stack. -/
theorem relist_of_relOpen (P : Par sh κ) (D : ListDecoder κ sh.R P.a sh.ℓ) (c : WeightedClaim I)
    (o : ∀ i, KOracle sh κ i)
    (h : OpenLang P (hμ.symm ▸ c.weight) c.value fun _ ↦ (o 0).lift) :
    ∃ q ∈ stackList I D hμ o, c.Holds (theStack q) := by
  rcases h with ⟨g, hCl, hclaim⟩ | hfold
  · refine ⟨fun _ ↦ stackOfMsgs I hμ g, List.mem_map.mpr ⟨g, (D.mem_iff _ g).mpr hCl, rfl⟩, ?_⟩
    have hK := isInK_of_cl P.hdist P.hb (KWord.isInK_lanes (o 0)) hCl
    rw [claim_zero, ← relayout_relayout (ofLanes g), pair_relayoutWeight] at hclaim
    show c.weight.pair (algebraMap K E) (hμ ▸ _) = c.value
    rw [pair_cast]
    refine Eq.trans ?_ hclaim
    unfold Weight.pair
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    obtain ⟨⟨x, u⟩, rfl⟩ := (cubeSplit κ sh.ℓ).surjective j
    obtain ⟨b, hb⟩ := (isInK_iff _).mp (hK u x)
    have hT : (relayout (κ := sh.ℓ) (ℓ := κ) (ofLanes g))[cubeSplit κ sh.ℓ (x, u)] = ofK b := by
      rw [← hb]
      simp only [cubeSplit_apply, relayout_getElem, ofLanes_getElem]
    have hT' : (relayout (κ := sh.ℓ) (ℓ := κ) (ofLanes g))[(cubeSplit κ sh.ℓ (x, u)).val] =
        ofK b := by
      simpa only [Fin.getElem_fin] using hT
    simp only [Fin.getElem_fin, Vector.getElem_map, RingHom.id_apply, hT', limb_ofK]
    rfl
  · exact absurd (foldOK_nil κ sh.R P.a sh.ℓ _) hfold

/-- The security of the opening's input, at the empty error: from the relisted batched claim to
WHIR's list relation at level 0's threshold, the stack read back from the table. -/
def openInputSecurity (P : Par sh κ) (D : ListDecoder κ sh.R P.a sh.ℓ) :
    Component.Security (openInput I hμ) (Component.relistRel (stackList I D hμ)
      (Opening.BatchedHolds I)) (relOpen P) (fun i ↦ Fin.elim0 i.1) :=
  Component.mapOraclesSecurity (KOracle sh κ) (OneW sh κ) _ _ _
    (fun t ↦ ⟨hμ ▸ (Vector.map (fun x : E ↦ x.limb 0) (t : Vector E (2 ^ (κ + sh.ℓ))) :
      CMlPolynomialEval K (κ + sh.ℓ))⟩) fun c o _ h ↦ by
    obtain ⟨q, hq, hc⟩ := relist_of_relOpen I hμ P D c o h
    exact ⟨q, hq, (), hc⟩

end Input

/-! ## The compiled protocol -/

section Instances

variable (I : M3Instance) (sh : Whir.Shape) (κ : ℕ)

/-- The commitment's schedule: one message, the level-0 word. -/
abbrev commitWordSpec : ProtocolSpec 1 := Component.sendSpec (KWord sh.ℓ (κ + sh.R) sh.t)

/-! The instances of the compiled schedule's prefixes, which the composition meets one append at
a time. -/

instance instOracleInterfaceWordBus :
    ∀ i, OracleInterface ((commitWordSpec sh κ ++ₚ busSpec I).Message i) :=
  msgAppend inferInstance (instOracleInterfaceBus I)

instance instSampleableTypeWordBus :
    ∀ i, SampleableType ((commitWordSpec sh κ ++ₚ busSpec I).Challenge i) :=
  chalAppend inferInstance (instSampleableTypeBus I)

instance instOracleInterfaceWordTable :
    ∀ i, OracleInterface ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I).Message i) :=
  msgAppend (instOracleInterfaceWordBus I sh κ) (instOracleInterfaceTable I)

instance instSampleableTypeWordTable :
    ∀ i, SampleableType ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I).Challenge i) :=
  chalAppend (instSampleableTypeWordBus I sh κ) (instSampleableTypeTable I)

instance instOracleInterfaceWordPub :
    ∀ i, OracleInterface
      ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec).Message i) :=
  msgAppend (instOracleInterfaceWordTable I sh κ) instOracleInterfacePub

instance instSampleableTypeWordPub :
    ∀ i, SampleableType
      ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec).Challenge i) :=
  chalAppend (instSampleableTypeWordTable I sh κ) instSampleableTypePub

instance instOracleInterfaceWordFlock :
    ∀ i, OracleInterface
      ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I).Message i) :=
  msgAppend (instOracleInterfaceWordPub I sh κ) (instOracleInterfaceFlock I)

instance instSampleableTypeWordFlock :
    ∀ i, SampleableType
      ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ
        flockSpec I).Challenge i) :=
  chalAppend (instSampleableTypeWordPub I sh κ) (instSampleableTypeFlock I)

/-- The schedule of the compiled protocol before WHIR's opening. -/
abbrev listBindingFrontSpec :
    ProtocolSpec (1 + busRounds I + tableRounds I + 2 + flockRounds I I.flock + 1 + 0) :=
  commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I ++ₚ openingSpec ++ₚ
    !p[]

instance instOracleInterfaceWordBatch :
    ∀ i, OracleInterface ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ
      flockSpec I ++ₚ openingSpec).Message i) :=
  msgAppend (instOracleInterfaceWordFlock I sh κ) (instOracleInterfaceDraw E)

instance instSampleableTypeWordBatch :
    ∀ i, SampleableType ((commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ
      flockSpec I ++ₚ openingSpec).Challenge i) :=
  chalAppend (instSampleableTypeWordFlock I sh κ) (instSampleableTypeDraw E)

instance instOracleInterfaceFront :
    ∀ i, OracleInterface ((listBindingFrontSpec I sh κ).Message i) :=
  msgAppend (instOracleInterfaceWordBatch I sh κ) inferInstance

instance instSampleableTypeFront :
    ∀ i, SampleableType ((listBindingFrontSpec I sh κ).Challenge i) :=
  chalAppend (instSampleableTypeWordBatch I sh κ) inferInstance

/-- The schedule of the compiled protocol: the front, then WHIR's opening of the chain `L`. -/
abbrev listBindingSpec (L : Ladder sh κ) :=
  listBindingFrontSpec I sh κ ++ₚ seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)

instance instOracleInterfaceListBinding (L : Ladder sh κ) :
    ∀ i, OracleInterface ((listBindingSpec I sh κ L).Message i) :=
  msgAppend (instOracleInterfaceFront I sh κ) (instOracleInterfaceSeq _)

instance instSampleableTypeListBinding (L : Ladder sh κ) :
    ∀ i, SampleableType ((listBindingSpec I sh κ L).Challenge i) :=
  chalAppend (instSampleableTypeFront I sh κ) (instSampleableTypeSeq _)

end Instances

section Compile

variable {I : M3Instance} {sh : Whir.Shape} {κ : ℕ}

/-- **The list-binding compilation** of a bundle of phases: the commitment of the level-0 word,
the four front phases and the opening's batching over it, the opening's input and WHIR's opening of
the chain `L`. -/
def listBindingDef (P : Phases I) (hμ : κ + sh.ℓ = I.μ) (L : Ladder sh κ) :
    Component.Def I.Stmt NoOracle (Column I.μ) Unit (OneW L.finShape L.finN) Unit
      (listBindingSpec I sh κ L) :=
  (((((((commitWord I hμ).append (P.bus.over I (KOracle sh κ))).append
    (P.table.over I (KOracle sh κ))).append (P.pub.over I (KOracle sh κ))).append
    (P.flock.over I (KOracle sh κ))).append (openingBatchOver I (KOracle sh κ))).append
    (openInput I hμ)).append (whirOpen sh κ L)

/-- Its errors: none on the commitment; `L₀` times the spine's error on each challenge of the four
front phases and the batching, `L₀` the list bound of level 0; none on the opening's input; WHIR's
errors on WHIR's challenges. -/
noncomputable def listBindingError (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (ps : L.Pars) : (listBindingSpec I sh κ L).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (errAppend
    (fun _ ↦ 0 : (Component.sendSpec (KWord sh.ℓ (κ + sh.R) sh.t)).ChallengeIdx → ℝ≥0)
    (fun i ↦ (L.headPar ps).L • busError I i)) (fun i ↦ (L.headPar ps).L • tableError I i))
    (fun i ↦ (L.headPar ps).L • pubError i)) (fun i ↦ (L.headPar ps).L • flockError I i))
    (fun i ↦ (L.headPar ps).L • openingError I i))
    (fun i ↦ Fin.elim0 i.1 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) (openErr L ps)

/-- **The list-binding compilation is round-by-round knowledge sound** from `M3Rel I` to
acceptance at `listBindingError`: `L₀` times the oracle protocol's errors on its challenges and
WHIR's errors on WHIR's, for every bundle of phases with its security, every chain of WHIR levels
with its parameters and every list decoder at level 0's threshold. The extractor list-decodes the
committed word and picks the stack that satisfies `M3Holds`; the state function, before WHIR, is
"some stack of the word's list satisfies the phase's state function". Inlined before compilation,
so the errors never reach compiled code and the extractor computes. -/
@[macro_inline]
def listBinding_compile (P : Phases I) (S : P.Security) (hμ : κ + sh.ℓ = I.μ) (L : Ladder sh κ)
    (ps : L.Pars) (D : ListDecoder κ sh.R (L.headPar ps).a sh.ℓ) :
    Component.Security (listBindingDef P hμ L) (M3Rel I) Set.univ (listBindingError I L ps) :=
  have hL := length_stackList I D hμ (L.headPar ps).hlist
  (((((((commitWordSecurity I D hμ).append (S.bus.relist I _ _ _ hL)).append
    (S.table.relist I _ _ _ hL)).append (S.pub.relist I _ _ _ hL)).append
    (S.flock.relist I _ _ _ hL)).append (openingBatchOverSecurity I _ _ _ hL)).append
    (openInputSecurity I hμ (L.headPar ps) D)).append (whirOpen_rbrSoundness L ps)

/-- The same as a statement about the compiled verifier: round-by-round knowledge soundness at
`listBindingError`, for the extractor and the state function of `listBinding_compile`. -/
theorem listBinding_rbrKnowledgeSoundness (P : Phases I) (S : P.Security) (hμ : κ + sh.ℓ = I.μ)
    (L : Ladder sh κ) (ps : L.Pars) (D : ListDecoder κ sh.R (L.headPar ps).a sh.ℓ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef P hμ L).red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (M3Rel I) Set.univ (listBinding_compile P S hμ L ps D).witMid
      (listBinding_compile P S hμ L ps D).extractor
      ((listBinding_compile P S hμ L ps D).kSF init impl) (listBindingError I L ps) :=
  (listBinding_compile P S hμ L ps D).rbr init impl

end Compile

/-! ## Completeness -/

section Complete

variable (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (hμ : κ + sh.ℓ = I.μ)

/-- The word is the honest word of the stack the witness holds. -/
def HonestWord (o : ∀ i, KOracle sh κ i) (q : Column I.μ) : Prop :=
  o 0 = kwordOf sh.ℓ κ sh.R sh.t (hμ.symm ▸ q.values)

/-- A seam read on the honest word: the word is the honest word of the witness stack, and the
seam holds of that stack. -/
abbrev honestRel {S : Type} (rel : Set ((S × ∀ i, TheOracle I i) × Unit)) :
    Set ((S × ∀ i, KOracle sh κ i) × Column I.μ) :=
  Component.viaRel (HonestWord I hμ) (fun q _ ↦ q) rel

/-- The commitment's completeness: it sends the honest word of a stack with `M3Holds`. -/
def commitWordComplete :
    Component.Complete (commitWord I hμ) (M3Rel I) (honestRel I hμ (Seam.commit I)) :=
  Component.sendEncodedComplete fun _ _ _ h ↦ ⟨rfl, h⟩

/-- A front phase's completeness over the word, at its seams read on the honest word. -/
def Phase.Complete.over {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
    {Pf : Phase.FrontDef I StmtIn StmtOut pSpec}
    {relIn : Set ((StmtIn × ∀ i, TheOracle I i) × Unit)}
    {relOut : Set ((StmtOut × ∀ i, TheOracle I i) × Unit)}
    (C : Phase.Complete I Pf.toDef relIn relOut) :
    Component.Complete (Pf.over I (KOracle sh κ)) (honestRel I hμ relIn) (honestRel I hμ relOut) :=
  Pf.front.overComplete _ (fun q _ ↦ q) (HonestWord I hμ) C

/-- The batching's completeness over the word. -/
def openingBatchOverComplete :
    Component.Complete (openingBatchOver I (KOracle sh κ)) (honestRel I hμ (Seam.flock I))
      (honestRel I hμ (Opening.BatchedHolds I)) :=
  Component.batchComplete (KOracle sh κ) E _ _ fun _ _ _ h ρ ↦
    ⟨h.1, Opening.batched_of_flock I h.2 ρ⟩

/-- The weighted claim of a weight against a table mapped from a subring is the claim against the
table through the map. -/
private theorem pair_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (W : Weight S n) (t : CMlPolynomialEval R n) :
    W.pair (RingHom.id S) (CMlPolynomialEval.map φ t) = W.pair φ t := by
  simp [Weight.pair, CMlPolynomialEval.map]

/-- The weighted claim against a table carried along an equality of heights, weight and table
carried alike. -/
private theorem pair_cast_cast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ}
    (h : m = n) (W : Weight S n) (t : CMlPolynomialEval R n) :
    (h.symm ▸ W).pair φ (h.symm ▸ t) = W.pair φ t := by
  subst h
  rfl

/-- The opening's input's completeness: on the honest word of a stack on which the batched
claim holds, WHIR's opening receives the honest word of the stack in `E` and its weighted
claim. -/
def openInputComplete :
    Component.Complete (openInput I hμ) (honestRel I hμ (Opening.BatchedHolds I))
      (stackRel sh κ) :=
  Component.mapOraclesComplete _ _ _ _ _ fun c o q h ↦ by
    refine ⟨?_, ?_⟩
    · have hg : o 0 = kwordOf sh.ℓ κ sh.R sh.t (hμ.symm ▸ q.values) := h.1
      show (o 0).lift = _
      rw [hg, kwordOf_lift]
    · show c.value = (hμ.symm ▸ c.weight).pair (RingHom.id E)
        (CMlPolynomialEval.map (algebraMap K E) (hμ.symm ▸ q.values))
      rw [pair_map, pair_cast_cast _ hμ]
      exact h.2.symm

/-- The compiled protocol's completeness: the commitment's, the four phases' and the batching's
over the word, the opening's input's and WHIR's opening's. -/
def listBindingComplete {P : Phases I} (C : P.Complete) (L : Ladder sh κ) :
    Component.Complete (listBindingDef P hμ L) (M3Rel I) Set.univ :=
  (((((((commitWordComplete I hμ).append (C.bus.over I hμ)).append (C.table.over I hμ)).append
    (C.pub.over I hμ)).append (C.flock.over I hμ)).append (openingBatchOverComplete I hμ)).append
    (openInputComplete I hμ)).append (whirOpenComplete sh κ L)

/-- **Perfect completeness of the list-binding compilation**: on every statement and stack with
`M3Holds`, the honest prover, which commits the honest word of its stack, convinces the compiled
verifier with probability one. -/
theorem listBinding_perfectCompleteness {P : Phases I} (C : P.Complete) (L : Ladder sh κ)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (listBindingDef P hμ L).red.perfectCompleteness init impl (M3Rel I) Set.univ :=
  (listBindingComplete I hμ C L).complete init impl

end Complete

end
end LeanerVM.Protocol
