/-
  LeanerVM.Protocol.ToArkLib.TranscriptMap

  A verifier that decodes the transcript of one schedule into a transcript of another before
  reading it: round-by-round knowledge soundness carries over at the same error, with the
  extractor and the state function read on the decoded transcript. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.Security.RoundByRound
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Decoding the transcript

Two schedules of the same length and the same directions: `pSpec'`, the messages as they are
sent (the *wire*), and `pSpec`, the messages a verifier reads. A `TranscriptMap S pSpec' pSpec`
maps every partial transcript of `pSpec'`, given the statement, to a partial transcript of
`pSpec` of the same length, causally: the image of a transcript extended by a prover message
extends the image of the transcript by some message (`map_msg`), and the image of a transcript
extended by a challenge extends it by that challenge, carried across by a bijection of the
challenge types (`chal`, `map_chal`). A message may thus be decoded from the statement and
everything sent before it, as a verifier that reads one value less than it checks derives the
missing value from the claim the earlier rounds left.

`Verifier.comap V T` runs `V` on the decoded transcript. `rbrKnowledgeSoundnessWorstCaseWith_comap`:
if `V` is round-by-round knowledge sound at the error `ε`, for an extractor and a knowledge state
function, then `V.comap T` is, at the same `ε`, for the extractor and the state function read on
the decoded transcript (`Extractor.RoundByRound.comap`, `KnowledgeStateFunction.comap`). A uniform
challenge carried by a bijection is uniform, so each challenge's escape probability is the
original's at the decoded prefix. The decoding of messages need not be injective: soundness
transfers for any causal map.

`TranscriptMap.ofMessage` builds the map that decodes each message by itself, from the statement
alone.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-- A causal map of the partial transcripts of `pSpec'` to those of `pSpec`, given the statement,
which carries the challenges across bijectively. -/
structure TranscriptMap (S : Type) {n : ℕ} (pSpec' pSpec : ProtocolSpec n) where
  /-- The two schedules have the same directions. -/
  dir_eq : ∀ i, pSpec'.dir i = pSpec.dir i
  /-- A challenge of `pSpec'`, read as a challenge of `pSpec`. -/
  chal : (i : pSpec'.ChallengeIdx) → pSpec'.Challenge i →
    pSpec.Challenge ⟨i.1, (dir_eq i.1).symm.trans i.2⟩
  /-- The challenges are carried across bijectively. -/
  chal_bijective : ∀ i, Function.Bijective (chal i)
  /-- The image of a partial transcript. -/
  map : (k : Fin (n + 1)) → S → pSpec'.Transcript k → pSpec.Transcript k
  /-- A message extends the image by some message. -/
  map_msg : ∀ (k : Fin n), pSpec'.dir k = .P_to_V → ∀ (s : S) (tr : pSpec'.Transcript k.castSucc)
    (x : pSpec'.«Type» k), ∃ x', map k.succ s (tr.concat x) = (map k.castSucc s tr).concat x'
  /-- A challenge extends the image by itself, carried across. -/
  map_chal : ∀ (k : Fin n) (h : pSpec'.dir k = .V_to_P) (s : S)
    (tr : pSpec'.Transcript k.castSucc) (x : pSpec'.«Type» k),
    map k.succ s (tr.concat x) = (map k.castSucc s tr).concat (chal ⟨k, h⟩ x)

namespace TranscriptMap

variable {S : Type} {n : ℕ} {pSpec' pSpec : ProtocolSpec n}

/-- The challenge index of `pSpec` a challenge index of `pSpec'` is carried to. -/
abbrev idx (T : TranscriptMap S pSpec' pSpec) (i : pSpec'.ChallengeIdx) : pSpec.ChallengeIdx :=
  ⟨i.1, (T.dir_eq i.1).symm.trans i.2⟩

/-- A direction that is not the prover's is the verifier's. -/
theorem dir_of_ne {d : Direction} (h : ¬ d = .P_to_V) : d = .V_to_P := by
  cases d
  · exact absurd rfl h
  · rfl

/-- The map that decodes each message by itself, given the statement, and carries each challenge
across. -/
def ofMessage (dir_eq : ∀ i, pSpec'.dir i = pSpec.dir i)
    (chal : (i : pSpec'.ChallengeIdx) → pSpec'.Challenge i →
      pSpec.Challenge ⟨i.1, (dir_eq i.1).symm.trans i.2⟩)
    (chal_bijective : ∀ i, Function.Bijective (chal i))
    (f : S → (i : pSpec'.MessageIdx) → pSpec'.Message i →
      pSpec.Message ⟨i.1, (dir_eq i.1).symm.trans i.2⟩) :
    TranscriptMap S pSpec' pSpec where
  dir_eq := dir_eq
  chal := chal
  chal_bijective := chal_bijective
  map := fun _ s tr i ↦
    if h : pSpec'.dir (Fin.castLE (by omega) i) = .P_to_V then
      f s ⟨Fin.castLE (by omega) i, h⟩ (tr i)
    else chal ⟨Fin.castLE (by omega) i, dir_of_ne h⟩ (tr i)
  map_msg := fun k hk s tr x ↦ ⟨f s ⟨k, hk⟩ x, by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Transcript.concat_last]
      exact dite_eq_left_of_eq_true (eq_true hk)
    · simp only [Transcript.concat_castSucc]
      rfl⟩
  map_chal := fun k hk s tr x ↦ by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Transcript.concat_last]
      exact dite_eq_right_of_eq_false (eq_false fun h ↦ Direction.noConfusion (hk.symm.trans h))
    · simp only [Transcript.concat_castSucc]
      rfl

end TranscriptMap

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ}
  {pSpec' pSpec : ProtocolSpec n}

/-- The verifier that reads the decoded transcript. -/
def comap (V : Verifier oSpec StmtIn StmtOut pSpec) (T : TranscriptMap StmtIn pSpec' pSpec) :
    Verifier oSpec StmtIn StmtOut pSpec' where
  verify := fun s tr ↦ V.verify s (T.map (Fin.last n) s tr)

end Verifier

/-- The extractor that reads the decoded transcript. -/
def Extractor.RoundByRound.comap {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type}
    {n : ℕ} {pSpec' pSpec : ProtocolSpec n} {WitMid : Fin (n + 1) → Type}
    (E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (T : TranscriptMap StmtIn pSpec' pSpec) :
    Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec' WitMid where
  eqIn := E.eqIn
  extractMid := fun m s tr w ↦ E.extractMid m s (T.map m.succ s tr) w
  extractOut := fun s tr w ↦ E.extractOut s (T.map (Fin.last n) s tr) w

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type} {n : ℕ}
  {pSpec' pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec'.Challenge i)] {σ : Type}
  {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {V : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
  {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}

/-- The knowledge state function read on the decoded transcript, for the verifier and the
extractor that read it. -/
def KnowledgeStateFunction.comap (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (T : TranscriptMap StmtIn pSpec' pSpec) :
    (Verifier.comap V T).KnowledgeStateFunction init impl relIn relOut
      (Extractor.RoundByRound.comap E T) where
  toFun := fun m s tr w ↦ K.toFun m s (T.map m s tr) w
  toFun_empty := fun s w ↦ by
    rw [K.toFun_empty s w]
    exact Iff.of_eq (congrArg (fun t ↦ K.toFun 0 s t w) (Subsingleton.elim _ _))
  toFun_next := fun m hm s tr msg w h ↦ by
    obtain ⟨x', hx'⟩ := T.map_msg m hm s tr msg
    show K.toFun m.castSucc s (T.map m.castSucc s tr)
      (E.extractMid m s (T.map m.succ s (tr.concat msg)) w)
    have h' : K.toFun m.succ s (T.map m.succ s (tr.concat msg)) w := h
    rw [hx'] at h' ⊢
    exact K.toFun_next m ((T.dir_eq m).symm.trans hm) s _ x' w h'
  toFun_full := fun s tr w hpos ↦ K.toFun_full s (T.map (Fin.last n) s tr) w hpos

/-- Round-by-round knowledge soundness carries over to the verifier that reads the decoded
transcript, at the same error, for the extractor and the state function read on it. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_comap
    {K : V.KnowledgeStateFunction init impl relIn relOut E} {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid E K ε)
    (T : TranscriptMap StmtIn pSpec' pSpec) :
    (Verifier.comap V T).rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut WitMid
      (Extractor.RoundByRound.comap E T) (KnowledgeStateFunction.comap K T)
      (fun i ↦ ε (T.idx i)) := by
  intro s i tr
  refine le_of_eq_of_le ?_ (h s (T.idx i) (T.map i.1.castSucc s tr))
  simp only [KnowledgeStateFunction.comap, Extractor.RoundByRound.comap,
    T.map_chal i.1 i.2 s tr]
  exact SampleableType.prEvent_uniformSample_comp_of_bijective (T.chal_bijective i)
    fun c ↦ ∃ w, ¬ K.toFun i.1.castSucc s (T.map i.1.castSucc s tr)
      (E.extractMid i.1 s ((T.map i.1.castSucc s tr).concat c) w) ∧
      K.toFun i.1.succ s ((T.map i.1.castSucc s tr).concat c) w

end Verifier

end
end LeanerVM.Protocol
