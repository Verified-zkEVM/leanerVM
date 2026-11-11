/-
  LeanerVM.Protocol.Core.Decoded

  What a transcript the verifier's chain history decodes to carries: the words supplied to the
  decoder, and front phases whose round polynomials pass their checks.
-/

module

public import LeanerVM.Protocol.Compile.Front
public import LeanerVM.Protocol.DecodeWire
public import LeanerVM.Protocol.Prove.ReadBack

/-!
# The decoded transcript

The decoder of leanVM's chain history (`DecodeChain.decoder`) reads a transcript of the compiled
protocol off the history, with words supplied for the oracle messages. Every value a slot reads
has the properties the slot's code enforces (`Always`), and `Always` composes along the slot
monad and along appended decoders; on a history the decoder reads exactly, the decoded
transcript has every property that holds of all the decoder's values (`Always.of_decode`).

* Round polynomials are read by `polySlot`, which keeps only polynomials that pass their check
  against the running claim, so the decoded rounds are solved (`RoundsSolved`), in the grand
  product, the bus phase, the table sumcheck and the Flock phase (`front_of_decode`): each
  phase's claims are the oracle verifier's, the decoder's running state being the oracle
  verifier's statement (`out_roundsFront`, `stRel_layerNext`).
* The commitment and every later commitment of WHIR's chain read their word from the supplied
  ones: the decoded transcript's level-0 word is the supplied one (`front_of_decode`), and so is
  every later level's (`LadderWords`, `words_of_decode`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir SlotDecoder Compile SumcheckRound CompPoly CMlPolynomialEval

@[expose] public section

namespace Core

/-! ## Values a slot reads -/

/-- Every value a slot reads has the property `P`. -/
def Always {α β : Type} (s : Slot α β) (P : β → Prop) : Prop :=
  ∀ l x r, s.read l = some (x, r) → P x

theorem Always.bind {α β γ : Type} {s : Slot α β} {P : β → Prop} {f : β → Slot α γ}
    {Q : γ → Prop} (hs : Always s P) (hf : ∀ x, P x → Always (f x) Q) : Always (s >>= f) Q := by
  intro l y r h
  rw [Slot.read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x, l₁⟩, h₁, h₂⟩ := h
  exact hf x (hs _ _ _ h₁) _ _ _ h₂

theorem Always.pure {α β : Type} {P : β → Prop} {x : β} (h : P x) :
    Always (Pure.pure x : Slot α β) P := by
  intro l y r hr
  rw [Slot.read_pure, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1 ▸ h

theorem Always.true {α β : Type} (s : Slot α β) : Always s fun _ ↦ True := fun _ _ _ _ ↦ trivial

theorem Always.mono {α β : Type} {s : Slot α β} {P Q : β → Prop} (h : Always s P)
    (hPQ : ∀ x, P x → Q x) : Always s Q := fun l x r hr ↦ hPQ x (h l x r hr)

theorem Always.map {α β γ : Type} {s : Slot α β} {g : β → γ} {P : γ → Prop}
    (h : Always s fun x ↦ P (g x)) : Always (g <$> s) P := by
  rw [← bind_pure_comp]
  exact h.bind fun x hx ↦ Always.pure hx

theorem always_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder Reading pSpec₁} {D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂}
    {P₁ : pSpec₁.FullTranscript → Prop}
    {P₂ : pSpec₁.FullTranscript → pSpec₂.FullTranscript → Prop}
    {Q : (pSpec₁ ++ₚ pSpec₂).FullTranscript → Prop}
    (h₁ : Always D₁.toSlot P₁) (h₂ : ∀ t₁, P₁ t₁ → Always (D₂ t₁).toSlot (P₂ t₁))
    (hQ : ∀ t₁ t₂, P₁ t₁ → P₂ t₁ t₂ → Q (t₁ ++ₜ t₂)) : Always (D₁.append D₂).toSlot Q := by
  rw [toSlot_append]
  exact h₁.bind fun t₁ ht₁ ↦ (h₂ t₁ ht₁).bind fun t₂ ht₂ ↦ Always.pure (hQ t₁ t₂ ht₁ ht₂)

theorem always_single {pSpec : ProtocolSpec 1} {s : Slot Reading (pSpec.«Type» 0)}
    {P : pSpec.«Type» 0 → Prop} (h : Always s P) : Always (single s).toSlot fun t ↦ P (t 0) := by
  rw [toSlot_single]
  exact Always.map h

theorem Always.of_decode {n : ℕ} {pSpec : ProtocolSpec n} {D : SlotDecoder Reading pSpec}
    {P : pSpec.FullTranscript → Prop} (h : Always D.toSlot P) {l : List Reading}
    {t : pSpec.FullTranscript} (ht : D.decode l = some t) : P t :=
  h l t [] (D.decode_eq_some.mp ht)

/-! ## Rounds -/

theorem always_polySlot (d : ℕ) (claim : Thunk E) (eq? : Thunk (Option E)) :
    Always (polySlot d claim eq?) fun c ↦ RoundPoly.Check claim.get eq?.get c := by
  unfold polySlot
  refine Always.bind (Always.true _) fun w _ ↦ ?_
  rcases h : RoundPoly.decode d claim.get eq?.get w with _ | c
  · intro l x r hr
    simp at hr
  · exact Always.pure (RoundPoly.check_of_decode h)

theorem always_roundsDec (d : ℕ) (eq? : ℕ → Option E) :
    ∀ (m : ℕ) (σ : Thunk E × ℕ),
      Always (roundsDec d eq? σ m).toSlot fun t ↦ RoundsSolved eq? m σ.2 σ.1.get t
  | 0, σ => fun _ _ _ _ ↦ trivial
  | m + 1, σ => by
    rw [roundsDec, toSlot_rounds_succ]
    refine Always.bind (always_polySlot _ _ _) fun p hp ↦ Always.bind (Always.true _) fun c _ ↦ ?_
    refine Always.bind (always_roundsDec d eq? m _) fun t ht ↦ Always.pure ?_
    exact (roundsSolved_roundsCons p c t).mpr ⟨hp, ht⟩

section Rounds

variable {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type} {d : ℕ}
  (P : Polys E X O W d) (wt : Weights E X) (m : ℕ)

private theorem out_roundsFront_succ (i j : ℕ) (h : j + (i + 1) = m) (s : Stmt X E j)
    (q : Message E d)
    (c : E) (tr : (roundsSpec E d i).FullTranscript) :
    (roundsFront P wt m (i + 1) j h).out s (roundsCons q c tr) =
      (roundsFront P wt m i (j + 1) (by omega)).out (next j s (evaluate d q c) c) tr := by
  rw [roundsCons]
  show (roundsFront P wt m i (j + 1) _).out ((roundFront P j wt).out s (roundTr q c ++ₜ tr).fst)
    (roundTr q c ++ₜ tr).snd = _
  rw [FullTranscript.append_fst, FullTranscript.append_snd]
  rfl

private theorem roundsNext_roundsCons (σ : Thunk E × ℕ) {i : ℕ} (q : Vector E (d + 1)) (c : E)
    (t : (roundsSpec E d i).FullTranscript) :
    roundsNext σ (i + 1) (roundsCons q c t) =
      roundsNext (Thunk.mk fun _ ↦ RoundPoly.eval q c, σ.2 + 1) i t := by
  simp only [roundsNext, roundsCons, roundTr, roundNext, FullTranscript.append_fst,
    FullTranscript.append_snd, msgTr_zero, chalTr_zero]

private theorem roundsChals_roundsCons {i : ℕ} (q : Vector E (d + 1)) (c : E)
    (t : (roundsSpec E d i).FullTranscript) :
    roundsChals (i + 1) (roundsCons q c t) = c :: roundsChals i t := by
  simp only [roundsChals, roundsCons, roundTr, FullTranscript.append_fst,
    FullTranscript.append_snd, chalTr_zero]

/-- The rounds' verdict keeps the public data, appends the challenges to the point, and its claim
is the decoder's running claim. -/
theorem out_roundsFront :
    ∀ (i j : ℕ) (h : j + i = m) (s : Stmt X E j) (t : (roundsSpec E d i).FullTranscript)
      (σ : Thunk E × ℕ), σ.1.get = s.2.2 →
      ((roundsFront P wt m i j h).out s t).1 = s.1 ∧
      ((roundsFront P wt m i j h).out s t).2.1.toList = s.2.1.toList ++ roundsChals i t ∧
      ((roundsFront P wt m i j h).out s t).2.2 = (roundsNext σ i t).1.get
  | 0, j, h, s, t, σ, hσ => by
    refine ⟨rfl, ?_, hσ.symm⟩
    have e : ((roundsFront P wt m 0 j h).out s t).2.1 = Vector.cast (by omega) s.2.1 := rfl
    rw [e, Vector.toList_cast]
    simp [roundsChals]
  | i + 1, j, h, s, t, σ, hσ => by
    obtain ⟨q, c, t', rfl⟩ : ∃ q c t', t = roundsCons q c t' := ⟨_, _, _, eq_roundsCons t⟩
    rw [out_roundsFront_succ, roundsNext_roundsCons, roundsChals_roundsCons]
    obtain ⟨h₁, h₂, h₃⟩ := out_roundsFront i (j + 1) (by omega) (next j s (evaluate d q c) c) t'
      (Thunk.mk fun _ ↦ RoundPoly.eval q c, σ.2 + 1) (eval_eq_evaluate q c)
    refine ⟨h₁, ?_, h₃⟩
    rw [h₂]
    simp [next, Vector.toList_push]

end Rounds

/-! ## The grand product -/

section Gkr

variable {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] (μ : ℕ)
  (leaves : X → (∀ i, O i) → Fin 3 → CMlPolynomialEval E μ)

/-- The decoder's state of the grand product is a layer statement's point and claims. -/
private def StRel {m : ℕ} (st : GkrState) (ℓ : Gkr.LayerStmt X E 3 m) : Prop :=
  st.get.1 = ℓ.2.1.toList ∧ st.get.2 = ℓ.2.2

theorem toVec_toList {n : ℕ} (v : Vector E n) : toVec n v.toList = v := by
  apply Vector.ext
  intro i _
  simp [toVec]

private theorem exists_eq_stepTr' {ρ m : ℕ} (t : (stepSpec E 3 ρ m).FullTranscript) :
    ∃ (lam : E) (R : (roundsSpec E (2 ^ ρ) m).FullTranscript) (ch : Fin 3 → Vector E (2 ^ ρ))
      (u : Vector E ρ), t = ((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i] := by
  obtain ⟨f, hf⟩ := exists_eq_chalsTr ρ t.snd
  refine ⟨t.fst.fst.fst 0, t.fst.fst.snd, t.fst.snd 0, Vector.ofFn f, ?_⟩
  conv_lhs => rw [Gkr.eq_stepTr t]
  rw [hf]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

private theorem out_layerStepFront (ρ m : ℕ) {S : Type} (inp : S → Gkr.LayerStmt X E 3 m) (s : S)
    (lam : E) (R : (roundsSpec E (2 ^ ρ) m).FullTranscript) (ch : Fin 3 → Vector E (2 ^ ρ))
    (u : Vector E ρ) :
    (Gkr.layerStepFront 3 μ leaves ρ m inp).out s
        (((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i]) =
      Gkr.interpDone 3 ρ m ((Gkr.childNext 3 ρ m ((roundsFront (Gkr.roundPoly 3 μ leaves ρ m)
        (Gkr.weights 3 m) m m 0 (Nat.zero_add m)).out
          ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) R) ch).1, u) := by
  have hI : ∀ x : Gkr.InterpStmt X E 3 m ρ 0,
      (Gkr.interpolateFront (F := E) (X := X) (O := O) 3 ρ m).out x (chalsTr ρ fun i ↦ u[i]) =
        Gkr.interpDone 3 ρ m (x.1, u) := fun x ↦
    ((Component.Front.run_eq_some_iff _).mp (Gkr.run_interpolateFront 3 ρ m x u)).2
  simp only [Gkr.layerStepFront, Component.Front.append, FullTranscript.append_fst,
    FullTranscript.append_snd, hI]
  rfl

private theorem stRel_layerNext (ρ m : ℕ) {S : Type} (inp : S → Gkr.LayerStmt X E 3 m) (s : S)
    (t : (stepSpec E 3 ρ m).FullTranscript) :
    StRel (layerNext t) ((Gkr.layerStepFront 3 μ leaves ρ m inp).out s t) := by
  obtain ⟨lam, R, ch, u, rfl⟩ := exists_eq_stepTr' t
  rw [out_layerStepFront]
  obtain ⟨-, h₂, -⟩ := out_roundsFront (Gkr.roundPoly 3 μ leaves ρ m) (Gkr.weights 3 m) m m 0
    (Nat.zero_add m) ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) R
    (Thunk.pure (powerBatch (inp s).2.2 lam), 0) rfl
  refine ⟨?_, ?_⟩
  · simp only [layerNext, get_thunk_mk, Gkr.interpDone, Gkr.childNext, FullTranscript.append_fst,
      FullTranscript.append_snd, drawsList_chalsTr, Vector.toList_cast, Vector.toList_append, h₂,
      ofFn_getElem_eq_toList]
    simp
  · simp only [layerNext, get_thunk_mk, Gkr.interpDone, Gkr.childNext, FullTranscript.append_fst,
      FullTranscript.append_snd, drawsList_chalsTr, msgTr_zero, ofFn_getElem_eq_toList,
      toVec_toList]

/-- A layer's rounds pass their checks from the decoder's state. -/
private theorem always_layerDec (st : GkrState) (ρ m : ℕ) :
    Always (layerDec st ρ m).toSlot fun t ↦ RoundsSolved (fun j ↦ st.get.1[j]?) m 0
      (powerBatch st.get.2 (layerCombiner t)) t.fst.fst.snd := by
  unfold layerDec
  refine always_append (always_append
    (always_append (always_single (Always.true _)) (fun t₁ _ ↦ always_roundsDec (2 ^ ρ) _ m _)
      (Q := fun T ↦ RoundsSolved (fun j ↦ st.get.1[j]?) m 0 (powerBatch st.get.2 (T.fst 0))
        T.snd) ?_)
    (fun _ _ ↦ always_single (Always.true _))
    (Q := fun T ↦ RoundsSolved (fun j ↦ st.get.1[j]?) m 0 (powerBatch st.get.2 (T.fst.fst 0))
      T.fst.snd) ?_)
    (fun _ _ ↦ Always.true _) ?_
  · intro t₁ t₂ _ h
    simpa only [FullTranscript.append_fst, FullTranscript.append_snd, get_thunk_mk] using h
  · intro t₁ t₂ h _
    simpa only [FullTranscript.append_fst, FullTranscript.append_snd, get_thunk_mk] using h
  · intro t₁ t₂ h _
    simpa only [layerCombiner, drawOf, FullTranscript.append_fst, FullTranscript.append_snd]
      using h

private theorem layerSolved_of_stRel {ρ m : ℕ} {st : GkrState} {ℓ : Gkr.LayerStmt X E 3 m}
    (hst : StRel st ℓ) {t : (stepSpec E 3 ρ m).FullTranscript}
    (h : RoundsSolved (fun j ↦ st.get.1[j]?) m 0 (powerBatch st.get.2 (layerCombiner t))
      t.fst.fst.snd) : LayerSolved ρ m ℓ t := by
  rw [LayerSolved, ← hst.2]
  have he : (fun j : ℕ ↦ st.get.1[j]?) = fun j : ℕ ↦ ℓ.2.1[j]? := by
    funext j
    rw [hst.1, Vector.getElem?_toList]
  rwa [he] at h

private theorem always_stepsDec : ∀ (k m : ℕ) (st : GkrState),
    Always (stepsDec st k m).toSlot fun t ↦ ∀ ℓ : Gkr.LayerStmt X E 3 m, StRel st ℓ →
      StepsSolved μ leaves k m ℓ t
  | 0, _, _ => fun _ _ _ _ _ _ ↦ trivial
  | k + 1, m, st => by
    refine always_append (always_layerDec st 2 m)
      (fun t₁ _ ↦ always_stepsDec k (m + 2) (layerNext t₁)) ?_
    intro t₁ t₂ h₁ h₂ ℓ hℓ
    exact (stepsSolved_stepsCons μ leaves ℓ t₁ t₂).mpr
      ⟨layerSolved_of_stRel hℓ h₁, h₂ _ (stRel_layerNext μ leaves 2 m id ℓ t₁)⟩

private theorem always_oddDec (st : GkrState) : ∀ (r : ℕ) (hr : r ≤ 1),
    Always (oddDec st r).toSlot fun t ↦ ∀ s : X × (Fin 3 → E), StRel st (Gkr.rootStmt 3 s) →
      OddSolved r s t ∧ StRel (oddNext st r t) ((Gkr.oddFront 3 μ leaves r hr).out s t)
  | 0, _ => fun _ _ _ _ _ hs ↦ ⟨trivial, hs⟩
  | 1, _ => (always_layerDec st 1 0).mono fun t ht s hs ↦
      ⟨layerSolved_of_stRel hs ht, stRel_layerNext μ leaves 1 0 (Gkr.rootStmt 3) s t⟩
  | _ + 2, h => absurd h (by omega)

private theorem always_gkrDec (st : GkrState) :
    Always (gkrDec st μ).toSlot fun t ↦ ∀ s : X × (Fin 3 → E), StRel st (Gkr.rootStmt 3 s) →
      GkrSolved μ leaves s t := by
  unfold gkrDec
  refine always_append (always_append (always_oddDec μ leaves st (μ % 2)
    (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos)))
    (fun t₁ _ ↦ always_stepsDec μ leaves _ _ (oddNext st _ t₁))
    (Q := fun T ↦ ∀ s : X × (Fin 3 → E), StRel st (Gkr.rootStmt 3 s) →
      OddSolved (μ % 2) s T.fst ∧ StepsSolved μ leaves (μ / 2) (μ % 2)
        ((Gkr.oddFront 3 μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))).out s
          T.fst) T.snd) ?_) (fun _ _ ↦ Always.true _) ?_
  · intro t₁ t₂ h₁ h₂ s hs
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact ⟨(h₁ s hs).1, h₂ _ (h₁ s hs).2⟩
  · intro t₁ t₂ h₁ _ s hs
    simp only [GkrSolved, FullTranscript.append_fst]
    exact h₁ s hs

end Gkr

/-! ## The bus phase and the table sumcheck -/

private theorem always_busDec (I : M3Instance) (input : I.Stmt) :
    Always (busDec I).toSlot (BusSolved I input) := by
  unfold busDec
  refine always_append (always_append (always_append (always_single (Always.true _))
    (fun _ _ ↦ always_single (Always.true _)) (Q := fun _ ↦ True) (fun _ _ _ _ ↦ trivial))
    (fun t₁ _ ↦ always_gkrDec I.μBus (Bus.leaves I) _)
    (Q := fun (T : (draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus).FullTranscript) ↦
      GkrSolved I.μBus (Bus.leaves I)
      ((input, T.fst.fst 0), ![(T.fst.snd 0).1, (T.fst.snd 0).1, (T.fst.snd 0).2]) T.snd) ?_)
    (fun _ _ ↦ Always.true _) ?_
  · intro t₁ t₂ _ h
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact h _ ⟨rfl, rfl⟩
  · intro t₁ t₂ h _
    refine ⟨t₁.fst.fst 0, t₁.fst.snd 0, t₁.snd, t₂ 0, ?_, h⟩
    rw [busTrOf, ← eq_chalTr, ← eq_msgTr, ← eq_msgTr, FullTranscript.append_fst_snd,
      FullTranscript.append_fst_snd]

private theorem always_tableDec (I : M3Instance) (s : Thunk (I.Stmt × BusOut I)) :
    Always (tableDec I s).toSlot (TableSolved I s.get) := by
  unfold tableDec
  refine always_append (always_append (always_single (Always.true _))
    (fun t₁ _ ↦ always_roundsDec 3 (fun _ ↦ none) I.τmax _)
    (Q := fun T ↦ RoundsSolved (fun _ ↦ none) I.τmax 0
      (powerBatch (TableSumcheck.claimed I s.get) (T.fst 0)) T.snd) ?_)
    (fun _ _ ↦ Always.true _) ?_
  · intro t₁ t₂ _ h
    simpa only [FullTranscript.append_fst, FullTranscript.append_snd, get_thunk_mk] using h
  · intro t₁ t₂ h _
    refine ⟨t₁.fst 0, t₁.snd, t₂ 0, ?_, h⟩
    rw [tableTrOf, ← eq_chalTr, ← eq_msgTr, FullTranscript.append_fst_snd]


/-! ## The Flock phase -/

private theorem zcMid_snd (k : ℕ) (t : (flockSpec₄ k).FullTranscript) : (zcMid k t).2 = 8 := by
  simp only [zcMid, roundsNext_snd]

/-- The Flock phase's rounds pass their checks from the claims its decoder carries. -/
private theorem always_flockDecOf (k : ℕ) :
    Always (flockDecOf k).toSlot fun t ↦
      (RoundsSolved (zcWeights k t.fst.fst.fst.fst.fst.fst.fst) 8 0
          (skipClaimOf k t.fst.fst.fst.fst.fst.fst.fst) t.fst.fst.fst.fst.fst.fst.snd ∧
        RoundsSolved (zcWeights k t.fst.fst.fst.fst.fst.fst.fst) k 8
          (zcMid k t.fst.fst.fst.fst.fst.fst).1.get t.fst.fst.fst.fst.fst.snd) ∧
        RoundsSolved (fun _ ↦ none) 8 0 (linClaimOf k t.fst.fst.fst) t.fst.fst.snd := by
  unfold flockDecOf
  refine always_append (always_append (always_append (always_append (always_append
    (always_append (always_append (always_append (always_append
    (Always.true _) (fun _ _ ↦ Always.true _) (Q := fun _ ↦ True) (fun _ _ _ _ ↦ trivial))
    (fun _ _ ↦ Always.true _) (Q := fun _ ↦ True) (fun _ _ _ _ ↦ trivial))
    (fun t _ ↦ always_roundsDec 2 (zcWeights k t) 8 _)
    (Q := fun T ↦ RoundsSolved (zcWeights k T.fst) 8 0 (skipClaimOf k T.fst) T.snd) ?_)
    (fun t _ ↦ always_roundsDec 2 (zcWeights k t.fst) k _)
    (Q := fun T ↦ RoundsSolved (zcWeights k T.fst.fst) 8 0 (skipClaimOf k T.fst.fst) T.fst.snd ∧
      RoundsSolved (zcWeights k T.fst.fst) k 8 (zcMid k T.fst).1.get T.snd) ?_)
    (fun _ _ ↦ Always.true _)
    (Q := fun T ↦ RoundsSolved (zcWeights k T.fst.fst.fst) 8 0 (skipClaimOf k T.fst.fst.fst)
        T.fst.fst.snd ∧
      RoundsSolved (zcWeights k T.fst.fst.fst) k 8 (zcMid k T.fst.fst).1.get T.fst.snd)
    (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h))
    (fun _ _ ↦ Always.true _)
    (Q := fun T ↦ RoundsSolved (zcWeights k T.fst.fst.fst.fst) 8 0
        (skipClaimOf k T.fst.fst.fst.fst) T.fst.fst.fst.snd ∧
      RoundsSolved (zcWeights k T.fst.fst.fst.fst) k 8 (zcMid k T.fst.fst.fst).1.get T.fst.fst.snd)
    (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h))
    (fun t _ ↦ always_roundsDec 2 (fun _ ↦ none) 8 _)
    (Q := fun T ↦ (RoundsSolved (zcWeights k T.fst.fst.fst.fst.fst) 8 0
        (skipClaimOf k T.fst.fst.fst.fst.fst) T.fst.fst.fst.fst.snd ∧
      RoundsSolved (zcWeights k T.fst.fst.fst.fst.fst) k 8 (zcMid k T.fst.fst.fst.fst).1.get
        T.fst.fst.fst.snd) ∧ RoundsSolved (fun _ ↦ none) 8 0 (linClaimOf k T.fst) T.snd) ?_)
    (fun _ _ ↦ Always.true _)
    (Q := fun T ↦ (RoundsSolved (zcWeights k T.fst.fst.fst.fst.fst.fst) 8 0
        (skipClaimOf k T.fst.fst.fst.fst.fst.fst) T.fst.fst.fst.fst.fst.snd ∧
      RoundsSolved (zcWeights k T.fst.fst.fst.fst.fst.fst) k 8 (zcMid k T.fst.fst.fst.fst.fst).1.get
        T.fst.fst.fst.fst.snd) ∧ RoundsSolved (fun _ ↦ none) 8 0 (linClaimOf k T.fst.fst) T.fst.snd)
    (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h))
    (fun _ _ ↦ Always.true _) (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h)
  · intro t₁ t₂ _ h
    simpa only [FullTranscript.append_fst, FullTranscript.append_snd, get_thunk_mk] using h
  · intro t₁ t₂ h₁ h₂
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    refine ⟨h₁, ?_⟩
    rw [zcMid_snd] at h₂
    exact h₂
  · intro t₁ t₂ h₁ h₂
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact ⟨h₁, h₂⟩

private theorem toVec_ofFn {n : ℕ} (f : Fin n → E) : toVec n (List.ofFn f) = Vector.ofFn f := by
  apply Vector.ext
  intro i _
  simp [toVec]

private theorem exists_eq_chalsTr_vec {k : ℕ} (t : (draws E k).FullTranscript) :
    ∃ v : Vector E k, t = chalsTr k fun i ↦ v[i] := by
  obtain ⟨f, rfl⟩ := exists_eq_chalsTr k t
  exact ⟨Vector.ofFn f, by simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]⟩

/-- The Flock phase's decoded rounds are solved, on every statement. -/
private theorem flockSolved_of_dec (I : M3Instance) (r : FlockRegion I.toShape)
    (s : I.Stmt × PubOut I)
    (t : (flockSpecOf r.kBatch).FullTranscript)
    (h : (RoundsSolved (zcWeights r.kBatch t.fst.fst.fst.fst.fst.fst.fst) 8 0
          (skipClaimOf r.kBatch t.fst.fst.fst.fst.fst.fst.fst) t.fst.fst.fst.fst.fst.fst.snd ∧
        RoundsSolved (zcWeights r.kBatch t.fst.fst.fst.fst.fst.fst.fst) r.kBatch 8
          (zcMid r.kBatch t.fst.fst.fst.fst.fst.fst).1.get t.fst.fst.fst.fst.fst.snd) ∧
        RoundsSolved (fun _ ↦ none) 8 0 (linClaimOf r.kBatch t.fst.fst.fst) t.fst.fst.snd) :
    FlockSolved I r s t := by
  obtain ⟨t₉, f₆, rfl⟩ := exists_eq_append (p₁ := flockSpec₉ r.kBatch) (p₂ := draws E 6) t
  obtain ⟨t₈, tsv, rfl⟩ :=
    exists_eq_append (p₁ := flockSpec₈ r.kBatch) (p₂ := say (Vector E 64)) t₉
  obtain ⟨t₇, lin, rfl⟩ :=
    exists_eq_append (p₁ := flockSpec₇ r.kBatch) (p₂ := roundsSpec E 2 8) t₈
  obtain ⟨t₆, tα, rfl⟩ := exists_eq_append (p₁ := flockSpec₆ r.kBatch) (p₂ := draw E) t₇
  obtain ⟨t₅, tab, rfl⟩ :=
    exists_eq_append (p₁ := flockSpec₅ r.kBatch) (p₂ := say (Vector E 2)) t₆
  obtain ⟨t₄, zcH, rfl⟩ :=
    exists_eq_append (p₁ := flockSpec₄ r.kBatch) (p₂ := roundsSpec E 2 r.kBatch) t₅
  obtain ⟨t₃, zcL, rfl⟩ :=
    exists_eq_append (p₁ := flockSpec₃ r.kBatch) (p₂ := roundsSpec E 2 8) t₄
  obtain ⟨t₂, tz, rfl⟩ := exists_eq_append (p₁ := flockSpec₂ r.kBatch) (p₂ := draw E) t₃
  obtain ⟨tv, tmsg, rfl⟩ :=
    exists_eq_append (p₁ := draws E (r.kBatch + 1)) (p₂ := say (Vector E 64)) t₂
  obtain ⟨v, rfl⟩ := exists_eq_chalsTr_vec tv
  obtain ⟨fs, rfl⟩ := exists_eq_chalsTr_vec f₆
  obtain ⟨msg, rfl⟩ : ∃ m, tmsg = msgTr m := ⟨_, eq_msgTr tmsg⟩
  obtain ⟨zskip, rfl⟩ : ∃ z, tz = chalTr z := ⟨_, eq_chalTr tz⟩
  obtain ⟨ab, rfl⟩ : ∃ m, tab = msgTr m := ⟨_, eq_msgTr tab⟩
  obtain ⟨α, rfl⟩ : ∃ z, tα = chalTr z := ⟨_, eq_chalTr tα⟩
  obtain ⟨sv, rfl⟩ : ∃ m, tsv = msgTr m := ⟨_, eq_msgTr tsv⟩
  simp only [FullTranscript.append_fst, FullTranscript.append_snd] at h
  obtain ⟨⟨hL, hH⟩, hLin⟩ := h
  have hpt : flockPoint r.kBatch (chalsTr (r.kBatch + 1) fun i ↦ v[i]) =
      (flockParams r.kBatch).point v := by
    unfold flockPoint
    rw [drawsList_chalsTr, ofFn_getElem_eq_toList]
    exact congrArg _ (toVec_toList v)
  have hw : zcWeights r.kBatch (((chalsTr (r.kBatch + 1) fun i ↦ v[i]) ++ₜ msgTr msg) ++ₜ
      chalTr zskip) = fun j ↦ ((flockParams r.kBatch).point v)[j]? := by
    funext j
    simp only [zcWeights, FullTranscript.append_fst, hpt]
  have hskip : skipClaimOf r.kBatch (((chalsTr (r.kBatch + 1) fun i ↦ v[i]) ++ₜ msgTr msg) ++ₜ
      chalTr zskip) = Flock.skipClaim (flockParams r.kBatch).nodes msg zskip := by
    simp only [skipClaimOf, FullTranscript.append_fst, FullTranscript.append_snd, msgTr_zero,
      chalTr_zero]
  rw [hw, hskip] at hL
  rw [hw] at hH
  simp only [zcMid, FullTranscript.append_fst, FullTranscript.append_snd] at hH
  obtain ⟨-, -, hoL⟩ := out_roundsFront (zcFam I r).poly (zcFam I r).weight
    (flockParams r.kBatch).m (flockParams r.kBatch).m 0 (Nat.zero_add _)
    (Flock.skipNext (flockParams r.kBatch) ((s, v), msg) zskip) zcL
    (Thunk.mk fun _ ↦ skipClaimOf r.kBatch (((chalsTr (r.kBatch + 1) fun i ↦ v[i]) ++ₜ
      msgTr msg) ++ₜ chalTr zskip), 0) hskip
  obtain ⟨-, -, hoH⟩ := out_roundsFront (zcFam I r).poly (zcFam I r).weight
    ((flockParams r.kBatch).m + (flockParams r.kBatch).κ) (flockParams r.kBatch).κ
    (flockParams r.kBatch).m rfl
    ((roundsFront (zcFam I r).poly (zcFam I r).weight (flockParams r.kBatch).m
      (flockParams r.kBatch).m 0 (Nat.zero_add _)).out
      (Flock.skipNext (flockParams r.kBatch) ((s, v), msg) zskip) zcL) zcH
    (zcMid r.kBatch ((((chalsTr (r.kBatch + 1) fun i ↦ v[i]) ++ₜ msgTr msg) ++ₜ chalTr zskip) ++ₜ
      zcL))
    (by
      rw [hoL]
      simp only [zcMid, FullTranscript.append_fst, FullTranscript.append_snd]
      rfl)
  refine ⟨v, msg, zskip, zcL, zcH, ab, α, lin, sv, fs, rfl, hL, ?_, ?_⟩
  · rw [hoL]
    exact hH
  · dsimp only [Flock.alphaNext, Flock.termNext]
    rw [hoH]
    simp only [linClaimOf, Flock.alphaNext, Flock.termNext, zcMid, FullTranscript.append_fst,
      FullTranscript.append_snd, msgTr_zero, chalTr_zero] at hLin ⊢
    exact hLin

/-! ## The front of the compiled protocol -/

/-- The Flock slot's rounds pass their checks, on every statement. -/
private def FlockOk (I : M3Instance) :
    (o : Option (FlockRegion I.toShape)) → (flockSpecOpt I o).FullTranscript → Prop
  | none, _ => True
  | some r, t => ∀ s, FlockSolved I r s t

private theorem always_flockDec (I : M3Instance) : ∀ o, Always (flockDec I o).toSlot (FlockOk I o)
  | none => fun _ _ _ _ ↦ trivial
  | some r => (always_flockDecOf r.kBatch).mono fun t ht s ↦ flockSolved_of_dec I r s t ht

private theorem always_commitSlot {M : Type} (ann : List E) (w : M) :
    Always (commitSlot ann w) (· = w) := by
  unfold commitSlot
  refine Always.bind (Always.true _) fun xs _ ↦ ?_
  split
  · exact Always.map ((Always.true _).mono fun _ _ ↦ rfl)
  · intro l x r h
    simp at h

/-- The front's decoded transcript, at the decoder's schedule: the committed word supplied, and
the bus phase's, the table sumcheck's and the Flock phase's rounds solved. -/
private def FrontOk (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt) {sh : Whir.Shape}
    {κ : ℕ}
    (w₀ : KWord sh.ℓ (κ + sh.R) sh.t)
    (T : (commitWordSpec sh κ ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ
      flockSpecOpt I I.flock ++ₚ openingSpec ++ₚ !p[]).FullTranscript) : Prop :=
  ((T.fst.fst.fst.fst.fst.fst 0 = w₀ ∧ BusSolved I input T.fst.fst.fst.fst.fst.snd) ∧
    TableSolved I (busOutOf I h input T.fst.fst.fst.fst.fst.snd) T.fst.fst.fst.fst.snd) ∧
    FlockOk I I.flock T.fst.fst.snd

/-- The front of the compiled protocol, decoded: the committed word is the one supplied, and the
bus phase's, the table sumcheck's and the Flock phase's rounds pass their checks. -/
private theorem always_frontDec (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)
    (ann : List E)
    {sh : Whir.Shape} {κ : ℕ} (w₀ : KWord sh.ℓ (κ + sh.R) sh.t) :
    Always (frontDec I h input ann w₀).toSlot (FrontOk I h input w₀) := by
  unfold frontDec
  refine always_append (always_append (always_append (always_append (always_append
    (always_append (always_single (always_commitSlot ann w₀)) (fun _ _ ↦ always_busDec I input)
      (Q := fun T ↦ T.fst 0 = w₀ ∧ BusSolved I input T.snd) ?_)
    (fun t _ ↦ always_tableDec I _)
    (Q := fun T ↦ (T.fst.fst 0 = w₀ ∧ BusSolved I input T.fst.snd) ∧
      TableSolved I (busOutOf I h input T.fst.snd) T.snd) ?_)
    (fun _ _ ↦ Always.true _)
    (Q := fun T ↦ (T.fst.fst.fst 0 = w₀ ∧ BusSolved I input T.fst.fst.snd) ∧
      TableSolved I (busOutOf I h input T.fst.fst.snd) T.fst.snd)
    (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h))
    (fun _ _ ↦ always_flockDec I _)
    (Q := fun T ↦ ((T.fst.fst.fst.fst 0 = w₀ ∧ BusSolved I input T.fst.fst.fst.snd) ∧
      TableSolved I (busOutOf I h input T.fst.fst.fst.snd) T.fst.fst.snd) ∧
      FlockOk I I.flock T.snd) ?_)
    (fun _ _ ↦ Always.true _)
    (Q := fun T ↦ ((T.fst.fst.fst.fst.fst 0 = w₀ ∧ BusSolved I input T.fst.fst.fst.fst.snd) ∧
      TableSolved I (busOutOf I h input T.fst.fst.fst.fst.snd) T.fst.fst.fst.snd) ∧
      FlockOk I I.flock T.fst.snd)
    (fun _ _ h _ ↦ by simpa only [FullTranscript.append_fst] using h))
    (fun _ _ ↦ Always.true _)
    (fun _ _ h _ ↦ by simpa only [FrontOk, FullTranscript.append_fst] using h)
  · intro t₁ t₂ h₁ h₂
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact ⟨h₁, h₂⟩
  · intro t₁ t₂ h₁ h₂
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact ⟨h₁, h₂⟩
  · intro t₁ t₂ h₁ h₂
    simp only [FullTranscript.append_fst, FullTranscript.append_snd]
    exact ⟨h₁, h₂⟩

/-- **The decoded transcript's front is solved**: at leanVM, a history decoded with the words `W`
carries `W`'s level-0 word, and its bus phase's, table sumcheck's and Flock phase's round
polynomials pass their checks against the claims the compiled verifier threads. -/
theorem front_of_decode {prog : Program} {input : PublicInput} {s : Sizes}
    {hs : s.Admissible prog} {ρ : ℕ} {hρ : validRate ρ} {W : LeanWords prog s hs ρ hρ}
    {hist : List Reading}
    {tr : (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).FullTranscript}
    (h : DecodeChain.decode prog input s hs ρ hρ W hist = some tr) :
    let I := leanVm prog s
    let f₆ := tr.fst.fst
    let f₅ := f₆.fst
    let f₄ := f₅.fst
    let f₃ := f₄.fst
    let f₂ := f₃.fst
    let bo := (busPhase I (leanIsa_conditions _ prog s)).front.out input f₂.snd
    let tout := (TableSumcheck.tableSumcheck I).front.out bo f₃.snd
    let po := (deployedPublicInputPhase I).front.out tout f₄.snd
    Prove.level0Word tr = W.level0 ∧ BusSolved I input f₂.snd ∧ TableSolved I bo f₃.snd ∧
      FlockSolved I (flockRegion prog s Blake2sFlock.blake2sFlockSpec) po f₅.snd := by
  have hdec : (compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input (announcement s ρ)
      (leanIsaChain prog s hs ρ hρ) W).decode hist = some tr := h
  have hA : FrontOk (leanVm prog s) (leanIsa_conditions _ prog s) input W.level0 tr.fst :=
    Always.of_decode (always_append (always_frontDec (leanVm prog s)
      (leanIsa_conditions _ prog s) input (announcement s ρ) W.level0)
      (fun _ _ ↦ Always.true _)
      (Q := fun tr ↦ FrontOk (leanVm prog s) (leanIsa_conditions _ prog s) input W.level0 tr.fst)
      (fun t₁ t₂ h₁ _ ↦ by simpa only [FullTranscript.append_fst] using h₁)) hdec
  obtain ⟨⟨⟨h0, hB⟩, hT⟩, hF⟩ := hA
  exact ⟨h0, hB, hT, hF _⟩

/-! ## WHIR's words -/

theorem Always.and {α β : Type} {s : Slot α β} {P Q : β → Prop} (h₁ : Always s P)
    (h₂ : Always s Q) : Always s fun x ↦ P x ∧ Q x :=
  fun l x r h ↦ ⟨h₁ l x r h, h₂ l x r h⟩

theorem always_seqTail {a : Step} {l : List Step} {D : SeqDecoder Reading (a :: l)}
    {Q : (seqSpec l).FullTranscript → Prop} (h : ∀ t, Always (D.2 t).toDecoder.toSlot Q) :
    Always D.toDecoder.toSlot fun T ↦ Q (seqTail T) :=
  always_append (Always.true _) (fun t _ ↦ h t) fun _ _ _ h₂ ↦ by
    simpa only [seqTail, FullTranscript.append_snd] using h₂

theorem always_seqHead {a : Step} {l : List Step} {D : SeqDecoder Reading (a :: l)}
    {P : a.spec.FullTranscript → Prop} (h : Always D.1.toSlot P) :
    Always D.toDecoder.toSlot fun T ↦ P (seqHead T) :=
  always_append h (fun _ _ ↦ Always.true _) fun _ _ h₁ _ ↦ by
    simpa only [seqHead, FullTranscript.append_fst] using h₁

/-- The words a chain of levels' transcript carries, level by level. -/
def LadderWords : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Words →
    (seqSpec L.steps).FullTranscript → Prop
  | _, _, .last _ _, _, _ => True
  | _, _, @Ladder.cons _ _ _ L, ws, t =>
    Prove.levelWord t = ws.1 ∧ LadderWords L ws.2 (levelWire t).2

private theorem always_levelDec_words (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    {cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k}
    {P : (seqSpec k).FullTranscript → Prop} (hc : ∀ σ', Always (cont σ').toDecoder.toSlot P) :
    Always (levelDec sh sh' κ' σ w next cont).toDecoder.toSlot fun t ↦
      Prove.levelWord t = next ∧ P (levelWire t).2 := by
  refine Always.and ?_ ?_
  · refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 1)).FullTranscript) ↦
        msgOf (seqHead (seqTail (seqTail T))) = next) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 2)).FullTranscript) ↦
        msgOf (seqHead (seqTail T)) = next) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 3)).FullTranscript) ↦
        msgOf (seqHead T) = next) fun _ ↦ ?_
    refine always_seqHead
      (P := fun (t : (Step.oracle (WordOf sh' κ') inferInstance).spec.FullTranscript) ↦
        msgOf t = next) ?_
    have key : Always ((fun _ ↦ next) <$> historyOps.nextRoot : Slot Reading (WordOf sh' κ'))
        (· = next) :=
      Always.map ((Always.true _).mono fun _ _ ↦ rfl)
    exact always_single (pSpec := (Step.oracle (WordOf sh' κ') inferInstance).spec)
      (P := fun x ↦ x = next) key
  · refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 1)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail T))))))))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 2)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail (seqTail (seqTail T)))))))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 3)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail (seqTail T))))))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 4)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail (seqTail T)))))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 5)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail (seqTail T))))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 6)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail
          (seqTail T)))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 7)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail (seqTail T))))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 8)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail (seqTail T)))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 9)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail (seqTail T))))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 10)).FullTranscript) ↦
        P (seqTail (seqTail (seqTail T)))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 11)).FullTranscript) ↦
        P (seqTail (seqTail T))) fun _ ↦ ?_
    refine always_seqTail
      (Q := fun (T : (seqSpec ((levelSteps sh sh' κ' k).drop 12)).FullTranscript) ↦
        P (seqTail T)) fun _ ↦ ?_
    exact always_seqTail fun _ ↦ hc _

private theorem always_ladderDec_words : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws : L.Words),
    Always (ladderDec L σ w ws).toDecoder.toSlot (LadderWords L ws)
  | _, _, .last _ _, _, _, _ => (Always.true _).mono fun _ _ ↦ trivial
  | _, _, @Ladder.cons sh sh' κ' L, σ, w, ws =>
    always_levelDec_words sh sh' κ' σ w ws.1 fun σ' ↦ always_ladderDec_words L σ' ws.1 ws.2

/-- **The decoded transcript carries the supplied words**: at every level of WHIR's chain, the word
the level sends is the supplied one. -/
theorem words_of_decode {prog : Program} {input : PublicInput} {s : Sizes}
    {hs : s.Admissible prog} {ρ : ℕ} {hρ : validRate ρ} {W : LeanWords prog s hs ρ hρ}
    {hist : List Reading}
    {tr : (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).FullTranscript}
    (h : DecodeChain.decode prog input s hs ρ hρ W hist = some tr) :
    LadderWords (leanIsaChain prog s hs ρ hρ).ladder W.later (Prove.ladderPart tr) := by
  have hdec : (compiledDec (leanVm prog s) (leanIsa_conditions _ prog s) input (announcement s ρ)
      (leanIsaChain prog s hs ρ hρ) W).decode hist = some tr := h
  have hw : ∀ (target : Thunk E) (w : WordOf (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ),
      Always (whirDec (leanIsaChain prog s hs ρ hρ).ladder target w W.later).toDecoder.toSlot
        fun T ↦ LadderWords (leanIsaChain prog s hs ρ hρ).ladder W.later (seqTail (seqTail T)) := by
    intro target w
    refine always_seqTail (Q := fun T ↦ LadderWords (leanIsaChain prog s hs ρ hρ).ladder W.later
      (seqTail T)) fun _ ↦ ?_
    exact always_seqTail fun _ ↦ always_ladderDec_words _ _ _ _
  exact Always.of_decode (always_append (Always.true _) (fun _ _ ↦ hw _ _)
    (Q := fun tr ↦ LadderWords (leanIsaChain prog s hs ρ hρ).ladder W.later
      (Prove.ladderPart tr))
    (fun t₁ t₂ _ h₂ ↦ by simpa only [Prove.ladderPart, FullTranscript.append_snd] using h₂)) hdec

end Core

end

end LeanerVM.Protocol
