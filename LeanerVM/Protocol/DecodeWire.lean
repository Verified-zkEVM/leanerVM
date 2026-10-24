/-
  LeanerVM.Protocol.DecodeWire

  The wire a transcript of the compiled protocol carries, and the walk's history decoded: what the
  verifier's chain walk reads on its history, the decoder reads too, as a transcript whose wire is
  the walk's.
-/

module

public import LeanerVM.Protocol.DecodeWalk

/-!
# The decoded history carries the walk's wire

`wireOf` (`LeanerVM.Protocol.Verify.WireOf`) reads the executable verifier's wire (`Verify.Wire`)
off a full transcript of the compiled protocol: every scalar and challenge where the walk records
it, each round polynomial without the coefficient the chain does not absorb (`RoundPoly.encode`),
WHIR's query positions as numbers. A transcript carries words where the chain carries roots, so the
roots read off a transcript are the default digest (`Wire.view` erases the walk's), and a position
is a number below its word's size (`Wire.view` reduces the walk's the way the verifier's algebra
does, `positionsOf`).

`walkChain_decodes`: if the chain walk on a history reads the whole history, and the history's
first eight scalars are the announcement, the history decodes, with any words, to a transcript whose
wire is the walk's, viewed. With `walkChain_history` (the logged walk reads its own history), a
chain walk the verifier accepts leaves a history that decodes (`walkChainLogged_decodes`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa CompPoly CMlPolynomialEval
  ProtocolSpec StepSchedule Verify Whir SlotDecoder

@[expose] public section

namespace DecodeChain

/-! ## The walk's wire, viewed -/

/-- A level's wire as a transcript carries it: its root the default digest, its positions reduced
below its word's size. -/
def WhirLevel.view (sh : LevelShape) (l : WhirLevel) : WhirLevel :=
  { l with
    root := l.root.map fun _ ↦ default
    positions := positionsList (positionsOf sh.queries (sh.msgLog + sh.rate) l.positions) }

/-- The walk's wire as a transcript carries it: its roots the default digest, its positions reduced
below their words' sizes. -/
def Wire.view (shs : List LevelShape) (w : Wire) : Wire :=
  { w with root := default, whir := List.zipWith WhirLevel.view shs w.whir }

/-! ## The walk's reads, decoded: scalars, challenges, round polynomials -/

section Reads

open Slot

@[simp] theorem get_thunk_mk {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

@[simp] theorem get_thunk_pure {α : Type} (a : α) : (Thunk.pure a).get = a := rfl

@[simp] theorem msgOf_oneTranscript {M : Type} (x : M) :
    msgOf (oneTranscript (pSpec := say M) x) = x := rfl

@[simp] theorem drawOf_oneTranscript {C : Type} (x : C) :
    drawOf (oneTranscript (pSpec := draw C) x) = x := rfl

/-- `k` scalars read off any reader of slots are `k`. -/
theorem length_of_read_nextScalars {ops : ChainOps (Slot Reading)} :
    ∀ {k : ℕ} {l : List Reading} {xs : List E} {r : List Reading},
      (ops.nextScalars k).read l = some (xs, r) → xs.length = k
  | 0, _, _, _, h => by
    simp only [ChainOps.nextScalars, read_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | k + 1, l, xs, r, h => by
    simp only [ChainOps.nextScalars, read_bind, Option.bind_eq_some_iff, read_pure,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨x, l₁, -, ys, l₂, hys, rfl, -⟩ := h
    simp [length_of_read_nextScalars hys]

/-- `k` challenges squeezed off any reader of slots are `k`. -/
theorem length_of_read_samples {ops : ChainOps (Slot Reading)} :
    ∀ {k : ℕ} {l : List Reading} {xs : List E} {r : List Reading},
      (samples ops k).read l = some (xs, r) → xs.length = k
  | 0, _, _, _, h => by
    simp only [samples, read_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | k + 1, l, xs, r, h => by
    simp only [samples, read_bind, Option.bind_eq_some_iff, read_pure,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨x, l₁, -, ys, l₂, hys, rfl, -⟩ := h
    simp [length_of_read_samples hys]

/-- A slot refines itself, keeping a property of what it reads. -/
theorem refines_self_of {β : Type} {P : β → Prop} (s : Slot Reading β)
    (hP : ∀ l x r, s.read l = some (x, r) → P x) : Refines (fun x y ↦ x = y ∧ P x) s s :=
  fun l x r h ↦ ⟨x, h, rfl, hP l x r h⟩

/-- A list of length `n` is the vector `toVec n` makes of it. -/
theorem toList_toVec {n : ℕ} {l : List E} (h : l.length = n) : (toVec n l).toList = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [toVec]

/-- `n` scalars read as a vector. -/
theorem refines_vecSlot (n : ℕ) :
    Refines (fun xs v ↦ v.toList = xs) (historyOps.nextScalars n) (vecSlot n) := by
  intro l xs r h
  refine ⟨toVec n xs, ?_, toList_toVec (length_of_read_nextScalars h)⟩
  rw [vecSlot, read_mapM, h]
  rfl

/-- A round polynomial's wire, read as the polynomial it decodes to: its wire is the wire read. -/
theorem refines_polySlot {d : ℕ} (hd : 0 < d) (claim : Thunk E) (e : Thunk (Option E)) :
    Refines (fun w c ↦ RoundPoly.encode e.get c = w) (historyOps.nextScalars d)
      (polySlot d claim e) := by
  intro l w r h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
    (RoundPoly.isSome_decode hd claim.get e.get (length_of_read_nextScalars h))
  refine ⟨c, ?_, RoundPoly.encode_decode hc⟩
  rw [polySlot, read_bind, h, Option.bind_some]
  simp only [hc]
  rfl

/-- `k + 1` challenges read by the walk are the first `k`, then the last. -/
theorem samples_succ' {n : Type → Type} [Monad n] [LawfulMonad n] (ops : ChainOps n) :
    ∀ k, samples ops (k + 1) = do
      let xs ← samples ops k
      let x ← ops.sample
      return xs ++ [x]
  | 0 => by simp [samples]
  | k + 1 => by
    conv_lhs => rw [samples, samples_succ' ops k]
    conv_rhs => rw [samples]
    simp

/-- `k` challenges, read as the walk reads them and as a run of draws. -/
theorem refines_draws : ∀ k : ℕ,
    Refines (fun xs t ↦ drawsList k t = xs) (samples historyOps k)
      (SlotDecoder.draws historyOps.sample k).toSlot
  | 0 => fun l x r h ↦ by
    cases h
    exact ⟨_, rfl, rfl⟩
  | k + 1 => by
    rw [samples_succ', toSlot_draws_succ]
    refine Refines.bind (refines_draws k) fun xs t h ↦
      Refines.bind (Refines.refl _) fun x y hxy ↦ Refines.pure ?_
    subst hxy
    simp only [drawsList, FullTranscript.append_fst, FullTranscript.append_snd, h]
    rfl

/-- Runs of rounds, read as the walk reads them and as the decoder decodes them: the wires the
transcript carries are the walk's, the coefficient at `drop` left out where the round's weight
drops it. -/
theorem refines_roundsDec {d : ℕ} (hd : 0 < d) (eq? : ℕ → Option E) (drop : ℕ) :
    ∀ (m : ℕ) (σ : Thunk E × ℕ),
      (∀ j, σ.2 ≤ j → j < σ.2 + m → RoundPoly.dropped (eq? j) = drop) →
      Refines (fun rs t ↦ roundsWire drop m t = rs) (readRounds historyOps d m)
        (roundsDec d eq? σ m).toSlot
  | 0, σ, _ => fun l x r h ↦ by
    cases h
    exact ⟨_, rfl, rfl⟩
  | m + 1, σ, hdrop => by
    rw [roundsDec, toSlot_rounds_succ]
    simp only [readRounds, readRound, bind_assoc, pure_bind]
    refine Refines.bind (refines_polySlot hd _ _) fun w p hwp ↦
      Refines.bind (Refines.refl _) fun c c' hc ↦ ?_
    subst hc
    refine Refines.bind (refines_roundsDec hd eq? drop m _ fun j h₁ h₂ ↦
      hdrop j (by simp only [roundNext] at h₁; omega) (by simp only [roundNext] at h₂; omega))
      fun rs t h ↦ Refines.pure ?_
    simp only [roundsWire, FullTranscript.append_fst, FullTranscript.append_snd, h, roundWire,
      polyWire]
    congr 1
    rw [← hwp]
    show (⟨p.toList.eraseIdx drop, c⟩ : Round) =
      ⟨p.toList.eraseIdx (RoundPoly.dropped (eq? σ.2)), c⟩
    rw [hdrop σ.2 le_rfl (by omega)]

/-- Two programs of two steps each, related as pairs, are related through any map of the pairs. -/
theorem Refines.bind_pair {α β γ α' β' γ' : Type} {R : α × β → α' × β' → Prop}
    {R₂ : γ → γ' → Prop} {A : Slot Reading α} {B : α → Slot Reading β} {A' : Slot Reading α'}
    {B' : α' → Slot Reading β'} {F : α → β → γ} {G : α' → β' → γ'}
    (h : Refines R (do let a ← A; let b ← B a; return (a, b))
      (do let a ← A'; let b ← B' a; return (a, b)))
    (hF : ∀ p q, R p q → R₂ (F p.1 p.2) (G q.1 q.2)) :
    Refines R₂ (do let a ← A; let b ← B a; return F a b)
      (do let a ← A'; let b ← B' a; return G a b) := by
  have e₁ : (do let a ← A; let b ← B a; return F a b) =
      (do let p ← (do let a ← A; let b ← B a; return (a, b)); return F p.1 p.2) := by
    simp only [bind_assoc, pure_bind]
  have e₂ : (do let a ← A'; let b ← B' a; return G a b) =
      (do let p ← (do let a ← A'; let b ← B' a; return (a, b)); return G p.1 p.2) := by
    simp only [bind_assoc, pure_bind]
  rw [e₁, e₂]
  exact Refines.bind h fun p q hpq ↦ Refines.pure (hF p q hpq)

theorem length_drawsList : ∀ (k : ℕ) (t : (draws E k).FullTranscript), (drawsList k t).length = k
  | 0, _ => rfl
  | k + 1, t => by simp [drawsList, length_drawsList k]

theorem length_roundsChals {d : ℕ} :
    ∀ (m : ℕ) (t : (roundsSpec E d m).FullTranscript), (roundsChals m t).length = m
  | 0, _ => rfl
  | m + 1, t => by simp [roundsChals, length_roundsChals m]

/-- A decoder of a schedule of no round reads nothing. -/
theorem exists_read_toSlot_of_zero {n : ℕ} {pSpec : ProtocolSpec n} (D : SlotDecoder Reading pSpec)
    (hn : n = 0) (l : List Reading) : ∃ t, D.toSlot.read l = some (t, l) := by
  subst hn
  exact ⟨_, rfl⟩

/-- A decoder of one round, then anything after, reads as its slot, then what comes after. -/
theorem Refines.single_bind {β γ γ' : Type} {pSpec : ProtocolSpec 1}
    {R₀ : β → pSpec.«Type» 0 → Prop}
    {R : γ → γ' → Prop} {s : Slot Reading β} {s' : Slot Reading (pSpec.«Type» 0)}
    {K : β → Slot Reading γ} {K' : pSpec.FullTranscript → Slot Reading γ'} (h : Refines R₀ s s')
    (hK : ∀ x y, R₀ x y → Refines R (K x) (K' (oneTranscript y))) :
    Refines R (s >>= K) ((single s').toSlot >>= K') := by
  rw [toSlot_single, bind_map_left]
  exact Refines.bind h hK

/-- Appended decoders, then anything after, read as the first, then the second, then what comes
after. -/
theorem Refines.append_bind {γ γ' : Type} {R : γ → γ' → Prop} {m n : ℕ} {pSpec₁ : ProtocolSpec m}
    {pSpec₂ : ProtocolSpec n} (D₁ : SlotDecoder Reading pSpec₁)
    (D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂) {s : Slot Reading γ}
    {K' : (pSpec₁ ++ₚ pSpec₂).FullTranscript → Slot Reading γ'}
    (h : Refines R s (D₁.toSlot >>= fun t₁ ↦ (D₂ t₁).toSlot >>= fun t₂ ↦ K' (t₁ ++ₜ t₂))) :
    Refines R s ((D₁.append D₂).toSlot >>= K') := by
  rw [toSlot_append]
  simpa only [bind_assoc, pure_bind] using h

/-- A slot, then anything after, read as itself. -/
theorem Refines.self_bind {β γ γ' : Type} {R : γ → γ' → Prop} (s : Slot Reading β)
    {K : β → Slot Reading γ} {K' : β → Slot Reading γ'} (hK : ∀ x, Refines R (K x) (K' x)) :
    Refines R (s >>= K) (s >>= K') :=
  Refines.bind (Refines.refl s) fun x _ h ↦ h ▸ hK x

/-- Two reads, then anything after, read as the pair of them, then what comes after. -/
theorem Refines.pair_left {α β γ γ' : Type} {R : γ → γ' → Prop} {s₁ : Slot Reading α}
    {s₂ : Slot Reading β} {K : α → β → Slot Reading γ} {T : Slot Reading γ'}
    (h : Refines R ((do let a ← s₁; let b ← s₂; return (a, b)) >>= fun p ↦ K p.1 p.2) T) :
    Refines R (do let a ← s₁; let b ← s₂; K a b) T := by
  simpa only [bind_assoc, pure_bind] using h

/-- A list of length `n` is its entries, padded with zeros. -/
theorem ofFn_getD {n : ℕ} {l : List E} (h : l.length = n) :
    List.ofFn (fun i : Fin n ↦ l.getD i 0) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

end Reads

/-! ## The bus phase -/

section Bus

open Slot

/-- A layer's descendants, read as three runs of scalars, then anything after. -/
theorem refines_childrenSlot {γ γ' : Type} {R : γ → γ' → Prop} (ρ : ℕ)
    {K : List E → List E → List E → Slot Reading γ}
    {K' : (Fin 3 → Vector E (2 ^ ρ)) → Slot Reading γ'}
    (hK : ∀ a b c (ch : Fin 3 → Vector E (2 ^ ρ)),
      List.ofFn (fun i : Fin 3 ↦ (ch i).toList) = [a, b, c] → Refines R (K a b c) (K' ch)) :
    Refines R
      (do
        let a ← historyOps.nextScalars (2 ^ ρ)
        let b ← historyOps.nextScalars (2 ^ ρ)
        let c ← historyOps.nextScalars (2 ^ ρ)
        K a b c)
      (do
        let ch ← childrenSlot ρ
        K' ch) := by
  simp only [childrenSlot, bind_assoc, pure_bind]
  exact Refines.bind (refines_vecSlot _) fun a va ha ↦ Refines.bind (refines_vecSlot _)
    fun b vb hb ↦ Refines.bind (refines_vecSlot _) fun c vc hc ↦
      hK a b c _ (by simp [List.ofFn_succ, ha, hb, hc])

/-- The decoder of a layer as one slot: the combiner, the rounds, the descendants and the
combination challenges. -/
theorem toSlot_layerDec (st : GkrState) (ρ m : ℕ) :
    (layerDec st ρ m).toSlot = do
      let x ← historyOps.sample
      let rs ← (roundsDec (2 ^ ρ) (fun j ↦ st.get.1[j]?)
        (Thunk.mk fun _ ↦ powerBatch st.get.2 x, 0) m).toSlot
      let ch ← childrenSlot ρ
      let u ← (SlotDecoder.draws historyOps.sample ρ).toSlot
      return ((oneTranscript (pSpec := draw E) x ++ₜ rs) ++ₜ
        oneTranscript (pSpec := say (Fin 3 → Vector E (2 ^ ρ))) ch) ++ₜ u := by
  simp only [layerDec, toSlot_append, toSlot_single, bind_map_left, bind_assoc, pure_bind]
  rfl

/-- **A layer**, read as the walk reads it (its combiner before it, the one after it left to the
rest) and as the decoder decodes it, then anything after: the combiner, the rounds, the descendants
and the combination challenges are the walk's. The point the layer starts from has as many
coordinates as its depth. -/
theorem refines_layerDec {γ γ' : Type} {R : γ → γ' → Prop} (st : GkrState) (ρ m : ℕ)
    (hst : st.get.1.length = m)
    (K : E → List Round → List E → List E → List E → List E → Slot Reading γ)
    (K' : (stepSpec E 3 ρ m).FullTranscript → Slot Reading γ')
    (hK : ∀ c rounds a b c' combos t, layerCombiner t = c → roundsWire 0 m t.fst.fst.snd = rounds →
      List.ofFn (fun i : Fin 3 ↦ (msgOf t.fst.snd i).toList) = [a, b, c'] →
      drawsList ρ t.snd = combos → Refines R (K c rounds a b c' combos) (K' t)) :
    Refines R
      (do
        let c ← historyOps.sample
        let rounds ← readRounds historyOps (2 ^ ρ) m
        let a ← historyOps.nextScalars (2 ^ ρ)
        let b ← historyOps.nextScalars (2 ^ ρ)
        let c' ← historyOps.nextScalars (2 ^ ρ)
        let combos ← samples historyOps ρ
        K c rounds a b c' combos)
      (do
        let t ← (layerDec st ρ m).toSlot
        K' t) := by
  rw [toSlot_layerDec]
  simp only [bind_assoc, pure_bind]
  refine Refines.bind (Refines.refl _) fun c x hx ↦ ?_
  subst hx
  refine Refines.bind (refines_roundsDec (Nat.two_pow_pos ρ) _ 0 m _ fun j _ hj ↦ ?_)
    fun rounds rs hrs ↦ ?_
  · simp [RoundPoly.dropped, List.getElem?_eq_getElem (show j < st.get.1.length by omega)]
  refine refines_childrenSlot ρ fun a b c' ch hch ↦
    Refines.bind (refines_draws ρ) fun combos u hu ↦ hK _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · simp [layerCombiner]
  · simpa using hrs
  · simpa using hch
  · simpa using hu

/-- **Layers of radix four**, read as the walk reads them (each layer's combiner after it, the first
before) and as the decoder decodes them (each layer's combiner first, the last after), then anything
after: the walk's layers. The point the layers start from has as many coordinates as the depth. -/
theorem refines_stepsDec {γ γ' : Type} {R : γ → γ' → Prop} : ∀ (k m : ℕ) (st : GkrState),
    st.get.1.length = m → ∀ (K : E → List GkrLayer → Slot Reading γ)
      (K' : (stepsSpec E 3 k m).FullTranscript → E → Slot Reading γ'),
      (∀ c ls t c', stepsWire k m t c' = (c, ls) → Refines R (K c ls) (K' t c')) →
      Refines R
        (do
          let c ← historyOps.sample
          let ls ← walkLayers historyOps (List.replicate k 2) m
          K c ls)
        (do
          let t ← (stepsDec st k m).toSlot
          let c ← historyOps.sample
          K' t c)
  | 0, m, st, _, K, K', hK => by
    intro l x r h
    simp only [List.replicate, walkLayers, pure_bind, read_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨c, l₁⟩, hc, hk⟩ := h
    obtain ⟨t, ht⟩ := exists_read_toSlot_of_zero (stepsDec st 0 m) rfl l
    obtain ⟨y, hy, hxy⟩ := hK c [] t c rfl l₁ x r hk
    refine ⟨y, ?_, hxy⟩
    rw [read_bind, ht, Option.bind_some, read_bind, hc, Option.bind_some]
    exact hy
  | k + 1, m, st, hst, K, K', hK => by
    show Refines R _ (do
      let t ← (SlotDecoder.append (pSpec₁ := stepSpec E 3 2 m) (pSpec₂ := stepsSpec E 3 k (m + 2))
        (layerDec st 2 m) fun t ↦ stepsDec (layerNext t) k (m + 2)).toSlot
      let c ← historyOps.sample
      K' t c)
    rw [toSlot_append]
    simp only [List.replicate, walkLayers, walkLayer, bind_assoc, pure_bind]
    refine refines_layerDec st 2 m hst _ _ fun c₀ rounds a b c combos t₁ h₀ hr hch hu ↦ ?_
    refine refines_stepsDec k (m + 2) _ ?_ _ _ fun comb ls t₂ c' h ↦ hK _ _ _ _ ?_
    · simp only [layerNext, get_thunk_mk, List.length_append, length_drawsList,
        length_roundsChals]
      omega
    simp only [stepsWire, FullTranscript.append_fst, FullTranscript.append_snd, h, h₀,
      layerWire, hr, hu, hch]

/-- A decoder of no round, then anything after, reads as what comes after. -/
theorem Refines.bind_zero {γ γ' : Type} {R : γ → γ' → Prop} {n : ℕ} {pSpec : ProtocolSpec n}
    (D : SlotDecoder Reading pSpec) (hn : n = 0) {s : Slot Reading γ}
    {K' : pSpec.FullTranscript → Slot Reading γ'} (h : ∀ t, Refines R s (K' t)) :
    Refines R s (D.toSlot >>= K') := by
  intro l x r hs
  obtain ⟨t, ht⟩ := exists_read_toSlot_of_zero D hn l
  obtain ⟨y, hy, hxy⟩ := h t l x r hs
  exact ⟨y, by rw [read_bind, ht, Option.bind_some, hy], hxy⟩

/-- **The grand product**, read as the walk reads it (the combiner after the roots, the layers each
with the combiner after it) and as the decoder decodes it, at a binary-layer count `r ≤ 1` and `k`
layers of radix four, then anything after. The point starts empty. -/
theorem refines_gkrAux {γ γ' : Type} {R : γ → γ' → Prop} (st : GkrState) (hst : st.get.1 = [])
    (r k : ℕ) (hr : r ≤ 1) (K : E → List GkrLayer → Slot Reading γ)
    (K' : (oddSpec E 3 r ++ₚ stepsSpec E 3 k r ++ₚ draw E).FullTranscript → Slot Reading γ')
    (hK : ∀ c ls t, oddWire r t.fst.fst (stepsWire k r t.fst.snd (drawOf t.snd)) = (c, ls) →
      Refines R (K c ls) (K' t)) :
    Refines R
      (do
        let c ← historyOps.sample
        let ls ← walkLayers historyOps ((if r = 1 then [1] else []) ++ List.replicate k 2) 0
        K c ls)
      (do
        let t ← ((SlotDecoder.append (SlotDecoder.append (oddDec st r) fun t ↦
          stepsDec (oddNext st r t) k r) fun _ ↦ single historyOps.sample).toSlot)
        K' t) := by
  rw [toSlot_append, toSlot_append, toSlot_single]
  simp only [bind_assoc, pure_bind, bind_map_left]
  rcases r with _ | r
  · simp only [Nat.zero_ne_one, ↓reduceIte, List.nil_append]
    refine Refines.bind_zero (oddDec st 0) rfl fun t₁ ↦ ?_
    refine refines_stepsDec k 0 (oddNext st 0 t₁) (by simp [oddNext, hst]) _ _
      fun c ls t₂ c' h ↦ hK _ _ _ ?_
    simpa [oddWire] using h
  · obtain rfl : r = 0 := by omega
    simp only [↓reduceIte, List.cons_append, List.nil_append, walkLayers, walkLayer, bind_assoc,
      pure_bind]
    refine refines_layerDec st 1 0 (by simp [hst]) _ _
      fun c₀ rounds a b c combos t₁ h₀ hrd hch hu ↦ ?_
    refine refines_stepsDec k 1 (oddNext st 1 t₁) ?_ _ _ fun comb ls t₂ c' h ↦ hK _ _ _ ?_
    · simp [oddNext, layerNext, length_drawsList, length_roundsChals]
    simp only [oddWire, FullTranscript.append_fst, FullTranscript.append_snd, drawOf_oneTranscript]
    erw [FullTranscript.append_fst, FullTranscript.append_snd]
    simp only [h, h₀, layerWire, hrd, hu, hch]

/-- **The grand product** for trees of `2 ^ μ` leaves, read as the walk reads it and as the
decoder decodes it, then anything after. -/
theorem refines_gkrDec {γ γ' : Type} {R : γ → γ' → Prop} (st : GkrState) (hst : st.get.1 = [])
    (μ : ℕ) (K : E → List GkrLayer → Slot Reading γ)
    (K' : (gkrSpec E 3 μ).FullTranscript → Slot Reading γ')
    (hK : ∀ c ls t, gkrWire μ t = (c, ls) → Refines R (K c ls) (K' t)) :
    Refines R
      (do
        let c ← historyOps.sample
        let ls ← walkLayers historyOps (gkrRadices μ) 0
        K c ls)
      (do
        let t ← (gkrDec st μ).toSlot
        K' t) :=
  refines_gkrAux st hst (μ % 2) (μ / 2) (by omega) K K' hK

/-- **The bus phase**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's wire. -/
theorem refines_busDec {γ γ' : Type} {R : γ → γ' → Prop} (I : M3Instance)
    (K : BusWire → Slot Reading γ) (K' : (busSpec I).FullTranscript → Slot Reading γ')
    (hK : ∀ w t, busWireOf I t = w → Refines R (K w) (K' t)) :
    Refines R (walkBus historyOps I.μBus I.busClaims >>= K) ((busDec I).toSlot >>= K') := by
  simp only [walkBus, bind_assoc, pure_bind]
  refine Refines.append_bind _ _ (Refines.append_bind _ _ (Refines.append_bind _ _ ?_))
  refine Refines.pair_left (Refines.single_bind (pSpec := draw ((Fin 4 → E) × E))
    (R₀ := fun (p : List E × E) fp ↦ List.ofFn fp.1 = p.1 ∧ fp.2 = p.2) ?_ ?_)
  · simp only [fingerprintSlot]
    refine Refines.bind (refines_self_of _ fun _ _ _ ↦ length_of_read_samples) fun a a' ha ↦
      Refines.self_bind _ fun b ↦ Refines.pure ⟨?_, rfl⟩
    obtain ⟨rfl, hl⟩ := ha
    exact ofFn_getD hl
  intro ⟨alpha, beta⟩ fp hfp
  refine Refines.pair_left (Refines.single_bind (pSpec := say (E × E)) (R₀ := Eq)
    (Refines.refl _) ?_)
  rintro ⟨shared, count⟩ _ rfl
  refine refines_gkrDec _ rfl I.μBus _ _ fun c ls g hg ↦ ?_
  refine Refines.single_bind (pSpec := say (Vector E I.busClaims)) (refines_vecSlot _)
    fun values vals hv ↦ hK _ _ ?_
  simp only [busWireOf, FullTranscript.append_fst, FullTranscript.append_snd,
    drawOf_oneTranscript, msgOf_oneTranscript, hg, hv, hfp.1, hfp.2]

end Bus

/-! ## The table sumcheck, the public input and the Flock phase -/

section Phases

open Slot

variable {γ γ' : Type} {R : γ → γ' → Prop}

/-- **The table sumcheck**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's wire. -/
theorem refines_tableDec (I : M3Instance) (s : Thunk (I.Stmt × BusOut I))
    (K : TableWire → Slot Reading γ) (K' : (tableSpec I).FullTranscript → Slot Reading γ')
    (hK : ∀ w t, tableWireOf I t = w → Refines R (K w) (K' t)) :
    Refines R (walkTables historyOps I.τmax I.tableColumns >>= K)
      ((tableDec I s).toSlot >>= K') := by
  simp only [walkTables, bind_assoc, pure_bind]
  refine Refines.append_bind _ _ (Refines.append_bind _ _ ?_)
  refine Refines.single_bind (pSpec := draw E) (R₀ := Eq) (Refines.refl _) ?_
  rintro xi _ rfl
  refine Refines.bind (refines_roundsDec (by norm_num) _ 1 _ _ fun _ _ _ ↦ rfl)
    fun rounds rs hrs ↦ ?_
  refine Refines.single_bind (pSpec := say (Vector E I.tableColumns)) (refines_vecSlot _)
    fun finals v hv ↦ hK _ _ ?_
  simp only [tableWireOf, FullTranscript.append_fst, FullTranscript.append_snd,
    drawOf_oneTranscript, msgOf_oneTranscript, hrs, hv]

/-- The public input's decoder as one slot. -/
theorem read_toSlot_pubDec (n : ℕ) (l : List Reading) :
    (pubDec n).toSlot.read l = (historyOps.sample.read l).bind fun p ↦
      ((historyOps.nextScalars n).read p.2).map fun q ↦
        ((fun | ⟨0, _⟩ => p.1 | ⟨1, _⟩ => q.1 : pubSpec.FullTranscript), q.2) := by
  have h0 : ∀ (h : 0 < 2) tr, (pubDec n).slot ⟨0, h⟩ tr = historyOps.sample := fun _ _ ↦ rfl
  have h1 : ∀ (h : 1 < 2) tr,
      (pubDec n).slot ⟨1, h⟩ tr = (historyOps.nextScalars n : Slot Reading (List E)) :=
    fun _ _ ↦ rfl
  simp only [read_toSlot, SlotDecoder.runFull, SlotDecoder.run, Option.bind_some, h0, h1]
  cases historyOps.sample.read l with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Option.bind_some]
    cases (historyOps.nextScalars n).read p.2 with
    | none => rfl
    | some q =>
      simp only [Option.map_some]
      congr 1
      refine Prod.ext (funext fun i ↦ ?_) rfl
      rcases i with ⟨_ | _ | i, hi⟩
      · rfl
      · rfl
      · omega

/-- **The public input**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's wire. -/
theorem refines_pubDec (n : ℕ) (K : PubWire → Slot Reading γ)
    (K' : pubSpec.FullTranscript → Slot Reading γ')
    (hK : ∀ w t, pubWireOf t = w → Refines R (K w) (K' t)) :
    Refines R (walkPub historyOps n >>= K) ((pubDec n).toSlot >>= K') := by
  intro l x r h
  simp only [walkPub, bind_assoc, pure_bind, read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rr, l₁⟩, h₁, ⟨vs, l₂⟩, h₂, h₃⟩ := h
  obtain ⟨y, hy, hxy⟩ :=
    hK ⟨rr, vs⟩ (fun | ⟨0, _⟩ => rr | ⟨1, _⟩ => vs : pubSpec.FullTranscript) rfl l₂ x r h₃
  refine ⟨y, ?_, hxy⟩
  rw [read_bind, read_toSlot_pubDec, h₁, Option.bind_some, h₂, Option.map_some, Option.bind_some]
  exact hy

/-- `a + b` rounds read by the walk are the first `a`, then the next `b`. -/
theorem readRounds_add {n : Type → Type} [Monad n] [LawfulMonad n] (ops : ChainOps n) (d b : ℕ) :
    ∀ a, readRounds ops d (a + b) = do
      let rs₁ ← readRounds ops d a
      let rs₂ ← readRounds ops d b
      return rs₁ ++ rs₂
  | 0 => by simp [readRounds]
  | a + 1 => by
    rw [Nat.add_right_comm, readRounds, readRounds_add ops d b a, readRounds]
    simp

theorem roundsNext_snd {d : ℕ} :
    ∀ (σ : Thunk E × ℕ) (m : ℕ) (t : (roundsSpec E d m).FullTranscript),
    (roundsNext σ m t).2 = σ.2 + m
  | _, 0, _ => rfl
  | σ, m + 1, t => by
    rw [roundsNext, roundsNext_snd]
    simp only [roundNext]
    omega

/-- **The Flock phase** for `2 ^ k` compressions, read as the walk reads it and as the decoder
decodes it, then anything after: the walk's wire. -/
theorem refines_flockDecOf (k : ℕ) (K : FlockWire → Slot Reading γ)
    (K' : (flockSpecOf k).FullTranscript → Slot Reading γ')
    (hK : ∀ w t, flockWireOf k t = w → Refines R (K w) (K' t)) :
    Refines R (walkFlock historyOps k >>= K) ((flockDecOf k).toSlot >>= K') := by
  simp only [walkFlock, readRounds_add, bind_assoc, pure_bind]
  refine Refines.append_bind _ _ (Refines.append_bind _ _ (Refines.append_bind _ _
    (Refines.append_bind _ _ (Refines.append_bind _ _ (Refines.append_bind _ _
    (Refines.append_bind _ _ (Refines.append_bind _ _ (Refines.append_bind _ _ ?_))))))))
  refine Refines.bind (refines_draws (k + 1)) fun point t₁ h₁ ↦ ?_
  refine Refines.single_bind (pSpec := say (Vector E 64)) (refines_vecSlot 64)
    fun skip v₂ h₂ ↦ ?_
  refine Refines.single_bind (pSpec := draw E) (R₀ := Eq) (Refines.refl _) ?_
  rintro zskip _ rfl
  refine Refines.bind (refines_roundsDec (by norm_num) _ 0 8 _ fun j _ hj ↦ ?_)
    fun zc₁ t₄ h₄ ↦ ?_
  · have hj : j < 8 := by simpa using hj
    have hb : j < (flockParams k).m + (flockParams k).κ := by
      simp only [flockParams, Flock.kIn]; omega
    simp [RoundPoly.dropped, zcWeights, Vector.getElem?_eq_getElem hb]
  refine Refines.bind (refines_roundsDec (by norm_num) _ 0 k _ fun j hj₁ hj₂ ↦ ?_)
    fun zc₂ t₅ h₅ ↦ ?_
  · rw [zcMid, roundsNext_snd] at hj₁ hj₂
    have hj : j < 8 + k := by simpa using hj₂
    have hb : j < (flockParams k).m + (flockParams k).κ := by
      simp only [flockParams, Flock.kIn]; omega
    simp [RoundPoly.dropped, zcWeights, Vector.getElem?_eq_getElem hb]
  refine Refines.single_bind (pSpec := say (Vector E 2)) (refines_vecSlot 2) fun ab v₆ h₆ ↦ ?_
  refine Refines.single_bind (pSpec := draw E) (R₀ := Eq) (Refines.refl _) ?_
  rintro alpha _ rfl
  refine Refines.bind (refines_roundsDec (by norm_num) _ 1 8 _ fun _ _ _ ↦ rfl)
    fun lin t₈ h₈ ↦ ?_
  refine Refines.single_bind (pSpec := say (Vector E 64)) (refines_vecSlot 64)
    fun slices v₉ h₉ ↦ ?_
  refine Refines.bind (refines_draws 6) fun ring t₁₀ h₁₀ ↦ hK _ _ ?_
  simp only [flockWireOf, FullTranscript.append_fst, FullTranscript.append_snd,
    drawOf_oneTranscript, msgOf_oneTranscript, h₁, h₂, h₄, h₅, h₆, h₈, h₉, h₁₀]

end Phases

/-! ## WHIR's opening -/

section Whir

open Slot

variable {γ γ' : Type} {R : γ → γ' → Prop}

/-- `k + 1` fold rounds read by the walk: the first challenge, then `k` rounds of a polynomial
and a challenge, then the last polynomial. -/
theorem walkFolds_eq {n : Type → Type} [Monad n] [LawfulMonad n] (ops : ChainOps n) :
    ∀ k, walkFolds ops (k + 1) = do
      let c ← ops.sample
      let rs ← readRounds ops 2 k
      let w ← ops.nextScalars 2
      return foldsWire c rs w
  | 0 => by simp [walkFolds, readRounds, foldsWire]
  | k + 1 => by
    conv_lhs => rw [walkFolds, walkFolds_eq ops k]
    conv_rhs => rw [readRounds, readRound]
    simp [foldsWire]

/-- `k + 1` tail rounds read by the walk: the first challenge, then `k` rounds of a polynomial and
a challenge. -/
theorem walkTail_eq {n : Type → Type} [Monad n] [LawfulMonad n] (ops : ChainOps n) :
    ∀ k, walkTail ops (k + 1) = do
      let c ← ops.sample
      let rs ← readRounds ops 2 k
      return foldsWire c rs []
  | 0 => by simp [walkTail, readRounds, foldsWire]
  | k + 1 => by
    conv_lhs => rw [walkTail, walkTail_eq ops k]
    conv_rhs => rw [readRounds, readRound]
    simp [foldsWire]

/-- The query positions, read as the walk reads them and as their slot does. -/
theorem refines_positionsSlot (b t : ℕ) :
    Refines (fun ps pos ↦ pos = positionsOf t b ps) (walkPositions historyOps b t t)
      (positionsSlot b t) := fun l x r h ↦
  ⟨positionsOf t b x, by rw [positionsSlot, read_mapM, h]; rfl, rfl⟩

/-- The shape of a final level as the verifier walks it. -/
abbrev finalShape (sh : Whir.Shape) (nf : ℕ) : LevelShape := ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩

/-- The shape of a level with a successor as the verifier walks it. -/
abbrev levelShape (sh sh' : Whir.Shape) (κ' : ℕ) : LevelShape :=
  ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩

/-- A step's transcript before the rest's, as a transcript of the list of steps. -/
abbrev seqCons {a : Step} {l : List Step} (t : a.spec.FullTranscript)
    (t' : (seqSpec l).FullTranscript) : (seqSpec (a :: l)).FullTranscript :=
  FullTranscript.append (pSpec₁ := a.spec) (pSpec₂ := seqSpec l) t t'

@[simp] theorem seqHead_seqCons {a : Step} {l : List Step} (t : a.spec.FullTranscript)
    (t' : (seqSpec l).FullTranscript) : seqHead (seqCons t t') = t :=
  FullTranscript.append_fst _ _

@[simp] theorem seqTail_seqCons {a : Step} {l : List Step} (t : a.spec.FullTranscript)
    (t' : (seqSpec l).FullTranscript) : seqTail (seqCons t t') = t' :=
  FullTranscript.append_snd _ _

/-- The wire of a final level's transcript, step by step. -/
theorem finalWire_mk {sh : Whir.Shape} {nf : ℕ}
    (t₁ : (Step.chal E inferInstance).spec.FullTranscript)
    (t₂ : (Step.rds E inferInstance 2 sh.lm1).spec.FullTranscript)
    (t₃ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t₄ : (Step.msg (Tab (nf + 1))).spec.FullTranscript) (t₅ : (Step.msg E).spec.FullTranscript)
    (t₆ : (Step.chal (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R))) inferInstance).spec.FullTranscript)
    (t₇ : (Step.chal E inferInstance).spec.FullTranscript) (t₈ : Step.skip.spec.FullTranscript)
    (t₉ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t₁₀ : Step.skip.spec.FullTranscript) (t₁₁ : (Step.chal E inferInstance).spec.FullTranscript)
    (t₁₂ : (Step.rds E inferInstance 2 nf).spec.FullTranscript)
    (t₁₃ : (seqSpec []).FullTranscript) :
    finalWire (sh := sh) (nf := nf) (seqCons t₁ (seqCons t₂ (seqCons t₃ (seqCons t₄ (seqCons t₅
      (seqCons t₆ (seqCons t₇ (seqCons t₈ (seqCons t₉ (seqCons t₁₀ (seqCons t₁₁
        (seqCons t₁₂ t₁₃)))))))))))) =
      ⟨foldsWire (drawOf t₁) (roundsWire 1 sh.lm1 t₂) (polyWire 1 (msgOf t₃)), none, [], 0, [],
        Vector.toList (msgOf t₄ : Vector E (2 ^ (nf + 1))), msgOf t₅, positionsList (drawOf t₆),
        drawOf t₇, polyWire 1 (msgOf t₉), foldsWire (drawOf t₁₁) (roundsWire 1 nf t₁₂) []⟩ := by
  simp only [finalWire, seqHead_seqCons, seqTail_seqCons]

/-- **The final level**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's level, viewed. -/
theorem refines_finalDec (sh : Whir.Shape) (nf : ℕ) (σ : Thunk E × Thunk (Vector E 3))
    (w : WordOf sh (nf + 1)) (K : WhirLevel → Slot Reading γ)
    (K' : (seqSpec (finalSteps sh nf)).FullTranscript → Slot Reading γ')
    (hK : ∀ l t, finalWire t = WhirLevel.view (finalShape sh nf) l → Refines R (K l) (K' t)) :
    Refines R (walkLevel historyOps (finalShape sh nf) >>= K)
      ((finalDec sh nf σ w).toDecoder.toSlot >>= K') := by
  simp only [walkLevel, ↓reduceIte, walkFolds_eq, walkTail_eq, bind_assoc, pure_bind]
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro c₁ _ rfl
  refine Refines.append_bind _ _ ?_
  refine Refines.bind (refines_roundsDec (d := 2) (by norm_num) (fun _ ↦ none) 1 sh.lm1 _
    fun _ _ _ ↦ rfl) fun rs t₂ h₂ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_polySlot (by norm_num) _ _)
    fun wl p₃ h₃ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_vecSlot (2 ^ (nf + 1)))
    fun residual v₄ h₄ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro nonce _ rfl
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_positionsSlot _ _)
    fun positions pos h₆ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro lam _ rfl
  refine Refines.append_bind _ _ ?_
  refine Refines.bind_zero _ rfl fun t₈ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_polySlot (by norm_num) _ _)
    fun qw p₉ h₉ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine Refines.bind_zero _ rfl fun t₁₀ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro c' _ rfl
  refine Refines.append_bind _ _ ?_
  refine Refines.bind (refines_roundsDec (d := 2) (by norm_num) (fun _ ↦ none) 1 nf _
    fun _ _ _ ↦ rfl) fun rs' t₁₂ h₁₂ ↦ ?_
  refine Refines.bind_zero _ rfl fun t₁₃ ↦ hK _ _ ?_
  subst h₂ h₃ h₄ h₉ h₁₂ h₆
  exact (finalWire_mk _ _ _ _ _ _ _ _ _ _ _ _ _).trans rfl

/-- The wire of a level's transcript, a level after it, step by step. -/
theorem levelWire_mk {sh sh' : Whir.Shape} {κ' : ℕ} {k : List Step}
    (t₁ : (Step.chal E inferInstance).spec.FullTranscript)
    (t₂ : (Step.rds E inferInstance 2 sh.lm1).spec.FullTranscript)
    (t₃ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t₄ : (Step.oracle (WordOf sh' κ') inferInstance).spec.FullTranscript)
    (t₅ : (Step.chals E inferInstance (Kap sh' κ')).spec.FullTranscript)
    (t₆ : (Step.msg E).spec.FullTranscript)
    (t₇ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t₈ : (Step.msg E).spec.FullTranscript)
    (t₉ : (Step.chal (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R))) inferInstance).spec.FullTranscript)
    (t₁₀ : (Step.chal E inferInstance).spec.FullTranscript) (t₁₁ : Step.skip.spec.FullTranscript)
    (t₁₂ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t₁₃ : Step.skip.spec.FullTranscript) (tr : (seqSpec k).FullTranscript) :
    levelWire (sh := sh) (sh' := sh') (κ' := κ') (seqCons t₁ (seqCons t₂ (seqCons t₃ (seqCons t₄
      (seqCons t₅ (seqCons t₆ (seqCons t₇ (seqCons t₈ (seqCons t₉ (seqCons t₁₀ (seqCons t₁₁
        (seqCons t₁₂ (seqCons t₁₃ tr))))))))))))) =
      (⟨foldsWire (drawOf t₁) (roundsWire 1 sh.lm1 t₂) (polyWire 1 (msgOf t₃)), some default,
        drawsList (Kap sh' κ') t₅, msgOf t₆, polyWire 1 (msgOf t₇), [], msgOf t₈,
        positionsList (drawOf t₉), drawOf t₁₀, polyWire 1 (msgOf t₁₂), []⟩, tr) := by
  simp only [levelWire, seqHead_seqCons, seqTail_seqCons]

/-- A slot, read as itself with its value mapped. -/
theorem refines_map_right {β β' : Type} (s : Slot Reading β) (g : β → β') :
    Refines (fun _ _ ↦ True) s (g <$> s) := fun l x r h ↦
  ⟨g x, by rw [read_mapM, h]; rfl, trivial⟩

/-- **A level with a successor**, read as the walk reads it and as the decoder decodes it, then
the rest of the opening: the walk's level, viewed, and the transcript of the rest. -/
theorem refines_levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    (cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k) (K : WhirLevel → Slot Reading γ)
    (K' : (seqSpec (levelSteps sh sh' κ' k)).FullTranscript → Slot Reading γ')
    (hK : ∀ l σ' (P : (seqSpec k).FullTranscript →
        (seqSpec (levelSteps sh sh' κ' k)).FullTranscript),
      (∀ tr, levelWire (P tr) = (WhirLevel.view (levelShape sh sh' κ') l, tr)) →
        Refines R (K l) ((cont σ').toDecoder.toSlot >>= fun tr ↦ K' (P tr))) :
    Refines R (walkLevel historyOps (levelShape sh sh' κ') >>= K)
      ((levelDec sh sh' κ' σ w next cont).toDecoder.toSlot >>= K') := by
  simp only [walkLevel, Bool.false_eq_true, ↓reduceIte, walkFolds_eq, bind_assoc, pure_bind,
    bind_map_left]
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro c₁ _ rfl
  refine Refines.append_bind _ _ ?_
  refine Refines.bind (refines_roundsDec (d := 2) (by norm_num) (fun _ ↦ none) 1 sh.lm1 _
    fun _ _ _ ↦ rfl) fun rs t₂ h₂ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_polySlot (by norm_num) _ _) fun wl p₃ h₃ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_map_right _ _) fun root _ _ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine Refines.bind (refines_draws _) fun ood t₅ h₅ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro oodValue _ rfl
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_polySlot (by norm_num) _ _) fun ow p₇ h₇ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro nonce _ rfl
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_positionsSlot _ _) fun positions pos h₉ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (Refines.refl _) ?_)
  rintro lam _ rfl
  refine Refines.append_bind _ _ ?_
  refine Refines.bind_zero _ rfl fun t₁₁ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine (Refines.single_bind (refines_polySlot (by norm_num) _ _) fun qw p₁₂ h₁₂ ↦ ?_)
  refine Refines.append_bind _ _ ?_
  refine Refines.bind_zero _ rfl fun t₁₃ ↦ ?_
  refine hK _ _ _ fun tr ↦ ?_
  subst h₂ h₃ h₅ h₇ h₉ h₁₂
  exact (levelWire_mk _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans rfl

/-- **A chain of levels**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's levels, viewed. -/
theorem refines_ladderDec : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Whir.Ladder sh κ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws : L.Words)
    (K : List WhirLevel → Slot Reading γ) (K' : (seqSpec L.steps).FullTranscript → Slot Reading γ'),
    (∀ ls t, ladderWire L t = List.zipWith WhirLevel.view L.shapes ls → Refines R (K ls) (K' t)) →
    Refines R (walkLevels historyOps L.shapes >>= K)
      ((ladderDec L σ w ws).toDecoder.toSlot >>= K')
  | _, _, .last sh nf, σ, w, _, K, K', hK => by
    simp only [Whir.Ladder.shapes, walkLevels, bind_assoc, pure_bind]
    exact refines_finalDec sh nf σ w _ K' fun l t h ↦
      hK [l] t (congrArg (fun x ↦ [x]) h)
  | _, _, @Whir.Ladder.cons sh sh' κ' L, σ, w, ws, K, K', hK => by
    simp only [Whir.Ladder.shapes, walkLevels, bind_assoc, pure_bind]
    refine refines_levelDec sh sh' κ' σ w ws.1 _ _ K' fun l σ' P hP ↦ ?_
    exact refines_ladderDec L σ' ws.1 ws.2 _ _ fun ls tr h ↦
      hK (l :: ls) (P tr) (by
        show (levelWire (P tr)).1 :: ladderWire L (levelWire (P tr)).2 = _
        rw [hP tr, h]; rfl)

/-- The wire of WHIR's opening transcript, step by step. -/
theorem whirWireOf_mk {sh : Whir.Shape} {κ : ℕ} (L : Whir.Ladder sh κ)
    (t₁ : Step.skip.spec.FullTranscript)
    (t₂ : (Step.msg (SumcheckRound.Message E 2)).spec.FullTranscript)
    (t : (seqSpec L.steps).FullTranscript) :
    whirWireOf L (seqCons t₁ (seqCons t₂ t)) = (polyWire 1 (msgOf t₂), ladderWire L t) := by
  simp only [whirWireOf, seqHead_seqCons, seqTail_seqCons]

/-- **WHIR's opening**, read as the walk reads it and as the decoder decodes it, then anything
after: the walk's reads, the levels viewed. -/
theorem refines_whirDec {sh : Whir.Shape} {κ : ℕ} (L : Whir.Ladder sh κ) (target : Thunk E)
    (w : WordOf sh κ) (ws : L.Words) (K : List E × List WhirLevel → Slot Reading γ)
    (K' : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript →
      Slot Reading γ')
    (hK : ∀ x t, whirWireOf L t = (x.1, List.zipWith WhirLevel.view L.shapes x.2) →
      Refines R (K x) (K' t)) :
    Refines R (walkWhir historyOps L.shapes >>= K)
      ((whirDec L target w ws).toDecoder.toSlot >>= K') := by
  simp only [walkWhir, bind_assoc, pure_bind]
  refine Refines.append_bind _ _ ?_
  refine Refines.bind_zero _ rfl fun t₁ ↦ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.single_bind (refines_polySlot (by norm_num) _ _) fun first p h ↦ ?_
  refine refines_ladderDec L _ w ws _ _ fun ls t hl ↦ hK _ _ ?_
  subst h
  exact (whirWireOf_mk L _ _ _).trans (by rw [hl]; rfl)

end Whir

/-! ## The compiled protocol -/

section Compiled

open Slot

variable {γ γ' : Type} {R : γ → γ' → Prop}

/-- The setup's reads with the announcement `ann` checked, as the commitment's slot reads them. -/
def walkSetupAt (ann : List E) : Slot Reading Digest := do
  let xs ← historyOps.nextScalars 8
  if xs = ann then historyOps.nextRoot else Slot.fail

/-- The chain walk after the setup on the instance `I`, from the commitment root: `nPub` public
values, the Flock phase for `2 ^ kF` compressions and the opening's levels `shs`. -/
def walkAfterSetup {n : Type → Type} [Monad n] (ops : ChainOps n) (I : M3Instance) (nPub kF : ℕ)
    (shs : List LevelShape) (root : Digest) : n Wire := do
  let bus ← walkBus ops I.μBus I.busClaims
  let table ← walkTables ops I.τmax I.tableColumns
  let pub ← walkPub ops nPub
  let flock ← walkFlock ops kF
  let lam ← ops.sample
  let (whirFirst, whir) ← walkWhir ops shs
  return ⟨root, bus, table, pub, flock, lam, whirFirst, whir⟩

/-- The chain walk is the setup, then the rest. -/
theorem walkChain_eq_setup {n : Type → Type} [Monad n] (ops : ChainOps n) (prog : Program)
    (s : Sizes) (input : PublicInput) (shs : List LevelShape) :
    walkChain ops prog s input shs = walkSetup ops >>= walkAfterSetup ops (leanVm prog s)
      (PublicInput.sentCount (leanVm prog s) ((leanVm prog s).publicLines input)) (s.τ 5) shs :=
  rfl

/-- Where the first eight scalars are `ann`, the setup reads as with the announcement checked. -/
theorem read_walkSetupAt {β : Type} (ann : List E) (f : Digest → Slot Reading β)
    {l r : List Reading} (h : (historyOps.nextScalars 8).read l = some (ann, r)) :
    (walkSetupAt ann >>= f).read l = (walkSetup historyOps >>= f).read l := by
  simp only [walkSetupAt, walkSetup, bind_assoc, read_bind, h, Option.bind_some, ↓reduceIte]

/-- A failing slot reads nowhere. -/
theorem Refines.fail_left {β β' : Type} {R : β → β' → Prop} (t : Slot Reading β') :
    Refines R (Slot.fail : Slot Reading β) t := fun _ _ _ h ↦ nomatch h

/-- The setup's reads with the announcement checked, read as the commitment's slot. -/
theorem refines_commitSlot {M : Type} (ann : List E) (w : M) :
    Refines (fun _ _ ↦ True) (walkSetupAt ann) (commitSlot ann w) := by
  refine Refines.bind (Refines.refl _) fun xs _ h ↦ ?_
  subst h
  by_cases hx : xs = ann
  · simp only [hx, ↓reduceIte]
    exact refines_map_right _ _
  · simp only [hx, ↓reduceIte]
    exact Refines.fail_left _

/-- **The Flock slot** of a region, read as the walk reads its phase and as the decoder decodes
it, then anything after: the walk's wire. -/
theorem refines_flockDec (I : M3Instance) (o : Option (FlockRegion I.toShape))
    (r : FlockRegion I.toShape) (ho : o = some r) (K : FlockWire → Slot Reading γ)
    (K' : (flockSpecOpt I o).FullTranscript → Slot Reading γ')
    (hK : ∀ w t, flockWireOpt I o t = w → Refines R (K w) (K' t)) :
    Refines R (walkFlock historyOps r.kBatch >>= K) ((flockDec I o).toSlot >>= K') := by
  subst ho
  exact refines_flockDecOf r.kBatch K K' hK

/-- The wire of a transcript of the compiled protocol, phase by phase. -/
theorem wireOf_mk (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Whir.Ladder sh κ)
    (t₁ : (commitWordSpec sh κ).FullTranscript) (t₂ : (busSpec I).FullTranscript)
    (t₃ : (tableSpec I).FullTranscript) (t₄ : pubSpec.FullTranscript)
    (t₅ : (flockSpec I).FullTranscript) (t₆ : openingSpec.FullTranscript)
    (t₇ : (!p[] : ProtocolSpec 0).FullTranscript)
    (t₈ : (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).FullTranscript) :
    wireOf I L (((((((t₁ ++ₜ t₂) ++ₜ t₃) ++ₜ t₄) ++ₜ t₅) ++ₜ t₆) ++ₜ t₇) ++ₜ t₈) =
      ⟨default, busWireOf I t₂, tableWireOf I t₃, pubWireOf t₄, flockWireOpt I I.flock t₅,
        drawOf t₆, (whirWireOf L t₈).1, (whirWireOf L t₈).2⟩ := by
  simp only [wireOf, FullTranscript.append_fst, FullTranscript.append_snd]

/-- **The compiled protocol**, read as the walk reads it after a checked announcement and as the
decoder decodes it: the transcript's wire is the walk's, viewed. -/
theorem refines_compiledDec (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)
    (ann : List E) (c : Chain) (W : Words c) (r : FlockRegion I.toShape) (hr : I.flock = some r) :
    Refines (fun w t ↦ wireOf I c.ladder t = Wire.view c.ladder.shapes w)
      (walkSetupAt ann >>= walkAfterSetup historyOps I
        (PublicInput.sentCount I (I.publicLines input)) r.kBatch c.ladder.shapes)
      (compiledDec I h input ann c W).toSlot := by
  rw [← bind_pure (compiledDec I h input ann c W).toSlot]
  unfold compiledDec frontDec
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.append_bind _ _ ?_
  refine Refines.single_bind (refines_commitSlot ann W.level0) fun root t₁ _ ↦ ?_
  simp only [walkAfterSetup]
  refine refines_busDec I _ _ fun bus t₂ h₂ ↦ ?_
  refine refines_tableDec I _ _ _ fun table t₃ h₃ ↦ ?_
  refine refines_pubDec _ _ _ fun pub t₄ h₄ ↦ ?_
  refine refines_flockDec I I.flock r hr _ _ fun flock t₅ h₅ ↦ ?_
  refine Refines.single_bind (pSpec := openingSpec) (R₀ := Eq) (Refines.refl _) ?_
  rintro lam _ rfl
  refine Refines.bind_zero _ rfl fun t₇ ↦ ?_
  refine refines_whirDec c.ladder _ _ _ _ _ fun x t₈ h₈ ↦ ?_
  obtain ⟨whirFirst, whir⟩ := x
  refine Refines.pure ?_
  refine (wireOf_mk I c.ladder _ _ _ _ _ _ _ _).trans ?_
  rw [h₂, h₃, h₄, h₅, h₈]
  rfl

end Compiled

/-! ## The history of a walk decodes -/

section Deployed

open Slot

/-- A scalar read off a history is its stream's first. -/
theorem streamOf_of_read_nextScalar {l : List Reading} {x : E} {r : List Reading}
    (h : historyOps.nextScalar.read l = some (x, r)) : streamOf l = x :: streamOf r := by
  rcases l with _ | ⟨⟨b, d⟩, l⟩
  · exact nomatch h
  · cases b with
    | observe y =>
      simp only [historyOps, read_next_cons, scalarOf, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | squeeze => exact nomatch h
    | nonce n => exact nomatch h

/-- `k` scalars read off a history are its stream's first `k`. -/
theorem streamOf_of_read_nextScalars :
    ∀ {k : ℕ} {l : List Reading} {xs : List E} {r : List Reading},
      (historyOps.nextScalars k).read l = some (xs, r) → streamOf l = xs ++ streamOf r
  | 0, _, _, _, h => by
    simp only [ChainOps.nextScalars, read_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | k + 1, l, xs, r, h => by
    simp only [ChainOps.nextScalars, read_bind, Option.bind_eq_some_iff, read_pure,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨x, l₁, hx, ys, l₂, hys, rfl, rfl⟩ := h
    rw [streamOf_of_read_nextScalar hx, streamOf_of_read_nextScalars hys, List.cons_append]

variable (prog : Program) (input : PublicInput) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- **The walk's history decodes**: if the chain walk at leanVM's chain reads the whole of a
history whose first eight scalars are the announcement, the history decodes, with any words, to a
transcript whose wire is the walk's, viewed. -/
theorem walkChain_decodes (W : LeanWords prog s hs ρ hρ) {hist : List Reading} {w : Wire}
    (hw : (walkChain historyOps prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes).read
      hist = some (w, []))
    (hann : (streamOf hist).take 8 = announcement s ρ) :
    ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
      wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
        Wire.view (leanIsaChain prog s hs ρ hρ).ladder.shapes w := by
  rw [walkChain_eq_setup] at hw
  have hw₁ := hw
  simp only [walkSetup, bind_assoc, read_bind, Option.bind_eq_some_iff] at hw₁
  obtain ⟨⟨xs, l₁⟩, hxs, -⟩ := hw₁
  have hx : xs = announcement s ρ := by
    rw [← hann, streamOf_of_read_nextScalars hxs, List.take_left' (length_of_read_nextScalars hxs)]
  subst hx
  rw [← read_walkSetupAt _ _ hxs] at hw
  obtain ⟨tr, htr, hrel⟩ := refines_compiledDec (leanVm prog s) (leanIsa_conditions _ prog s)
    input (announcement s ρ) (leanIsaChain prog s hs ρ hρ) W
    (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl hist w [] hw
  refine ⟨tr, (decoder prog input s hs ρ hρ W).decode_eq_some.mpr ?_, hrel⟩
  rw [read_toSlot] at htr
  exact htr

/-- **A logged walk's history decodes**: if the logged chain walk at leanVM's chain succeeds from a
stream whose first eight scalars are the announcement, the history it logged decodes, with any
words, to a transcript whose wire is the walk's, viewed. -/
theorem walkChainLogged_decodes (W : LeanWords prog s hs ρ hρ) {H : List UInt8 → Id Digest}
    {st st' : ReaderState PrunedMerklePaths} {w : Wire} {hist : List Reading}
    (h : walkChainLogged prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes H st =
      .ok ((w, hist), st'))
    (hann : st.stream.take 8 = announcement s ρ) :
    ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
      wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
        Wire.view (leanIsaChain prog s hs ρ hρ).ladder.shapes w := by
  obtain ⟨hw, hst⟩ := walkChain_history H h
  refine walkChain_decodes prog input s hs ρ hρ W hw ?_
  have hw₁ := hw
  rw [walkChain_eq_setup] at hw₁
  simp only [walkSetup, bind_assoc, read_bind, Option.bind_eq_some_iff] at hw₁
  obtain ⟨⟨xs, l₁⟩, hxs, -⟩ := hw₁
  have h₈ := length_of_read_nextScalars hxs
  rw [hst, streamOf_of_read_nextScalars hxs, List.append_assoc,
    List.take_left' h₈] at hann
  rw [streamOf_of_read_nextScalars hxs, List.take_left' h₈, hann]

/-- **An accepted walk's history decodes**: if the chain walk on the proof reader at leanVM's chain
succeeds from a stream whose first eight scalars are the announcement, the logged walk succeeds
with the same wire, and its history decodes, with any words, to a transcript whose wire is the
walk's, viewed. -/
theorem walkChain_reader_decodes (W : LeanWords prog s hs ρ hρ) {H : List UInt8 → Id Digest}
    {st st' : ReaderState PrunedMerklePaths} {w : Wire}
    (h : runPlain (walkChain (readerOps H) prog s input
      (leanIsaChain prog s hs ρ hρ).ladder.shapes) st = .ok (w, st'))
    (hann : st.stream.take 8 = announcement s ρ) :
    ∃ hist, walkChainLogged prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes H st =
        .ok ((w, hist), st') ∧
      ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
        wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
          Wire.view (leanIsaChain prog s hs ρ hρ).ladder.shapes w := by
  obtain ⟨hist, hl⟩ := walkChainLogged_of_walkChain H h
  exact ⟨hist, hl, walkChainLogged_decodes prog input s hs ρ hρ W hl hann⟩

end Deployed

end DecodeChain

end

end LeanerVM.Protocol
