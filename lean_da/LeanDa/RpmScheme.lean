import LeanDa.Merkle
import LeanRpm.Keccak
import LeanRpm.Lemmas

/-!
# LeanDA's hashing and challenges over a permutation oracle

The random-permutation model (`LeanRpm`) instantiates LeanDA's hash `H` with Keccak-256, the
sponge over a permutation `π` of the 200-byte Keccak-f[1600] state, and the challenges' duplex
sponge `P` with `π` itself. The definitions of `LeanDa.Scheme` take `H` and `P` as functions; here
they are transcribed for oracles, in any monad (`Sponge.newM`, …, `membershipChallengesM`,
`walkM`, `verifyCellM`), and are the scheme's own for pure ones (`membershipChallengesM_id`,
`verifyCellM_id`).

**Lanes and bytes.** The sponge's state is `25` lanes of `K`, the permutation's `200` bytes; lane
`i` is bytes `8 i … 8 i + 7`, little endian (`laneBytes`, which is `kBytes`: `laneBytes_toList`),
as in Keccak-f[1600] (`LeanRpm.keccakF`, `lanesOfBytes`). `lanesToState` and `stateToLanes`
convert, and a duplexing writes the rate lanes `0 … 15` and keeps lanes `16 … 24`, that is bytes
`128 … 199`: the capacity and the last rate byte `135`, whose top bit no padded block has clear
(`LeanRpm.keccakNF`). So every permutation call of the challenges' sponge absorbs a non-final
block into the zero state or into an earlier answer (`duplexP_membershipChallengesR`): the duplex
discipline of the two-oracle transfer (`LeanRpm.keccak256_transfer2`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanRpm

namespace LeanDa

/-! ## Lanes and bytes -/

/-- **A lane's bytes**, little endian. -/
def laneBytes : K ≃ Vector UInt8 8 :=
  BF64.equivFin.trans <| (finCongr (show 2 ^ 64 = 256 ^ 8 by norm_num)).trans <|
    finFunctionFinEquiv.symm.trans <|
      (Equiv.arrowCongr (Equiv.refl _) LeanRpm.uInt8EquivFin.symm).trans
        (arrayVectorEquivFin UInt8 8).symm

/-- A lane's bytes are the crate's (`kBytes`, `as_bytes`). -/
theorem laneBytes_toList (a : K) : (laneBytes a).toList = kBytes a := by
  apply List.ext_getElem
  · simp [kBytes]
  intro t h1 h2
  simp only [Vector.getElem_toList, kBytes, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  simp only [laneBytes, Equiv.trans_apply, arrayVectorEquivFin, Equiv.coe_fn_symm_mk,
    Vector.getElem_ofFn, Equiv.arrowCongr_apply, Function.comp_apply]
  change ((finFunctionFinEquiv (m := 256) (n := 8)).symm _ ⟨t, _⟩ : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val]
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

/-- **The permutation's state of 25 lanes**: lane `i` at bytes `8 i … 8 i + 7`. -/
def lanesToState (L : Lanes) : KState := KState.ofBytes (L.toList.flatMap fun a ↦ (laneBytes a).toList)

/-- **The lanes of a permutation's state.** -/
def stateToLanes (s : KState) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦ laneBytes.symm (Vector.ofFn fun j : Fin 8 ↦ s.toBytes.getD (8 * i + j) 0)

/-- **The permutation on lanes** from a permutation of the state, in any monad. -/
def lanePerm {m : Type → Type} [Monad m] (π : KState → m KState) (L : Lanes) : m Lanes :=
  stateToLanes <$> π (lanesToState L)

/-- Byte `p` of lanes of eight bytes each is byte `p % 8` of lane `p / 8`. -/
theorem getD_flatMap_laneBytes (l : List K) (p : ℕ) :
    (l.flatMap fun a ↦ (laneBytes a).toList).getD p 0 =
      if h : p / 8 < l.length then (laneBytes l[p / 8])[p % 8] else 0 := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    by_cases hp : p < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hp)]
      have h0 : p / 8 = 0 := by omega
      simp [h0, Nat.mod_eq_of_lt hp, Vector.getElem?_eq_getElem hp]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), ← List.getD_eq_getElem?_getD]
      simp only [Vector.length_toList]
      rw [ih (p - 8)]
      have h1 : (p - 8) / 8 = p / 8 - 1 := by omega
      have h2 : (p - 8) % 8 = p % 8 := by omega
      simp only [h1, h2, List.length_cons]
      by_cases hl : p / 8 - 1 < l.length
      · have h3 : p / 8 < l.length + 1 := by omega
        simp only [hl, h3, ↓reduceDIte]
        rw [List.getElem_cons (by omega)]
        simp [show p / 8 ≠ 0 by omega]
      · have h3 : ¬ p / 8 < l.length + 1 := by omega
        simp [hl, h3]

theorem toBytes_getD_cap (s : KState) (j : Fin 64) : s.toBytes.getD (136 + j) 0 = s.2[j] := by
  rw [KState.toBytes, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp [show 136 + (j : ℕ) - (32 + 104) = j by omega]

theorem toBytes_getD_135 (s : KState) : s.toBytes.getD 135 0 = s.1.2[103] := by
  rw [KState.toBytes, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by simp)]
  simp

/-- Byte `p` of the state of lanes `L` is byte `p % 8` of lane `p / 8`. -/
theorem lanesToState_byte (L : Lanes) (p : ℕ) (hp : p < 200) :
    (L.toList.flatMap fun a ↦ (laneBytes a).toList).getD p 0 =
      (laneBytes L[p / 8])[p % 8] := by
  rw [getD_flatMap_laneBytes]
  simp only [Vector.length_toList, show p / 8 < 25 by omega, ↓reduceDIte, Vector.getElem_toList]

/-- Byte `p` of a state, read back from its lanes. -/
theorem laneBytes_stateToLanes (y : KState) (p : ℕ) (hp : p < 200) :
    (laneBytes (stateToLanes y)[p / 8])[p % 8] = y.toBytes.getD p 0 := by
  simp only [stateToLanes, Vector.getElem_ofFn, Equiv.apply_symm_apply]
  congr 1
  omega

/-- **The kept lanes keep the capacity and byte `135`**: a state whose lanes `16 … 24` are those of
`y` has `y`'s capacity and byte `135`. -/
theorem lanesToState_keep {L : Lanes} {y : KState}
    (h : ∀ i : Fin 25, 16 ≤ (i : ℕ) → L[i] = (stateToLanes y)[i]) :
    (lanesToState L).2 = y.2 ∧ (lanesToState L).1.2[103] = y.1.2[103] := by
  have hb : ∀ p, 128 ≤ p → p < 200 →
      (L.toList.flatMap fun a ↦ (laneBytes a).toList).getD p 0 = y.toBytes.getD p 0 := by
    intro p hp1 hp2
    rw [lanesToState_byte L p hp2, ← laneBytes_stateToLanes y p hp2]
    have := h ⟨p / 8, by omega⟩ (by simp; omega)
    simp only [Fin.getElem_fin] at this
    rw [this]
  refine ⟨Vector.ext fun j hj ↦ ?_, ?_⟩
  · simp only [lanesToState, KState.ofBytes, Vector.getElem_ofFn]
    rw [hb _ (by omega) (by omega), toBytes_getD_cap y ⟨j, hj⟩]
    rfl
  · simp only [lanesToState, KState.ofBytes, Vector.getElem_ofFn]
    rw [hb _ (by omega) (by omega), ← toBytes_getD_135 y]

/-! ## The challenges and the openings' verification, over oracles -/

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (P : Lanes → m Lanes)

/-- The lanes a duplexing permutes: the waiting scalars over the rate, the rest of the rate zero,
the capacity kept (`Sponge.duplex`). -/
def duplexInput (s : Sponge) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < rateLanes then (rateWords s.pending).getD i 0 else s.state[i]

/-- The lanes of a fresh sponge (`Sponge.new`). -/
def newInput (iv publicInput : Digest) : Lanes :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then word iv i else if (i : ℕ) < 8 then word publicInput (i - 4) else 0

/-- `Sponge.new` over an oracle. -/
def Sponge.newM (iv publicInput : Digest) : m Sponge := do
  let state ← P (newInput iv publicInput)
  pure ⟨state, []⟩

/-- `Sponge.fromLabel` over oracles. -/
def Sponge.fromLabelM (label : List UInt8) : m Sponge := do
  let iv ← H label
  Sponge.newM P iv (Vector.replicate 32 0)

/-- `Sponge.duplex` over an oracle. -/
def Sponge.duplexM (s : Sponge) : m Sponge := do
  let state ← P (duplexInput s)
  pure ⟨state, []⟩

/-- `Sponge.absorb` over an oracle. -/
def Sponge.absorbM (s : Sponge) (x : E) (tag : K) : m Sponge :=
  (if s.pending.length = rateScalars then Sponge.duplexM P s else pure s) >>= fun s ↦
    pure ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- `Sponge.observe` over an oracle. -/
def Sponge.observeM (s : Sponge) (x : E) : m Sponge := Sponge.absorbM P s x dsObserve

/-- `Sponge.sample` over an oracle. -/
def Sponge.sampleM (s : Sponge) : m (E × Sponge) := do
  let s ← Sponge.duplexM P s
  pure (ofLimbs s.state[0] s.state[1] s.state[2], s)

/-- `Sponge.samples` over an oracle. -/
def Sponge.samplesM : ℕ → Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, s => do
    let (z, s) ← Sponge.sampleM P s
    let zs ← Sponge.samplesM n s
    pure (z :: zs)

/-- **The challenges of a root** (`membershipChallenges`) over oracles. -/
def membershipChallengesM (root : Digest) : m (List E) := do
  let s ← Sponge.fromLabelM H P label
  let s ← Sponge.observeM P s (ofLimbs (word root 0) (word root 1) 0)
  let s ← Sponge.observeM P s (ofLimbs (word root 2) (word root 3) 0)
  Sponge.samplesM P logK s

/-- `walk` over an oracle. -/
def walkM : ℕ → Digest → List Digest → m Digest
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkM (idx / 2) d rest

/-- **Verification of a cell opening** (`verifyCell`) over an oracle: every hash of the climb is
computed, then the checks. -/
def verifyCellM (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : m Bool := do
  let d ← H (cellBytes x)
  let w ← walkM H (colIndex p) d τ.path
  let root ← H (pairBytes τ.rowRoot w)
  pure (decide (τ.path.length = 7 + logPad r) && decide (root = com))

end Monadic

section Pure

variable (H : List UInt8 → Digest) (P : Lanes → Lanes)

theorem samplesM_id (n : ℕ) (s : Sponge) :
    Sponge.samplesM (m := Id) (fun L ↦ pure (P L)) n s = Sponge.samples P n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Sponge.samplesM, Sponge.samples, ih]
    rfl

/-- **Over pure functions, the challenges are the crate's.** -/
theorem membershipChallengesM_id (root : Digest) :
    membershipChallengesM (m := Id) (fun a ↦ pure (H a)) (fun L ↦ pure (P L)) root =
      membershipChallenges H P root := by
  simp only [membershipChallengesM, membershipChallenges, ← samplesM_id]
  rfl

theorem walkM_id (idx : ℕ) (node : Digest) (path : List Digest) :
    walkM (m := Id) (fun a ↦ pure (H a)) idx node path = walk H idx node path := by
  induction path generalizing idx node with
  | nil => rfl
  | cons s rest ih =>
    simp only [walkM, walk, apply_ite H]
    exact ih _ _

/-- **Over a pure function, the verification is `verifyCell`.** -/
theorem verifyCellM_id (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) :
    verifyCellM (m := Id) (fun a ↦ pure (H a)) r com p x τ = verifyCell H r com p x τ := by
  simp only [verifyCellM, verifyCell]
  change (decide _ && decide (H (pairBytes τ.rowRoot (walkM (m := Id) _ _ _ _)) = com)) = _
  rw [walkM_id]
  rfl

end Pure

/-! ## The duplex discipline -/

/-- The two-oracle random-oracle model's oracles: coins, `H` and the direct calls `F`. -/
abbrev Rom2 := unifSpec + hfSpec (List UInt8) KDigest KState

/-- The hash `H` in the two-oracle model. -/
abbrev hR (a : List UInt8) : OracleComp Rom2 Digest :=
  hQuery (Msg := List UInt8) (Dg := KDigest) (E := KRest) (C := KCap) a

/-- The direct calls `F`, on lanes. -/
abbrev pR (L : Lanes) : OracleComp Rom2 Lanes :=
  lanePerm (fun x ↦ fQuery (Msg := List UInt8) (Dg := KDigest) x) L

/-- **The duplex discipline with a postcondition**: along every run, every direct call is
admissible after the earlier answers (`Duplex`), and every result satisfies `post` with the
answers so far. -/
def DuplexP {α : Type} (post : α → List KState → Prop) :
    OracleComp Rom2 α → List KState → Prop
  | .pure a, hist => post a hist
  | .liftBind (.inr (.inr x)) k, hist =>
      Admissible KState.zero keccakNF hist x ∧ ∀ y, DuplexP post (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexP post (k u) hist

theorem duplexP_pure {α : Type} {post : α → List KState → Prop} {a : α} {hist : List KState}
    (h : post a hist) : DuplexP post (pure a : OracleComp Rom2 α) hist := h

theorem duplexP_query_bind_F {α : Type} {post : α → List KState → Prop} (x : KState)
    (k : KState → OracleComp Rom2 α) (hist : List KState) :
    DuplexP post (liftM (Rom2.query (.inr (.inr x))) >>= k) hist ↔
      Admissible KState.zero keccakNF hist x ∧ ∀ y, DuplexP post (k y) (y :: hist) := Iff.rfl

theorem duplexP_query_bind_other {α : Type} {post : α → List KState → Prop}
    (t : Rom2.Domain) (ht : ∀ x, t ≠ .inr (.inr x)) (k : Rom2.Range t → OracleComp Rom2 α)
    (hist : List KState) :
    DuplexP post (liftM (Rom2.query t) >>= k) hist ↔ ∀ u, DuplexP post (k u) hist := by
  rcases t with n | a | x
  · exact Iff.rfl
  · exact Iff.rfl
  · exact absurd rfl (ht x)

/-- **Sequencing**: a computation with postcondition `Q`, then one with postcondition `R` from
every result and history satisfying `Q`. -/
theorem duplexP_bind {α β : Type} {Q : α → List KState → Prop} {R : β → List KState → Prop}
    {X : OracleComp Rom2 α} {f : α → OracleComp Rom2 β} {hist : List KState}
    (hX : DuplexP Q X hist) (hf : ∀ a hist', Q a hist' → DuplexP R (f a) hist') :
    DuplexP R (X >>= f) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => simpa using hf a hist hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with n | a | x
    · exact (duplexP_query_bind_other (.inl n) (by simp) _ hist).mpr fun u ↦
        ih u ((duplexP_query_bind_other (.inl n) (by simp) _ hist).mp hX u)
    · exact (duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mpr fun u ↦
        ih u ((duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mp hX u)
    · obtain ⟨hadm, hk⟩ := (duplexP_query_bind_F x k hist).mp hX
      exact (duplexP_query_bind_F x _ hist).mpr ⟨hadm, fun y ↦ ih y (hk y)⟩

theorem duplexP_mono {α : Type} {Q R : α → List KState → Prop} {X : OracleComp Rom2 α}
    {hist : List KState} (hX : DuplexP Q X hist) (h : ∀ a hist', Q a hist' → R a hist') :
    DuplexP R X hist := by
  simpa using duplexP_bind (f := pure) hX fun a hist' hq ↦ duplexP_pure (h a hist' hq)

/-- The duplex discipline is the discipline with the trivial postcondition. -/
theorem duplex_of_duplexP {α : Type} {X : OracleComp Rom2 α} {hist : List KState}
    {Q : α → List KState → Prop} (hX : DuplexP Q X hist) :
    Duplex KState.zero keccakNF X hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rcases t with n | a | x
    · exact fun u ↦ ih u ((duplexP_query_bind_other (.inl n) (by simp) _ hist).mp hX u)
    · exact fun u ↦ ih u ((duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mp hX u)
    · obtain ⟨hadm, hk⟩ := (duplexP_query_bind_F x k hist).mp hX
      exact ⟨hadm, fun y ↦ ih y (hk y)⟩

theorem duplexP_hR_bind {α : Type} {post : α → List KState → Prop} (a : List UInt8)
    (k : Digest → OracleComp Rom2 α) (hist : List KState) (hk : ∀ d, DuplexP post (k d) hist) :
    DuplexP post (hR a >>= k) hist :=
  (duplexP_query_bind_other (.inr (.inl a)) (by simp) k hist).mpr hk

theorem duplexP_fQuery_bind {α : Type} {post : α → List KState → Prop} (x : KState)
    (k : KState → OracleComp Rom2 α) (hist : List KState)
    (hadm : Admissible KState.zero keccakNF hist x) (hk : ∀ y, DuplexP post (k y) (y :: hist)) :
    DuplexP post (fQuery (Msg := List UInt8) (Dg := KDigest) x >>= k) hist :=
  (duplexP_query_bind_F x k hist).mpr ⟨hadm, hk⟩

theorem admissible_mono {hist hist' : List KState} {x : KState} (h : hist ⊆ hist')
    (hx : Admissible KState.zero keccakNF hist x) : Admissible KState.zero keccakNF hist' x := by
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, h hy, hxy⟩

theorem laneBytes_zero : laneBytes 0 = Vector.replicate 8 0 := by
  apply Vector.toList_inj.mp
  rw [laneBytes_toList]
  rfl

theorem stateToLanes_zero : stateToLanes KState.zero = Vector.replicate 25 0 := by
  apply Vector.ext
  intro i hi
  simp only [stateToLanes, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [Equiv.symm_apply_eq, laneBytes_zero]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  have : KState.zero.toBytes = List.replicate 200 0 := rfl
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- A sponge whose state is the lanes of an earlier answer. -/
def SpongeOK (hist : List KState) (s : Sponge) : Prop := ∃ y ∈ hist, s.state = stateToLanes y

/-- A duplexing permutes an admissible state. -/
theorem admissible_duplexInput {hist : List KState} {s : Sponge} (hs : SpongeOK hist s) :
    Admissible KState.zero keccakNF hist (lanesToState (duplexInput s)) := by
  obtain ⟨y, hy, hsy⟩ := hs
  have hk := lanesToState_keep (L := duplexInput s) (y := y) fun i hi ↦ by
    simp only [duplexInput, Vector.getElem_ofFn, rateLanes, Fin.getElem_fin,
      show ¬ (i : ℕ) < 16 by omega, ↓reduceIte, hsy]
  exact Or.inr ⟨y, hy, hk.1, keccakNF_blockTo y _ hk.2⟩

/-- A fresh sponge permutes an admissible state. -/
theorem admissible_newInput (hist : List KState) (iv publicInput : Digest) :
    Admissible KState.zero keccakNF hist (lanesToState (newInput iv publicInput)) := by
  have hk := lanesToState_keep (L := newInput iv publicInput) (y := KState.zero) fun i hi ↦ by
    simp only [newInput, Vector.getElem_ofFn, stateToLanes_zero, Vector.getElem_replicate,
      Fin.getElem_fin, show ¬ (i : ℕ) < 4 by omega, show ¬ (i : ℕ) < 8 by omega, ↓reduceIte]
  exact Or.inl ⟨hk.1, keccakNF_blockTo KState.zero _ hk.2⟩

/-- The postcondition of the sponge's steps: a good sponge, and the earlier answers kept. -/
def SpongePost (hist : List KState) (s : Sponge) (hist' : List KState) : Prop :=
  SpongeOK hist' s ∧ hist ⊆ hist'

theorem duplexP_pR {hist : List KState} {L : Lanes}
    (hadm : Admissible KState.zero keccakNF hist (lanesToState L)) :
    DuplexP (fun L' hist' ↦ (∃ y ∈ hist', L' = stateToLanes y) ∧ hist ⊆ hist') (pR L) hist := by
  rw [pR, lanePerm, map_eq_bind_pure_comp]
  exact duplexP_fQuery_bind _ _ hist hadm fun y ↦
    duplexP_pure ⟨⟨y, List.mem_cons_self, rfl⟩, List.subset_cons_self _ _⟩

theorem duplexP_newM (hist : List KState) (iv publicInput : Digest) :
    DuplexP (SpongePost hist) (Sponge.newM pR iv publicInput) hist := by
  refine duplexP_bind (duplexP_pR (admissible_newInput hist iv publicInput)) fun L hist' h ↦ ?_
  obtain ⟨⟨y, hy, rfl⟩, hsub⟩ := h
  exact duplexP_pure ⟨⟨y, hy, rfl⟩, hsub⟩

theorem duplexP_duplexM {hist : List KState} {s : Sponge} (hs : SpongeOK hist s) :
    DuplexP (SpongePost hist) (Sponge.duplexM pR s) hist := by
  refine duplexP_bind (duplexP_pR (admissible_duplexInput hs)) fun L hist' h ↦ ?_
  obtain ⟨⟨y, hy, rfl⟩, hsub⟩ := h
  exact duplexP_pure ⟨⟨y, hy, rfl⟩, hsub⟩

theorem SpongePost.trans {h₀ h₁ h₂ : List KState} {s : Sponge} (h01 : h₀ ⊆ h₁)
    (h : SpongePost h₁ s h₂) : SpongePost h₀ s h₂ := ⟨h.1, fun _ ha ↦ h.2 (h01 ha)⟩

theorem duplexP_absorbM {hist : List KState} {s : Sponge} (hs : SpongeOK hist s) (x : E)
    (tag : K) : DuplexP (SpongePost hist) (Sponge.absorbM pR s x tag) hist := by
  unfold Sponge.absorbM
  have h1 : DuplexP (SpongePost hist)
      (if s.pending.length = rateScalars then Sponge.duplexM pR s else pure s) hist := by
    split
    · exact duplexP_duplexM hs
    · exact duplexP_pure ⟨hs, List.Subset.refl _⟩
  exact duplexP_bind h1 fun s' hist' h ↦ duplexP_pure ⟨h.1, h.2⟩

theorem duplexP_samplesM (n : ℕ) {hist : List KState} {s : Sponge} (hs : SpongeOK hist s) :
    DuplexP (fun _ hist' ↦ hist ⊆ hist') (Sponge.samplesM pR n s) hist := by
  induction n generalizing hist s with
  | zero => exact duplexP_pure (List.Subset.refl _)
  | succ n ih =>
    unfold Sponge.samplesM Sponge.sampleM
    rw [bind_assoc]
    refine duplexP_bind (duplexP_duplexM hs) fun s' hist' h ↦ ?_
    simp only [pure_bind]
    exact duplexP_bind (ih h.1) fun zs hist'' h' ↦ duplexP_pure fun _ ha ↦ h' (h.2 ha)

/-- **The challenges' sponge follows the duplex discipline.** -/
theorem duplexP_membershipChallengesR (root : Digest) (hist : List KState) :
    DuplexP (fun _ hist' ↦ hist ⊆ hist') (membershipChallengesM hR pR root) hist := by
  unfold membershipChallengesM Sponge.fromLabelM
  rw [bind_assoc]
  refine duplexP_hR_bind _ _ hist fun iv ↦ ?_
  refine duplexP_bind (duplexP_newM hist iv _) fun s₁ h₁ hs₁ ↦ ?_
  refine duplexP_bind (duplexP_absorbM hs₁.1 _ _) fun s₂ h₂ hs₂ ↦ ?_
  refine duplexP_bind (duplexP_absorbM hs₂.1 _ _) fun s₃ h₃ hs₃ ↦ ?_
  exact duplexP_mono (duplexP_samplesM logK hs₃.1) fun _ h₄ h _ ha ↦
    h (hs₃.2 (hs₂.2 (hs₁.2 ha)))

end LeanDa
