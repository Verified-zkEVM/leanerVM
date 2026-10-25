/-
  LeanVM.Protocol.Rpm.Duplex

  The duplex discipline of the verifier and of the honest prover: every permutation query keeps
  lanes `16..24` of the zero state or of an earlier answer.
-/

import LeanVM.Protocol.LeanVM

/-!
# The duplex discipline

The transfer from the two-oracle random-oracle model to the random-permutation model
(`Common.keccak256_transfer2`) asks of the honest parties' direct calls of the permutation a
*duplex discipline* (`Common.Duplex`): every call absorbs a non-final block into the initial
state or into the answer of an earlier call, keeping the capacity. On leanVM's states this is
`DuplexVm`: every query `F x` keeps lanes `16..24` of the zero state or of an earlier answer
(`AdmissibleVm`); lane `16` holds the padding's last byte, lanes `17..24` the capacity.

leanVM's Fiat-Shamir sponge (`Statement/LeanVmVerifier.lean`) follows it: its seed is
`F (seedInput iv publicInput)`, zero from lane `8` on, and each later call is
`F (duplexInput sp)`, which overwrites lanes `0..15` and keeps lanes `16..24` of the sponge's
state, itself the seed or a later answer. Hence `duplexVm_verifier` and, for the honest prover
followed by the verifier, `duplexVm_honest`.

The proofs carry a postcondition (`DuplexP`): a computation follows the discipline from the
answers `hist`, and each of its outcomes satisfies `Q` with the answers at its end.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-! ## The discipline -/

/-- A direct call at `x` is admissible after the answers `hist` of earlier direct calls: `x`
keeps lanes `16..24` of the zero state or of an earlier answer. -/
def AdmissibleVm (hist : List KState) (x : KState) : Prop :=
  (∀ i : Fin 25, 16 ≤ i.val → x[i] = 0) ∨ ∃ y ∈ hist, ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]

/-- The duplex discipline of an oracle computation (as `Common.Duplex`,
`common/Common/Transfer2.lean`): along every run, every permutation query is admissible after
the answers of the earlier ones (newest first). -/
def DuplexVm {α : Type} : OracleComp HashSpec α → List KState → Prop
  | .pure _, _ => True
  | .liftBind (.inr x) k, hist => AdmissibleVm hist x ∧ ∀ y, DuplexVm (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexVm (k u) hist

/-- The duplex discipline with a postcondition: every permutation query is admissible, and every
outcome satisfies `Q` with the answers at the end of its run. -/
def DuplexP {α : Type} : OracleComp HashSpec α → List KState → (α → List KState → Prop) → Prop
  | .pure a, hist, Q => Q a hist
  | .liftBind (.inr x) k, hist, Q => AdmissibleVm hist x ∧ ∀ y, DuplexP (k y) (y :: hist) Q
  | .liftBind _ k, hist, Q => ∀ u, DuplexP (k u) hist Q

/-- A computation that queries the hash only. -/
def HOnly {α : Type} : OracleComp HashSpec α → Prop
  | .pure _ => True
  | .liftBind (.inr _) _ => False
  | .liftBind _ k => ∀ u, HOnly (k u)

section Rules

variable {α β : Type}

theorem admissibleVm_mono {h h' : List KState} (hs : h ⊆ h') {x : KState}
    (hx : AdmissibleVm h x) : AdmissibleVm h' x := by
  rcases hx with hx | ⟨y, hy, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, hs hy, hx⟩

theorem duplexVm_pure (a : α) (h : List KState) : DuplexVm (pure a : OracleComp HashSpec α) h :=
  trivial

theorem duplexP_pure {a : α} {h : List KState} {Q : α → List KState → Prop} (ha : Q a h) :
    DuplexP (pure a : OracleComp HashSpec α) h Q := ha

theorem duplexP_queryF_bind (x : KState) (k : KState → OracleComp HashSpec α) (h : List KState)
    (Q : α → List KState → Prop) :
    DuplexP (queryF x >>= k) h Q ↔ AdmissibleVm h x ∧ ∀ y, DuplexP (k y) (y :: h) Q :=
  Iff.rfl

theorem duplexP_queryH_bind (x : Bytes) (k : Digest → OracleComp HashSpec α) (h : List KState)
    (Q : α → List KState → Prop) :
    DuplexP (queryH x >>= k) h Q ↔ ∀ u, DuplexP (k u) h Q :=
  Iff.rfl

theorem duplexVm_query_bind (t : HashSpec.Domain) (k : HashSpec.Range t → OracleComp HashSpec α)
    (h : List KState) :
    DuplexVm (liftM (HashSpec.query t) >>= k) h ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexVm (k y) (y :: h)
      | .inl _ => ∀ u, DuplexVm (k u) h := by
  rcases t with x | x <;> exact Iff.rfl

theorem duplexP_query_bind (t : HashSpec.Domain) (k : HashSpec.Range t → OracleComp HashSpec α)
    (h : List KState) (Q : α → List KState → Prop) :
    DuplexP (liftM (HashSpec.query t) >>= k) h Q ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexP (k y) (y :: h) Q
      | .inl _ => ∀ u, DuplexP (k u) h Q := by
  rcases t with x | x <;> exact Iff.rfl

theorem hOnly_query_bind (t : HashSpec.Domain) (k : HashSpec.Range t → OracleComp HashSpec α) :
    HOnly (liftM (HashSpec.query t) >>= k) ↔
      match t with
      | .inr _ => False
      | .inl _ => ∀ u, HOnly (k u) := by
  rcases t with x | x <;> exact Iff.rfl

/-- The discipline without postcondition is the discipline with the trivial one. -/
theorem duplexVm_iff_duplexP (X : OracleComp HashSpec α) (h : List KState) :
    DuplexVm X h ↔ DuplexP X h fun _ _ ↦ True := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [duplexVm_query_bind, duplexP_query_bind]
    rcases t with x | x
    · exact forall_congr' fun u ↦ ih u h
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _)

/-- A weaker postcondition. -/
theorem DuplexP.mono {X : OracleComp HashSpec α} {h : List KState}
    {Q R : α → List KState → Prop} (hX : DuplexP X h Q) (hQR : ∀ a h', Q a h' → R a h') :
    DuplexP X h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact hQR a h hX
  | query_bind t k ih =>
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- **The answers only grow**: an outcome's answers contain the answers at the start. -/
theorem DuplexP.grow {X : OracleComp HashSpec α} {h : List KState}
    {Q : α → List KState → Prop} (hX : DuplexP X h Q) :
    DuplexP X h fun a h' ↦ Q a h' ∧ h ⊆ h' := by
  suffices ∀ h₀ : List KState, h₀ ⊆ h → DuplexP X h fun a h' ↦ Q a h' ∧ h₀ ⊆ h' from
    this h (List.Subset.refl h)
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact fun h₀ hs ↦ ⟨hX, hs⟩
  | query_bind t k ih =>
    intro h₀ hs
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u) h₀ hs
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y) h₀ (List.subset_cons_of_subset y hs)⟩

/-- **Sequencing.** -/
theorem DuplexP.bind {X : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    {h : List KState} {Q : α → List KState → Prop} {R : β → List KState → Prop}
    (hX : DuplexP X h Q) (hf : ∀ a h', Q a h' → DuplexP (f a) h' R) :
    DuplexP (X >>= f) h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => simpa using hf a h hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- **Monotonicity in the earlier answers.** -/
theorem DuplexP.of_subset {X : OracleComp HashSpec α} {h h' : List KState}
    {Q : α → List KState → Prop} (hX : DuplexP X h Q) (hs : h ⊆ h')
    (hQ : ∀ a h₁ h₂, h₁ ⊆ h₂ → Q a h₁ → Q a h₂) : DuplexP X h' Q := by
  induction X using OracleComp.inductionOn generalizing h h' with
  | pure a => exact hQ a h h' hs hX
  | query_bind t k ih =>
    rw [duplexP_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u) hs
    · exact ⟨admissibleVm_mono hs hX.1,
        fun y ↦ ih y (hX.2 y) (List.cons_subset_cons y hs)⟩

/-- **Monotonicity in the earlier answers**, without postcondition. -/
theorem DuplexVm.of_subset {X : OracleComp HashSpec α} {h h' : List KState} (hX : DuplexVm X h)
    (hs : h ⊆ h') : DuplexVm X h' := by
  rw [duplexVm_iff_duplexP] at hX ⊢
  exact hX.of_subset hs fun _ _ _ _ _ ↦ trivial

/-- **Sequencing** without postcondition: a disciplined computation, then disciplined
continuations from no answer. -/
theorem DuplexVm.bind {X : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    {h : List KState} (hX : DuplexVm X h) (hf : ∀ a, DuplexVm (f a) []) :
    DuplexVm (X >>= f) h := by
  rw [duplexVm_iff_duplexP] at hX ⊢
  exact hX.bind fun a h' _ ↦ (duplexVm_iff_duplexP _ _).mp ((hf a).of_subset (List.nil_subset _))

/-- A computation that only hashes keeps the discipline, and its answers. -/
theorem HOnly.duplexP {X : OracleComp HashSpec α} (hX : HOnly X) (h : List KState) :
    DuplexP X h fun _ h' ↦ h' = h := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [hOnly_query_bind] at hX
    rw [duplexP_query_bind]
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact hX.elim

theorem hOnly_pure (a : α) : HOnly (pure a : OracleComp HashSpec α) := trivial

theorem HOnly.bind {X : OracleComp HashSpec α} {f : α → OracleComp HashSpec β} (hX : HOnly X)
    (hf : ∀ a, HOnly (f a)) : HOnly (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [hOnly_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact hX

theorem hOnly_queryH (x : Bytes) : HOnly (queryH x) := by
  have : HOnly (queryH x >>= pure) := (hOnly_query_bind (.inl x) pure).mpr fun _ ↦ trivial
  simpa using this

theorem hOnly_mapM {γ : Type} (f : γ → OracleComp HashSpec β) (hf : ∀ c, HOnly (f c)) :
    ∀ l : List γ, HOnly (l.mapM f)
  | [] => trivial
  | c :: l => by
    rw [List.mapM_cons]
    exact (hf c).bind fun _ ↦ (hOnly_mapM f hf l).bind fun _ ↦ trivial

end Rules

/-! ## The sponge -/

theorem lane_eq_getElem_fin (a : KState) (i : Fin 25) : Keccak.lane a i = a[i] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?]

/-- A permutation of the sponge keeps lanes `16..24` of its state. -/
theorem admissibleVm_duplexInput {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) :
    AdmissibleVm h (duplexInput sp) := by
  refine Or.inr ⟨sp.state, hs, fun i hi ↦ ?_⟩
  have : ¬ (i.val < 16) := by omega
  simp [duplexInput, lane_eq_getElem_fin, this]

theorem duplexP_duplex {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) :
    DuplexP (duplex queryF sp) h fun sp' h' ↦ sp'.state ∈ h' := by
  simp only [duplex]
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_duplexInput hs, fun y ↦ List.mem_cons_self⟩

theorem duplexP_absorb {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) (x : E) (tag : ℕ) :
    DuplexP (Compile.absorb queryF sp x tag) h fun sp' h' ↦ sp'.state ∈ h' := by
  simp only [Compile.absorb]
  split
  · exact (duplexP_duplex hs).bind fun sp' h' hsp ↦ hsp
  · exact hs

theorem duplexP_squeeze {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) :
    DuplexP (squeeze queryF sp) h fun r h' ↦ r.2.state ∈ h' := by
  simp only [squeeze]
  exact (duplexP_duplex hs).bind fun sp' h' hsp ↦ hsp

/-! ## The verifier -/

theorem hOnly_climb : ∀ (node : Digest) (q : ℕ) (path : List Digest),
    HOnly (climb queryH node q path)
  | _, _, [] => trivial
  | node, q, s :: ss => by
    simp only [climb]
    split <;> exact (hOnly_queryH _).bind fun _ ↦ hOnly_climb _ _ ss

theorem hOnly_openOne (root : Digest) (height width q : ℕ) (o : Opening) :
    HOnly (openOne queryH root height width q o) := by
  simp only [openOne]
  split
  · exact (hOnly_queryH _).bind fun _ ↦ (hOnly_climb _ _ _).bind fun _ ↦ trivial
  · trivial

theorem hOnly_openAll (root : Digest) (height width : ℕ) :
    ∀ (qs : List ℕ) (os : List Opening), HOnly (openAll queryH root height width qs os)
  | [], _ => trivial
  | _ :: _, [] => trivial
  | q :: qs, o :: os => by
    simp only [openAll]
    refine (hOnly_openOne _ _ _ _ _).bind fun b ↦ ?_
    split
    · exact (hOnly_openAll root height width qs os).bind fun _ ↦ trivial
    · trivial

/-- **The compiled run keeps the discipline**, from a sponge whose state is an earlier answer. -/
theorem duplexP_run {α : Type} (P : Prog α) :
    ∀ (s : St) (h : List KState), s.sponge.state ∈ h →
      DuplexP (Compile.run queryH queryF P s) h fun _ _ ↦ True := by
  induction P with
  | ret a => intro s h _; trivial
  | fail => intro s h _; trivial
  | read k ih =>
    intro s h hs
    simp only [Compile.run]
    split
    · trivial
    · exact (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ih _ _ _ hsp
  | sample k ih =>
    intro s h hs
    simp only [Compile.run]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ hr
  | grind bits k ih =>
    intro s h hs
    simp only [Compile.run]
    split
    · trivial
    · refine (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ?_
      refine (duplexP_squeeze hsp).bind fun r h'' hr ↦ ?_
      split
      · exact ih _ _ hr
      · trivial
  | commit height width k ih =>
    intro s h hs
    simp only [Compile.run]
    split
    · refine (duplexP_absorb hs _ _).bind fun sp h' hsp ↦ ?_
      refine (duplexP_absorb hsp _ _).bind fun sp' h'' hsp' ↦ ?_
      split
      · exact ih _ _ hsp'
      · trivial
    · trivial
  | query i ps k ih =>
    intro s h hs
    simp only [Compile.run]
    split
    · trivial
    · refine ((hOnly_openAll _ _ _ _ _).duplexP h).bind fun r h' hh ↦ ?_
      subst hh
      split
      · exact ih _ _ _ hs
      · trivial

theorem duplexP_runProof (P : Prog Bool) {seed : KState} {h : List KState} (hs : seed ∈ h)
    (π : Proof) : DuplexP (runProof queryH queryF P seed π) h fun _ _ ↦ True := by
  simp only [runProof]
  refine (duplexP_run P _ h hs).bind fun r h' _ ↦ ?_
  split <;> trivial

theorem hOnly_fiatShamirIvWith (bytecode : List K) :
    HOnly (fiatShamirIvWith queryH bytecode) := by
  simp only [fiatShamirIvWith]
  exact (hOnly_queryH _).bind fun _ ↦ (hOnly_queryH _).bind fun _ ↦ hOnly_queryH _

/-- The seed's input is zero from lane `8` on. -/
theorem admissibleVm_seedInput (h : List KState) (iv publicInput : Digest) :
    AdmissibleVm h (seedInput iv publicInput) := by
  refine Or.inl fun i hi ↦ ?_
  have h4 : ¬ (i.val < 4) := by omega
  have h8 : ¬ (i.val < 8) := by omega
  simp [seedInput, h4, h8]

theorem duplexP_seedWith (bytecode : List K) (publicInput : Digest) (h : List KState) :
    DuplexP (seedWith queryH queryF bytecode publicInput) h fun seed h' ↦ seed ∈ h' := by
  simp only [seedWith]
  refine ((hOnly_fiatShamirIvWith bytecode).duplexP h).bind fun iv h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The verifier follows the duplex discipline.** -/
theorem duplexVm_verifier (prog : Program) (input : PublicInput) (proof : Proof) :
    DuplexVm (verifier queryH queryF prog input proof) [] := by
  rw [duplexVm_iff_duplexP]
  change DuplexP (verifyWith queryH queryF (bytecodeWords prog) (publicDigest input) proof) [] _
  simp only [verifyWith]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

/-! ## The honest prover -/

theorem hOnly_parentsM (level : List Digest) (n : ℕ) : HOnly (parentsM queryH level n) :=
  hOnly_mapM _ (fun _ ↦ hOnly_queryH _) _

theorem hOnly_rootOfLevelM : ∀ (k : ℕ) (level : List Digest), HOnly (rootOfLevelM queryH k level)
  | 0, _ => trivial
  | k + 1, _ => (hOnly_parentsM _ _).bind fun _ ↦ hOnly_rootOfLevelM k _

theorem hOnly_pathOfLevelM : ∀ (k : ℕ) (level : List Digest) (i : ℕ),
    HOnly (pathOfLevelM queryH k level i)
  | 0, _, _ => trivial
  | k + 1, _, _ =>
    (hOnly_parentsM _ _).bind fun _ ↦ (hOnly_pathOfLevelM k _ _).bind fun _ ↦ trivial

theorem hOnly_leafHashesM (height : ℕ) (word : Word) : HOnly (leafHashesM queryH height word) :=
  hOnly_mapM _ (fun _ ↦ hOnly_queryH _) _

theorem hOnly_treeRootM (height : ℕ) (word : Word) : HOnly (treeRootM queryH height word) :=
  (hOnly_leafHashesM _ _).bind fun _ ↦ hOnly_rootOfLevelM _ _

theorem hOnly_openingAtM (height : ℕ) (word : Word) (q : ℕ) :
    HOnly (openingAtM queryH height word q) := by
  simp only [openingAtM]
  exact (hOnly_leafHashesM _ _).bind fun _ ↦ (hOnly_pathOfLevelM _ _ _).bind fun _ ↦ trivial

theorem duplexP_powStepM {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) (n : E) :
    DuplexP (powStepM queryF sp n) h fun r h' ↦ r.2.state ∈ h' :=
  (duplexP_absorb hs _ _).bind fun _ _ hsp ↦ duplexP_squeeze hsp

/-- The nonce search keeps the discipline, and the sponge it searches at. -/
theorem duplexP_searchM (bits : ℕ) {h : List KState} {sp : Sponge} (hs : sp.state ∈ h) :
    ∀ ns : List ℕ, DuplexP (searchM queryF bits sp ns) h fun _ h' ↦ sp.state ∈ h'
  | [] => hs
  | n :: ns => by
    simp only [searchM]
    refine (duplexP_powStepM hs _).grow.bind fun r h' hr ↦ ?_
    split
    · exact hr.2 hs
    · exact duplexP_searchM bits (hr.2 hs) ns

theorem duplexP_findNonceM (bits : ℕ) {h : List KState} {sp : Sponge} (hs : sp.state ∈ h)
    (fuel : ℕ) : DuplexP (findNonceM queryF bits sp fuel) h fun _ h' ↦ sp.state ∈ h' := by
  simp only [findNonceM]
  split
  · exact hs
  · exact duplexP_searchM bits hs _

/-- **The honest prover keeps the discipline**, from a sponge whose state is an earlier answer. -/
theorem duplexP_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} (P : Prog α) :
    ∀ (sp : Sponge) (ev : List Ev) (h : List KState), sp.state ∈ h →
      DuplexP (proveFromM queryH queryF S fuel P sp ev) h fun _ _ ↦ True := by
  induction P with
  | ret a => intro sp ev h _; trivial
  | fail => intro sp ev h _; trivial
  | read k ih =>
    intro sp ev h hs
    simp only [proveFromM]
    exact (duplexP_absorb hs _ _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | sample k ih =>
    intro sp ev h hs
    simp only [proveFromM]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ _ hr
  | grind bits k ih =>
    intro sp ev h hs
    simp only [proveFromM]
    refine (duplexP_findNonceM bits hs fuel).bind fun r h' hr ↦ ?_
    split
    · trivial
    · exact (duplexP_powStepM hr _).bind fun r' h'' hr' ↦
        (ih _ _ _ hr').bind fun _ _ _ ↦ trivial
  | commit height width k ih =>
    intro sp ev h hs
    simp only [proveFromM]
    refine ((hOnly_treeRootM _ _).duplexP h).bind fun root h' hh ↦ ?_
    subst hh
    exact (duplexP_absorb hs _ _).bind fun sp0 h0 hs0 ↦ (duplexP_absorb hs0 _ _).bind
      fun sp1 h1 hs1 ↦ (ih _ _ _ hs1).bind fun _ _ _ ↦ trivial
  | query i ps k ih =>
    intro sp ev h hs
    simp only [proveFromM]
    split
    · trivial
    · refine ((hOnly_mapM _ (fun _ ↦ hOnly_openingAtM _ _ _) ps).duplexP h).bind
        fun os h' hh ↦ ?_
      subst hh
      exact (ih _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-- **The honest prover follows the duplex discipline.** -/
theorem duplexVm_honestComp (prog : Program) (input : PublicInput) (t : Trace prog)
    (ρ fuel : ℕ) : DuplexVm (LeanVM.Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel) [] := by
  rw [duplexVm_iff_duplexP]
  unfold LeanVM.Protocol.EndToEnd.Complete.honestComp
  split
  · simp only [Rom.honestComp, seedRun_leanVmSeed, proveM, bind_assoc]
    exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦
      (duplexP_proveFromM _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial
  · trivial

/-- **The honest prover, then the verifier, follow the duplex discipline.** -/
theorem duplexVm_honest (prog : Program) (input : PublicInput) (t : Trace prog) (ρ fuel : ℕ) :
    DuplexVm (LeanVM.Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel >>= fun proof ↦
      verifier queryH queryF prog input proof) [] :=
  (duplexVm_honestComp prog input t ρ fuel).bind fun proof ↦ duplexVm_verifier prog input proof

end LeanVM.Rpm
