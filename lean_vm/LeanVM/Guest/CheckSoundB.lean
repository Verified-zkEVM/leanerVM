/-
  LeanVM.Guest.CheckSoundB

  Soundness of the checker (`CheckSound.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.ExecB
public import LeanVM.Guest.CoreLocB

/-!
# Soundness of the checker under any `BLAKE2S` semantics

`CheckSound.lean` over `ExecB.lean` and `CoreLocB.lean`: the checker is `Check.lean`'s, a book's
atoms hold under `S` (`BookHoldsB`), and a check that passes gives the function's located core
relation under `S` (`checkWinsB_run`), each lemma proved as there. The one step that reads a
`BLAKE2S` atom, `blakeOkB_sound`, carries the row's `S.check` from the instruction to the core
atom: the checker never looks inside it. The contracts' precondition (`Pre`) and the frame
valuations (`valG`) do not mention the semantics and are `CheckSound.lean`'s; the postcondition
is `PostB S`.
-/

namespace LeanVM.Guest.Check

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

variable {S : BlakeSem}

/-! ## Words of the frame -/

section Words

variable {κ : ℕ} (L : MemImage κ) (fp : K)

variable (S) in
/-- The atoms filed in a book hold. -/
def BookHoldsB (B : Book) : Prop := ∀ o, ∀ a ∈ look B o, a.HoldsB S L fp

end Words

section Basic

variable {κ : ℕ} {L : MemImage κ} {fp : K}

theorem BookHoldsB.nil : BookHoldsB S L fp .nil := fun _ _ h ↦ by simp [look, getF_eq] at h

theorem BookHoldsB.addFact {B : Book} (hB : BookHoldsB S L fp B) {a : Exec.Atom} (ha : a.HoldsB S L fp) :
    BookHoldsB S L fp (Check.addFact B a) := by
  unfold Check.addFact
  generalize keys a = ks
  induction ks generalizing B with
  | nil => exact hB
  | cons o ks ih =>
    refine ih (fun o' b hb ↦ ?_)
    rcases look_addKey hb with rfl | hb
    · exact ha
    · exact hB o' b hb

end Basic

/-! ## The atoms of a book -/

section Atoms

variable {κ : ℕ} {L : MemImage κ} {fp : K} {B : Book}

theorem setImmB_sound (hB : BookHoldsB S L fp B) {c l0 l1 l2 : ℕ} (h : setImm B c l0 l1 l2 = true) :
    L.read (fp * gpow c) = some (OInstr.imm l0 l1 l2) := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB c a ha
  split at hp
  · rename_i pc o k0 k1 k2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hp
    exact hh
  · simp at hp

theorem setIsB_sound (hB : BookHoldsB S L fp B) {c : ℕ} {x : E} (h : setIs B c x = true) :
    L.read (fp * gpow c) = some x := by
  rw [eq_imm_of_limbs rfl rfl rfl (x := x)]
  exact setImmB_sound hB h

theorem xorInB_sound (hB : BookHoldsB S L fp B) {o p q r : ℕ} (h : xorIn B o p q r = true) :
    wd L fp r = wd L fp p + wd L fp q := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB o a ha
  split at hp
  · obtain ⟨vX, vY, hx, hy, hz⟩ := hh
    exact perm3_sound hp hx hy hz
  · simp at hp

theorem addOkB_sound (hB : BookHoldsB S L fp B) {d a b : ℕ} (h : addOk B d a b = true) :
    wd L fp d = wd L fp a + wd L fp b := by
  simp only [addOk, Bool.or_eq_true] at h
  rcases h with (h | h) | h <;> exact xorInB_sound hB h

theorem mulOkB_sound (hB : BookHoldsB S L fp B) {d a b : ℕ} (h : mulOk B d a b = true) :
    ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow d) = some (vA * vB) := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB d x hx
  split at hp
  · rename_i pc x' y' z'
    obtain ⟨vX, vY, h1, h2, h3⟩ := hh
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := hp
    · exact ⟨vX, vY, h1, h2, h3⟩
    · exact ⟨vY, vX, h2, h1, by rw [mul_comm vY vX]; exact h3⟩
  · simp at hp

theorem mulOkB_wd (hB : BookHoldsB S L fp B) {d a b : ℕ} (h : mulOk B d a b = true) :
    wd L fp d = wd L fp a * wd L fp b := by
  obtain ⟨vA, vB, h1, h2, h3⟩ := mulOkB_sound hB h
  rw [wd_of h1, wd_of h2, wd_of h3]

theorem sameOkB_sound (hB : BookHoldsB S L fp B) {a b : ℕ} (h : sameOk B a b = true) :
    wd L fp a = wd L fp b := by
  simp only [sameOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wd_of h1, wd_of h2]
    · rw [wd_of h1, wd_of h2]
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wd_of h1, wd_of h2]
    · rw [wd_of h1, wd_of h2]
  · simp at hp

theorem sameOkB_read (hB : BookHoldsB S L fp B) {a b : ℕ} (h : sameOk B a b = true) :
    L.read (fp * gpow a) = L.read (fp * gpow b) := by
  simp only [sameOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2]
    · rw [h1, h2]
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2]
    · rw [h1, h2]
  · simp at hp

theorem loadOkB_sound (hB : BookHoldsB S L fp B) {d p off : ℕ} (h : loadOk B d p off = true) :
    ∃ pv, L.read (fp * gpow p) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * gpow d) = some v ∧ L.read (pv.limb 0 * gpow off) = some v := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB d x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
    obtain ⟨pv, v3, h1, hK, h3, h2⟩ := hh
    exact ⟨pv, h1, hK, v3, h3, h2⟩
  · simp at hp

theorem loadOkB_holds (hB : BookHoldsB S L fp B) {d p off : ℕ} (h : loadOk B d p off = true) :
    Core.LoadHolds L.read (wd L fp p) off (wd L fp d) := by
  obtain ⟨pv, h1, hK, v, h3, h2⟩ := loadOkB_sound hB h
  rw [wd_of h1, wd_of h3]
  exact ⟨hK, h2⟩

theorem inKOkB_sound (hB : BookHoldsB S L fp B) {a b : ℕ} (h : inKOk B a b = true) :
    IsInK (wd L fp a) ∧ IsInK (wd L fp b) := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨c, d, f, -, h2, h3, -, hd, hf⟩ := hh
    rw [wd_of h2, wd_of h3]
    exact ⟨hd, hf⟩
  · simp at hp

theorem blakeOkB_sound (hB : BookHoldsB S L fp B) {m0 m1 m2 m3 cv0 cv1 o0 o1 md : ℕ}
    (h : blakeOk B m0 m1 m2 m3 cv0 cv1 o0 o1 md = true) :
    S.check ![wd L fp m0, wd L fp m1, wd L fp m2, wd L fp m3] (wd L fp cv0) (wd L fp cv1)
      (wd L fp o0) (wd L fp o1) (wd L fp md) := by
  simp only [blakeOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB o0 x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hp
    obtain ⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hc⟩ := hh
    rw [← gpow_succ] at hc1 hd1
    rw [wd_of h0, wd_of h1, wd_of h2, wd_of h3, wd_of hc0, wd_of hc1, wd_of hd0, wd_of hd1,
      wd_of hv]
    exact hc
  · simp at hp

theorem neOkB_sound (hB : BookHoldsB S L fp B) {x i p : ℕ} (h : neOk B x i p = true) :
    wd L fp p = wd L fp x * wd L fp i ∧ wd L fp p = 1 := by
  simp only [neOk, Bool.and_eq_true] at h
  refine ⟨mulOkB_wd hB h.1, wd_of ?_⟩
  rw [show (1 : E) = OInstr.imm 1 0 0 from (imm_of_ofBits rfl).trans ofK_one |>.symm]
  exact setImmB_sound hB h.2

theorem rangeOkB_sound (hB : BookHoldsB S L fp B) {x y t1 t2 k : ℕ}
    (h : rangeOk B x y t1 t2 k = true) :
    Core.LoadHolds L.read (wd L fp x) 0 (wd L fp t1) ∧ wd L fp k = wd L fp x * wd L fp y ∧
      Core.LoadHolds L.read (wd L fp y) 0 (wd L fp t2) := by
  simp only [rangeOk, Bool.and_eq_true] at h
  exact ⟨loadOkB_holds hB h.1.1, mulOkB_wd hB h.1.2, loadOkB_holds hB h.2⟩

theorem bounceOkB_sound (hB : BookHoldsB S L fp B) {x : ℕ} (h : bounceOk B x = true) :
    L.read (fp * gpow x) = some (ofK fp) := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB x a ha
  split at hp
  · rename_i pc hc x'
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨b, hb, hq⟩ := List.any_eq_true.mp hp
    have hh' := hB hc b hb
    split at hq
    · rename_i pc' h' o3
      simp only [beq_iff_eq] at hq
      subst hq
      obtain ⟨p, v3, h1, -, h3, h2⟩ := hh
      obtain ⟨p', v3', h1', -, -, h2'⟩ := hh'
      obtain rfl : p' = p := Option.some.inj (h1'.symm.trans h1)
      have hv := Option.some.inj (h2.symm.trans h2')
      simp only [derefSource] at hv
      rw [h3, hv]
    · simp at hq
  · simp at hp

theorem fpgAtB_sound (hB : BookHoldsB S L fp B) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ) {x e : ℕ}
    (h : fpgAt B ψ x = some e) : L.read (fp * gpow x) = some (ofK (fp * gpow e)) := by
  unfold fpgAt at h
  split at h
  · rename_i e' he
    obtain rfl := Option.some.inj h
    exact hψ x _ he
  · simp only [Bool.cond_eq_ite] at h
    split_ifs at h with hb
    obtain rfl := Option.some.inj h
    rw [bounceOkB_sound hB hb, gpow_zero', mul_one]

theorem gpAtB_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHoldsB S L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {y e : ℕ} (h : gpAt F B ψ y = some e) :
    L.read (fp * gpow y) = some (ofK (gpow e)) := by
  unfold gpAt at h
  split at h
  · rename_i e' he
    obtain rfl := Option.some.inj h
    exact hψ y _ he
  · obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
    have hh := hB y a ha
    split at hp
    · rename_i pc o k0
      simp only [Bool.cond_eq_ite, beq_iff_eq] at hp
      split_ifs at hp with ho
      subst ho
      have := PowTree.find_ok hF hp
      rw [hh, imm_of_ofBits this]
    · simp at hp

theorem addrOkB_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHoldsB S L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {loc : Trie ℕ} {p : ℕ} {run : List Core.V}
    (h : addrOk F B ψ loc p run = true) :
    IsInK (wd L fp p) ∧ ∀ (k : ℕ) (hk : k < run.length) (w : E),
      L.read ((wd L fp p).limb 0 * gpow k) = some w → w = val L fp loc run[k] := by
  obtain ⟨a, ha, hq⟩ := List.any_eq_true.mp h
  have hh := hB p a ha
  split at hq
  · rename_i pc x y z
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, hq⟩ := hq
    split at hq
    · rename_i e1 e2 h1 h2
      obtain ⟨vX, vY, hx, hy, hz⟩ := hh
      rw [fpgAtB_sound hB hψ h1] at hx
      rw [gpAtB_sound hF hB hψ h2] at hy
      obtain rfl := Option.some.inj hx
      obtain rfl := Option.some.inj hy
      have hp : wd L fp z = ofK (fp * gpow (e1 + e2)) := by
        rw [wd_of hz, ← ofK_mul, mul_assoc, gpow, gpow, gpow, ← pow_add]
      rw [hp]
      refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, fun k hk w hw ↦ ?_⟩
      have hl : (ofK (fp * gpow (e1 + e2))).limb 0 = fp * gpow (e1 + e2) := by simp
      have ha : fp * gpow (e1 + e2) * gpow k = fp * gpow (e1 + e2 + k) := by
        rw [mul_assoc, gpow, gpow, gpow, ← pow_add]
      rw [hl, ha] at hw
      unfold val
      rw [runAt_sound hq k hk]
      exact (wd_of hw).symm
    · simp at hq
  · simp at hq

/-- **A core atom the book implies holds** under the valuation of the check. -/
theorem atomOkB_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHoldsB S L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {loc : Trie ℕ} {a : Core.Atom} (h : atomOk F B ψ loc a = true) :
    a.HoldsB S L.read (val L fp loc) := by
  cases a with
  | const d x => exact wd_of (setIsB_sound hB h)
  | add d a b => exact addOkB_sound hB h
  | mul d a b => exact mulOkB_wd hB h
  | copy d s => exact sameOkB_sound hB h
  | load d p off => exact loadOkB_holds hB h
  | assertEq a b =>
    show wd L fp _ + wd L fp _ = 0
    rw [sameOkB_sound hB h, CharTwo.add_self_eq_zero]
  | assertNe x i p => exact neOkB_sound hB h
  | rangeCheck x y t1 t2 k => exact rangeOkB_sound hB h
  | assertInK a b => exact inKOkB_sound hB h
  | blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md => exact blakeOkB_sound hB h
  | frameAddr p run => exact addrOkB_sound hF hB hψ h
  | hint _ => trivial

end Atoms

/-! ## Contracts -/

section Contracts

variable {κ : ℕ} (P : Core.Program) (G : Glob) (L : MemImage κ)

variable (S) in
/-- **The guest's located call relation**: a callee runs at a frame of the memory, its values
its certificate's cells there (`Core.Program.RelLB`). -/
noncomputable abbrev RLB (cert : String → Cert) : Core.CallRel :=
  P.RelLB S L.read (frameVal L cert) (InMem κ)

variable (S) in
/-- **A function's postcondition** at frame `fp`: its located core relation holds of the argument
and return words of the frame, and its bounded frame cells are bounded. -/
def PostB (cert : String → Cert) (j : ℕ) (fp : K) : Prop :=
  RLB S P L cert (G.sig j).name (frameWords L fp 2 (G.sig j).nargs)
      (frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret) ∧ BndHolds L fp (G.sig j).post

end Contracts

/-! ## Positions of the walk -/

section Pos

variable {κ : ℕ} (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx)

variable (S) in
/-- **The run is at a position** with `k` steps left, its segment entered with at most `K`: the
segment is the executor's, the book, environment and bounds hold, the rest of the segment's
items is run (`RunKB`), its exits are the segment's, and a fresh position is the start of the
segment the index names. -/
structure PosOkB (K : ℕ) (st : CS) (k : ℕ) : Prop where
  seg : st.seg ∈ X.segs
  book : BookHoldsB S L fp st.book
  psi : EnvHolds L fp st.psi
  bnd : BndHolds L fp st.bnd
  run : ∃ k₀, k₀ ≤ K ∧ k ≤ k₀ ∧
    RunKB S L fp guest f.entry k₀ (st.seg.exit.ReachedB S L fp guest f.entry k₀) st.its k
  exits : ∀ x, x = st.seg.exit ∨ x ∈ branchExits st.its → x ∈ st.seg.exits
  fresh : ∀ t, st.fresh = some t →
    X.idx.get t = some st.seg ∧ st.seg.start = t ∧ st.its = st.seg.items ∧ st.psi = st.seg.env ∧
      SafeB S guest L k ⟨gpow (f.entry + t), fp⟩

variable (S) in
/-- **The run is at the start of the segment at offset `t`**, with `k` steps left; at the
window's end, where no segment of it starts, in its environment `wenv`. -/
def SegRunB (K t k : ℕ) : Prop :=
  SafeB S guest L k ⟨gpow (f.entry + t), fp⟩ ∧
  (∀ s, X.idx.get t = some s → s.start = t → s ∈ X.segs ∧ EnvHolds L fp s.env ∧
    ∃ k₀, k₀ ≤ K ∧ k ≤ k₀ ∧
      RunKB S L fp guest f.entry k₀ (s.exit.ReachedB S L fp guest f.entry k₀) s.items k) ∧
  (t = X.wJ → X.idx.get t = none → EnvHolds L fp X.wenv)

variable (S) in
/-- At a window's end `J`, what it hands on holds. -/
def HandHoldsB (J : ℕ) : Prop :=
  ∀ J' fs bs, X.win = some (J', fs, bs) → J = J' →
    (∀ p ∈ fs, p.2.HoldsB S L fp) ∧ BndHolds L fp bs

variable (S) in
/-- **The run arrives at `t`**: at the start of the segment there, a window's hand-over in
place. -/
def ArriveB (K t k : ℕ) : Prop := SegRunB S L fp f X K t k ∧ HandHoldsB S L fp X t

end Pos

section PosLemmas

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx}

theorem fwdLB_ok {test : Book → Bool} {e k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ (its : List Exec.Item) (B : Book) (k : ℕ), BookHoldsB S L fp B →
      RunKB S L fp guest e k₀ Q its k →
      ∃ k' ≤ k, BookHoldsB S L fp (fwdL test its B).2.1 ∧ RunKB S L fp guest e k₀ Q (fwdL test its B).1 k' ∧
        ((fwdL test its B).2.2 = true → test (fwdL test its B).2.1 = true) ∧
        ∃ pre, pre ++ (fwdL test its B).1 = its
  | [], B, k, hB, h => ⟨k, le_rfl, hB, h, fun h ↦ h, [], rfl⟩
  | it :: its, B, k, hB, h => by
    unfold fwdL
    cases ht : test B
    · simp only [Bool.cond_false]
      cases it with
      | ins a =>
        simp only [Trie.seq_eq]
        obtain ⟨ha, k', rfl, h⟩ := h
        obtain ⟨k'', hk, hB', hr, hok, pre, hpre⟩ := fwdLB_ok its _ k' (hB.addFact ha) h
        exact ⟨k'', by omega, hB', hr, hok, .ins a :: pre, by rw [List.cons_append, hpre]⟩
      | fact a =>
        simp only [Trie.seq_eq]
        obtain ⟨ha, h⟩ := h
        obtain ⟨k'', hk, hB', hr, hok, pre, hpre⟩ := fwdLB_ok its _ k (hB.addFact ha) h
        exact ⟨k'', hk, hB', hr, hok, .fact a :: pre, by rw [List.cons_append, hpre]⟩
      | branch oc od of x =>
        exact ⟨k, le_rfl, hB, h, fun h ↦ by simp at h, [], rfl⟩
    · simp only [Bool.cond_true]
      exact ⟨k, le_rfl, hB, h, fun _ ↦ ht, [], rfl⟩

theorem fwdB_ok {K : ℕ} {test : Book → Bool} {st : CS} {k : ℕ} (h : PosOkB S L fp f X K st k) :
    ∃ k' ≤ k, PosOkB S L fp f X K (fwd test st).1 k' ∧
      ((fwd test st).2 = true → test (fwd test st).1.book = true) ∧
      (fwd test st).1.seg = st.seg ∧ (fwd test st).1.psi = st.psi ∧
      (fwd test st).1.bnd = st.bnd := by
  rw [fwd_eq]
  cases ht : test st.book
  · simp only [Bool.cond_false]
    obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
    obtain ⟨k', hk', hB, hr', hok, pre, hpre⟩ := fwdLB_ok (test := test) st.its st.book k h.book hr
    refine ⟨k', hk', ⟨h.seg, hB, h.psi, h.bnd, ⟨k₀, hk₀, by omega, hr'⟩,
      exits_suffix hpre h.exits, fun t ht ↦ by simp at ht⟩, hok, by simp, by simp, by simp⟩
  · simp only [Bool.cond_true]
    exact ⟨k, le_rfl, h, fun _ ↦ ht, trivial, trivial, trivial⟩

theorem toEndB_ok {K : ℕ} {st : CS} {k : ℕ} (h : PosOkB S L fp f X K st k) :
    ∃ k' ≤ k, PosOkB S L fp f X K (toEnd st) k' ∧ (toEnd st).seg = st.seg ∧
      (toEnd st).psi = st.psi ∧ (toEnd st).bnd = st.bnd := by
  obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
  obtain ⟨k', hk', hB, hr', -, pre, hpre⟩ :=
    fwdLB_ok (test := fun _ ↦ false) st.its st.book k h.book hr
  refine ⟨k', hk', ⟨h.seg, hB, h.psi, h.bnd, ⟨k₀, hk₀, by omega, hr'⟩,
    exits_suffix hpre h.exits, fun t ht ↦ by simp [toEnd_eq] at ht⟩, by simp [toEnd_eq],
    by simp [toEnd_eq], by simp [toEnd_eq]⟩

/-- At the end of its segment, the run has reached the segment's exit. -/
theorem endAtB_ok {K : ℕ} {st se : CS} {k : ℕ} (h : PosOkB S L fp f X K st k)
    (he : endAt st = some se) :
    ∃ k' ≤ k, PosOkB S L fp f X K se k' ∧ se.seg = st.seg ∧ se.psi = st.psi ∧ se.bnd = st.bnd ∧
      ∃ k₀ ≤ K, se.seg.exit.ReachedB S L fp guest f.entry k₀ k' := by
  obtain ⟨k', hk', hp, hs, hψ, hb⟩ := toEndB_ok h
  unfold endAt at he
  split at he
  · rename_i s B ψ bnd fr heq
    obtain rfl := Option.some.inj he
    rw [heq] at hp hs hψ hb
    obtain ⟨k₀, hk₀, -, hr⟩ := hp.run
    exact ⟨k', hk', hp, hs, hψ, hb, k₀, hk₀, hr⟩
  · simp at he

/-- At a branch, the run falls through when the condition cell is `0` and leaves by the
branch's exit otherwise. -/
theorem branchAtB_ok {K : ℕ} {st st' : CS} {oc : ℕ} {x : Exec.Exit} {k : ℕ}
    (h : PosOkB S L fp f X K st k) (hb : branchAt st = some (st', oc, x)) :
    ∃ k' < k, ∃ c, L.read (fp * gpow oc) = some c ∧ IsInK c ∧ x ∈ st.seg.exits ∧
      st'.seg = st.seg ∧ st'.psi = st.psi ∧ st'.bnd = st.bnd ∧ BookHoldsB S L fp st'.book ∧
      ((c = 0 ∧ PosOkB S L fp f X K st' k') ∨
        (c ≠ 0 ∧ ∃ k₀ ≤ K, x.ReachedB S L fp guest f.entry k₀ k')) := by
  obtain ⟨k₁, hk₁, hp, hs, hψ, hbd⟩ := toEndB_ok h
  unfold branchAt at hb
  split at hb
  · rename_i s oc' od of x' its B ψ bnd fr heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    rw [heq] at hp hs hψ hbd
    obtain ⟨k₀, hk₀, hkk, hr⟩ := hp.run
    obtain ⟨⟨c, d, f', hc, -, -, hcK, -, -⟩, k', rfl, hr⟩ := hr
    have hx : x' ∈ s.exits := hp.exits x' (Or.inr (by simp [branchExits]))
    refine ⟨k', by omega, c, hc, hcK, hs ▸ hx, hs, hψ, hbd, hp.book, ?_⟩
    rcases hr with ⟨hc0, hr⟩ | ⟨⟨v, hv, hv0⟩, hr⟩
    · left
      refine ⟨Option.some.inj (hc.symm.trans hc0), hp.seg, hp.book, hp.psi, hp.bnd,
        ⟨k₀, hk₀, by omega, hr⟩, fun y hy ↦ hp.exits y ?_, fun t ht ↦ by simp at ht⟩
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (by simp only [branchExits]; exact List.mem_cons_of_mem _ hy)
    · right
      obtain rfl := Option.some.inj (hc.symm.trans hv)
      exact ⟨hv0, k₀, hk₀, hr⟩
  · simp at hb

end PosLemmas

/-! ## Segments -/

section Segs

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx}

variable (S) in
/-- What a walk assumes of its context: the executor's facts hold of the frame, the code is the
program's, the segments are good (an executor's, `execB_good`, `execWinB_good`), and the index and
links are theirs. -/
structure WalkHypB (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx) : Prop where
  ctx : Exec.Ctx X.F κ fp
  fetch : Fetches guest f.entry f.code
  entry : X.entry = f.entry
  good : ∀ s ∈ X.segs, SegGoodB S L fp guest f.entry s
  idx : X.idx = index X.segs
  linked : linkedWeak X.idx X.segs X.wJ X.wenv = true

/-- A run entering offset `t`, a successor of an exit whose environment holds, is at the start
of the segment there. -/
theorem segRunB_of_safe (H : WalkHypB S L fp f X) {s : Exec.Seg} (hs : s ∈ X.segs)
    {x : Exec.Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ) (he : EnvHolds L fp x.env)
    {K k : ℕ} (hk : k ≤ K) (h : SafeB S guest L k ⟨gpow (f.entry + t), fp⟩) :
    SegRunB S L fp f X K t k := by
  refine ⟨h, fun s' hs' hst ↦ ?_, fun htJ hn ↦ ?_⟩
  swap
  · subst htJ
    exact he.sub (linkedWeak_none H.linked hs hx ht hn)
  have hl := linkedWeak_get H.linked hs hx ht hs'
  have hmem : s' ∈ X.segs := by
    rw [H.idx] at hs'
    exact index_get hs'
  have he' := he.sub hl.2
  refine ⟨hmem, he', k, hk, le_rfl, ?_⟩
  exact (H.good s' hmem).1 k he' (by rw [hst]; exact h)

/-- A local jump to `t` leaves into the segment at `t`. -/
theorem segRunB_of_next (H : WalkHypB S L fp f X) {s : Exec.Seg} (hs : s ∈ X.segs)
    {x : Exec.Exit} (hx : x ∈ s.exits) {t : ℕ} (hk : x.kind = .next t) (ht : x.succ = [t])
    {K k₀ k : ℕ} (hk₀ : k₀ ≤ K) (h : x.ReachedB S L fp guest f.entry k₀ k) :
    SegRunB S L fp f X K t k := by
  obtain ⟨hlt, he, -, r, hr, hsafe⟩ := h
  rw [hk] at hr
  simp only [Kind.Regs] at hr
  subst hr
  exact segRunB_of_safe H hs hx (by simp [ht]) he (by omega) hsafe

theorem segAtB_ok (H : WalkHypB S L fp f X) {t : ℕ} {B : Book} {bnd : List (ℕ × ℕ)} {st : CS}
    (h : segAt X t B bnd = some st) {K k : ℕ} (hr : SegRunB S L fp f X K t k)
    (hB : BookHoldsB S L fp B) (hb : BndHolds L fp bnd) : PosOkB S L fp f X K st k := by
  unfold segAt at h
  split at h
  · rename_i s hs
    rw [getF_eq] at hs
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with hst
    obtain rfl := Option.some.inj h
    obtain ⟨hmem, he, k₀, hk₀, hk, hrun⟩ := hr.2.1 s hs hst
    exact ⟨hmem, hB, he, hb, ⟨k₀, hk₀, hk, hrun⟩,
      fun x hx ↦ (H.good s hmem).2.2 x hx, fun t' ht' ↦ by
        obtain rfl := Option.some.inj ht'
        exact ⟨hs, hst, rfl, rfl, hr.1⟩⟩
  · simp at h

theorem PosOkB.segRun {K : ℕ} {st : CS} {k : ℕ} (h : PosOkB S L fp f X K st k) {t : ℕ}
    (ht : st.fresh = some t) : SegRunB S L fp f X K t k := by
  obtain ⟨hi, hs, hits, hψ, hsafe⟩ := h.fresh t ht
  refine ⟨hsafe, fun s hs' _ ↦ ?_, fun _ hn ↦ by rw [hi] at hn; cases hn⟩
  obtain rfl := Option.some.inj (hi.symm.trans hs')
  obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
  exact ⟨h.seg, hψ ▸ h.psi, k₀, hk₀, hk, hits ▸ hr⟩

/-- Where a block ends, the run is at the start of that segment. -/
theorem endOfB_ok (H : WalkHypB S L fp f X) {K : ℕ} {st se : CS} {k J : ℕ} (h : PosOkB S L fp f X K st k)
    (he : endOf st = some (J, se)) :
    ∃ k' ≤ k, PosOkB S L fp f X K se k' ∧ SegRunB S L fp f X K J k' := by
  unfold endOf at he
  split at he
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨k, le_rfl, h, h.segRun ht⟩
  · split at he
    · rename_i se' hse
      split at he
      · rename_i t hkind
        simp only [Bool.cond_eq_ite, beq_iff_eq] at he
        split_ifs at he with hsucc
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k', hk', hp, hs, -, -, k₀, hk₀, hr⟩ := endAtB_ok h hse
        exact ⟨k', hk', hp, segRunB_of_next H hp.seg (hp.exits _ (Or.inl rfl)) hkind hsucc hk₀ hr⟩
      · simp at he
    · simp at he

end Segs

/-! ## Inverting the walk -/

section Inv

variable {X : Fx}

end Inv

/-! ## Calls and tables -/

section Calls

variable {κ : ℕ} {L : MemImage κ} {fp : K} {B : Book}

theorem storesOkB_sound (hB : BookHoldsB S L fp B) {q : ℕ} :
    ∀ {o : ℕ} {cs : List ℕ}, storesOk B q o cs = true → ∀ i (hi : i < cs.length),
      ∃ pv, L.read (fp * gpow q) = some pv ∧ IsInK pv ∧
        ∃ v, L.read (fp * gpow cs[i]) = some v ∧ L.read (pv.limb 0 * gpow (o + i)) = some v
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | o, c :: cs, h, i, hi => by
    simp only [storesOk, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using loadOkB_sound hB h.1
    | succ i =>
      obtain ⟨pv, h1, hK, v, h2, h3⟩ := storesOkB_sound hB h.2 i (by simpa using hi)
      exact ⟨pv, h1, hK, v, by simpa using h2, by rw [show o + (i + 1) = o + 1 + i by omega]; exact h3⟩

/-- Stored cells are the callee frame's words. -/
theorem storesOkB_words (hB : BookHoldsB S L fp B) {q o : ℕ} {cs : List ℕ} (h : storesOk B q o cs = true)
    {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    cs.map (wd L fp) = frameWords L (pv.limb 0) o cs.length := by
  apply List.ext_getElem (by simp [frameWords])
  intro i h1 h2
  simp only [List.getElem_map, frameWords, List.getElem_range]
  obtain ⟨pv', hq', -, v, h3, h4⟩ := storesOkB_sound hB h i (by simpa using h1)
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  rw [wd_of h3, wd_of h4]

theorem envStoresOkB_sound (hB : BookHoldsB S L fp B) {q : ℕ} {env : List (ℕ × Sym)}
    (h : envStoresOk B q env = true) {pv : E} (hq : L.read (fp * gpow q) = some pv)
    (hK : IsInK pv) : EnvHolds L (pv.limb 0) (envOf env) := by
  apply envOf_holds
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this
  obtain ⟨hs, hl⟩ := this
  rw [Sym.beq_eq hs]
  obtain ⟨pv', hq', -, v, h1, h2⟩ := loadOkB_sound hB hl
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  obtain rfl := Option.some.inj (h1.symm.trans hq')
  rw [h2]
  simp only [Sym.val, gpow_zero', mul_one]
  exact congrArg some (inK_eq hK)

theorem boundOkB_sound {mem : List (ℕ × ℕ × ℕ)} (hm : MemPre L fp mem) (hB : BookHoldsB S L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {c n : ℕ} (h : boundOk mem B bnd c n = true) :
    ∃ e < n, L.read (fp * gpow c) = some (ofK (gpow e)) := by
  simp only [boundOk, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB c a ha
    split at hp
    · rename_i x y k
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
      obtain ⟨rfl, hk⟩ := hp
      obtain ⟨e, e', he, hx, -⟩ := hh
      exact ⟨e, by omega, hx⟩
    · rename_i pc o1 o2 o3
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨m, hmm, hq⟩ := List.any_eq_true.mp hp
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq] at hq
      obtain ⟨⟨rfl, hlt⟩, hle⟩ := hq
      obtain ⟨p, v3, h1, -, h3, h2⟩ := hh
      obtain ⟨p', h1', -, e, he, h2'⟩ := hm m hmm o2 hlt
      obtain rfl := Option.some.inj (h1.symm.trans h1')
      have hv := Option.some.inj (h2.symm.trans h2')
      simp only [derefSource] at hv
      exact ⟨e, by omega, by rw [h3, hv]⟩
    · simp at hp
  · obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq
    obtain ⟨e, he, hr⟩ := hb p hp
    exact ⟨e, by omega, hq.1 ▸ hr⟩

theorem memOkB_sound (hB : BookHoldsB S L fp B) {known : List (ℕ × ℕ × ℕ)} (hk : MemKnown L fp known)
    {args : List ℕ} {mem : List (ℕ × ℕ × ℕ)} (h : memOk known args mem = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    MemPre L (pv.limb 0) mem := by
  intro m hm c hc
  have := List.all_eq_true.mp h m hm
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hany⟩ := this
  obtain ⟨kk, hkk, hq'⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq'
  obtain ⟨⟨hc1, hlen⟩, hn⟩ := hq'
  obtain ⟨e, he, hK, hr⟩ := hk kk hkk c (by omega)
  obtain ⟨pv', hq'', -, v, h1, h3⟩ := storesOkB_sound hB hs (m.1 - 2) hlt
  obtain rfl := Option.some.inj (hq''.symm.trans hq)
  rw [show 2 + (m.1 - 2) = m.1 by omega] at h3
  rw [hc1, nth_eq hlt, wd_of h1] at hK hr
  exact ⟨v, h3, hK, e, by omega, hr⟩

theorem preOkB_sound {mem : List (ℕ × ℕ × ℕ)} (hm : MemPre L fp mem) (hB : BookHoldsB S L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd)
    {args : List ℕ} {pre : List (ℕ × ℕ)} (h : preOk mem B bnd args pre = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    BndHolds L (pv.limb 0) pre := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
  obtain ⟨e, he, hr⟩ := boundOkB_sound hm hB hb hbd
  obtain ⟨pv', hq', -, v, h1, h3⟩ := storesOkB_sound hB hs (p.1 - 2) hlt
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  rw [nth_eq hlt, h1] at hr
  obtain rfl := Option.some.inj hr
  refine ⟨e, he, ?_⟩
  rwa [show 2 + (p.1 - 2) = p.1 by omega] at h3

theorem tableBaseB_sound (hB : BookHoldsB S L fp B) {t c base : ℕ} (h : tableBase B t c = some base) :
    ∃ pv, L.read (fp * gpow c) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * gpow t) = some v ∧ L.read (pv.limb 0 * gpow base) = some v := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB t a ha
  split at hp
  · rename_i pc o1 o2 o3
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at hp
    split_ifs at hp with hc
    obtain rfl := Option.some.inj hp
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨pv, v3, h1, hK, h3, h2⟩ := hh
    exact ⟨pv, h1, hK, v3, h3, h2⟩
  · simp at hp

/-- Stored cells, with the frame they are stored in fixed. -/
theorem storesOkB_at (hB : BookHoldsB S L fp B) {q o : ℕ} {cs : List ℕ} (h : storesOk B q o cs = true)
    {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    ∀ i (hi : i < cs.length), ∃ v, L.read (fp * gpow cs[i]) = some v ∧
      L.read (pv.limb 0 * gpow (o + i)) = some v := by
  intro i hi
  obtain ⟨pv', hq', -, v, h1, h2⟩ := storesOkB_sound hB h i hi
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  exact ⟨v, h1, h2⟩

theorem tailEnvOkB_sound (hB : BookHoldsB S L fp B) {env : Trie Sym} (he : EnvHolds L fp env)
    {Sz o : ℕ} (h : tailEnvOk B env Sz o = true) :
    L.read (fp * gpow (Sz + o)) = some (ofK (fp * gpow Sz)) := by
  simp only [tailEnvOk, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i e' he'
      simp only [beq_iff_eq] at h
      subst h
      exact he _ _ he'
    · simp at h
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB _ a ha
    split at hp
    · rename_i d w
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      split at hp
      · rename_i e' he'
        simp only [beq_iff_eq] at hp
        subst hp
        obtain ⟨v, h1, h2⟩ := hh
        rw [h2, ← h1]
        exact he _ _ he'
      · simp at hp
    · simp at hp

end Calls

/-! ## The walk -/

section Walk

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx} {Prog : Core.Program}
  {cert : String → Cert}
  {Kb : ℕ}

variable (S) in
/-- The words a function returns and what its return does: the frame's return words, back to
the caller with fewer than `Kb` steps left (but `main`), its bounds after. -/
def RetWordsB (L : MemImage κ) (fp : K) (X : Fx) (Kb : ℕ) (rs : List E) : Prop :=
  rs = frameWords L fp (2 + X.nargs) X.nret ∧
    (X.main = false → ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ SafeB S guest L k' r) ∧
    BndHolds L fp X.post

variable (S) in
/-- What a walk of runs with at most `K` steps assumes: its context, the jump table, and every
function's contract for runs shorter than `K`. -/
structure WalkEnvB (Prog : Core.Program) (cert : String → Cert) (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx)
    (Kb : ℕ) : Prop where
  hyp : WalkHypB S L fp f X
  jt : JTHolds X.G L
  mem : MemPre L fp X.mem
  known : MemKnown L fp X.known
  sems : SemHolds X.G L fp X.sems
  callees : ∀ j, FunSpecLtB S guest L Kb (X.G.sig j).entry (Pre X.G L j) (PostB S Prog X.G L cert j)

variable (S) in
/-- **What the walk of a block from a position gives**: the block's core semantics under the
check's valuation, with any continuation the run's arrival at the join gives; the pending atoms;
and that the run arrives at the join. -/
def WalkGoodB (Prog : Core.Program) (cert : String → Cert) (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx) (Kb : ℕ)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom) : Prop :=
  ∀ k (N : Prop), PosOkB S L fp f X Kb st k → chkL X ss st P ≠ .fail →
    (∀ J, chkL X ss st P = .join J → ∀ k', k' ≤ k → SegRunB S L fp f X Kb J k' → N) →
    Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N (RetWordsB S L fp X Kb) ∧
      (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
      (∀ J, chkL X ss st P = .join J → ∃ k' ≤ k, ArriveB S L fp f X Kb J k')

theorem handOkB_sound {st : CS} (hB : BookHoldsB S L fp st.book) (hb : BndHolds L fp st.bnd) {J : ℕ}
    (h : handOk X J st = true) : HandHoldsB S L fp X J := by
  intro J' fs bs hw hJ
  unfold handOk at h
  rw [hw] at h
  simp only [hJ, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun p hp ↦ hB p.1 p.2 (by simpa using h.1 p hp), fun b hbb ↦ hb b (by simpa using h.2 b hbb)⟩

theorem pendOkB_sound (W : WalkEnvB S Prog cert L fp f X Kb) {st : CS} {k : ℕ} (hp : PosOkB S L fp f X Kb st k)
    {P : List Core.Atom} (h : pendOk X st P = true) : ∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc) :=
  fun a ha ↦ atomOkB_sound W.hyp.ctx.pows hp.book hp.psi (List.all_eq_true.mp h a ha)

theorem walkB_nil (W : WalkEnvB S Prog cert L fp f X Kb) (st : CS) (P : List Core.Atom) :
    WalkGoodB S Prog cert L fp f X Kb [] st P := by
  intro k N hp hne hj
  rw [chkL_nil] at hne hj ⊢
  obtain ⟨J, se, he, hpd, hhand, hr⟩ := blockEnd_join hne
  obtain ⟨k', hk', hse, hsr⟩ := endOfB_ok W.hyp hp he
  refine ⟨hj J hr k' hk' hsr, pendOkB_sound W hse hpd, fun J' hJ' ↦ ⟨k', hk', ?_⟩⟩
  rw [hr] at hJ'
  cases hJ'
  exact ⟨hsr, handOkB_sound hse.book hse.bnd hhand⟩

theorem walkB_atom (W : WalkEnvB S Prog cert L fp f X Kb) (a : Core.Atom) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.atom a :: ss) st P := by
  intro k N hp hne hj
  rw [chkL_atom] at hne hj ⊢
  obtain ⟨k', hk', hp', htest, -, hpsi, -⟩ :=
    fwdB_ok (test := fun B ↦ atomOk X.F B st.psi X.loc a) hp
  revert hne hj htest hp'
  rcases hf : fwd (fun B ↦ atomOk X.F B st.psi X.loc a) st with ⟨st', b⟩
  intro hne hj hp' htest
  simp only at hp' htest hne hj ⊢
  cases b with
  | false =>
    obtain ⟨hl, hP, hr⟩ := ih st' (a :: P) k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
    refine ⟨⟨hP a List.mem_cons_self, hl⟩, fun b hb ↦ hP b (List.mem_cons_of_mem _ hb),
      fun J hJ ↦ ?_⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩
  | true =>
    obtain ⟨hl, hP, hr⟩ := ih st' P k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
    have ha := atomOkB_sound W.hyp.ctx.pows hp'.book hp.psi (htest rfl)
    refine ⟨⟨ha, hl⟩, hP, fun J hJ ↦ ?_⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩

theorem walkB_ite (W : WalkEnvB S Prog cert L fp f X Kb) (c : Core.V) (z n ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ihz : ∀ st P, WalkGoodB S Prog cert L fp f X Kb z st P)
    (ihn : ∀ st P, WalkGoodB S Prog cert L fp f X Kb n st P)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.ite c z n :: ss) st P := by
  intro k N hp hne hj
  obtain ⟨st', x, t, sn, J, sj, hb, hk, hsucc, hsn, hz, hn, hsj, heq⟩ := chkL_ite hne
  rw [heq] at hne hj ⊢
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, -, hbnd, hB', hcase⟩ := branchAtB_ok hp hb
  have rest : ∀ k2, k2 ≤ k → SegRunB S L fp f X Kb J k2 →
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N (RetWordsB S L fp X Kb) ∧
        (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, ArriveB S L fp f X Kb J' k') := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3⟩ := ih sj P k2 N (segAtB_ok W.hyp hsj hr hB' (hbnd ▸ hp.bnd)) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩⟩
  have hσ : val L fp X.loc c = cv := wd_of hc
  have hblk : ∀ (b : List Core.Stmt) (sb : CS), (∀ st P, WalkGoodB S Prog cert L fp f X Kb b st P) →
      PosOkB S L fp f X Kb sb k1 → chkL X b sb [] = .join J →
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) b
          (Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N
            (RetWordsB S L fp X Kb)) (RetWordsB S L fp X Kb) ∧
        (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, ArriveB S L fp f X Kb J' k') := by
    intro b sb ihb hpb hjb
    obtain ⟨hl, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
      (fun J' hJ' k2 hk2 hr2 ↦ by
        rw [hjb] at hJ'
        cases hJ'
        exact (rest k2 (by omega) hr2).1)
    obtain ⟨k2, hk2, hr2⟩ := hr J hjb
    obtain ⟨-, hP, hreach⟩ := rest k2 (by omega) hr2.1
    exact ⟨hl, hP, hreach⟩
  rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
  · obtain ⟨hl, hP, hreach⟩ := hblk z st' ihz hp' hz
    exact ⟨⟨hσ ▸ hcK, fun _ ↦ hl, fun h0 ↦ absurd hσ h0⟩, hP, hreach⟩
  · have hrt := segRunB_of_next W.hyp hp.seg (hseg ▸ hx) hk hsucc hk₀ hr
    obtain ⟨hl, hP, hreach⟩ := hblk n sn ihn (segAtB_ok W.hyp hsn hrt hB' (hbnd ▸ hp.bnd)) hn
    exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd (hσ.symm.trans h0) hc0, fun _ ↦ hl⟩, hP, hreach⟩

/-- A block walked from `sb` to the join `J`, the rest walked from the join's segment `sj`. -/
theorem walkB_block (W : WalkEnvB S Prog cert L fp f X Kb) {b ss : List Core.Stmt} {sb sj : CS}
    {P : List Core.Atom} {J k k1 : ℕ} {N : Prop} {B : Book} {bnd : List (ℕ × ℕ)}
    (hk1 : k1 ≤ k) (ihb : ∀ st P, WalkGoodB S Prog cert L fp f X Kb b st P)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) (hpb : PosOkB S L fp f X Kb sb k1)
    (hjb : chkL X b sb [] = .join J) (hsj : segAt X J B bnd = some sj)
    (hB : BookHoldsB S L fp B) (hbnd : BndHolds L fp bnd) (hne : chkL X ss sj P ≠ .fail)
    (hj : ∀ J', chkL X ss sj P = .join J' → ∀ k', k' ≤ k → SegRunB S L fp f X Kb J' k' → N) :
    Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) b
        (Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N
          (RetWordsB S L fp X Kb)) (RetWordsB S L fp X Kb) ∧
      (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
      (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, ArriveB S L fp f X Kb J' k') := by
  have rest : ∀ k2, k2 ≤ k1 → SegRunB S L fp f X Kb J k2 →
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N (RetWordsB S L fp X Kb) ∧
        (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, ArriveB S L fp f X Kb J' k') := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3⟩ := ih sj P k2 N (segAtB_ok W.hyp hsj hr hB hbnd) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩⟩
  obtain ⟨hl, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
    (fun J' hJ' k2 hk2 hr2 ↦ by
      rw [hjb] at hJ'
      cases hJ'
      exact (rest k2 hk2 hr2).1)
  obtain ⟨k2, hk2, hr2⟩ := hr J hjb
  obtain ⟨-, hP, hreach⟩ := rest k2 hk2 hr2.1
  exact ⟨hl, hP, hreach⟩

theorem walkB_match (W : WalkEnvB S Prog cert L fp f X Kb) (v : Core.V) (arms : List (List Core.Stmt))
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (iha : ∀ e (he : e < arms.length) st P, WalkGoodB S Prog cert L fp f X Kb arms[e] st P)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.match_ v arms :: ss) st P := by
  intro k N hp hne hj
  obtain ⟨se, t, ft, t0, ts, a0, as, base, s0, J, sj, hse, hk, hs, harms0, hself, hlen, hbd, htb,
    harms, hs0, hJ, hchk, hsj, heq⟩ := chkL_match hne
  subst harms0
  rw [heq] at hne hj ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAtB_ok hp hse
  obtain ⟨hlt, henv, -, r, hreg, hsafe⟩ := hr
  rw [hk] at hreg
  obtain ⟨a, b, ⟨w, hw, -, rfl⟩, hb, rfl⟩ := hreg
  obtain rfl := self_is W.hyp.ctx.fpOne hself hb
  obtain ⟨e, he, hce⟩ := boundOkB_sound W.mem hpse.book hpse.bnd hbd
  obtain ⟨pv, hpv, -, w', hw', hload⟩ := tableBaseB_sound hpse.book htb
  obtain rfl := Option.some.inj (hpv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  have heA : e < (t0 :: ts).length := by simp; omega
  have hslot := W.jt _ _ (armsOk_get harms e heA)
  have hadd : gpow e * gpow base = gpow (base + (0 + e)) := by
    rw [Nat.zero_add, gpow, gpow, gpow, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0, W.hyp.entry] at hsafe
  have hrun := segRunB_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl))
    (by rw [hs]; exact List.getElem_mem heA) henv (K := Kb) (by omega) hsafe
  have harm : ∃ sb, segAt X (t0 :: ts)[e] se.book se.bnd = some sb ∧
      chkL X (a0 :: as)[e] sb [] = .join J := by
    cases e with
    | zero => exact ⟨s0, hs0, hJ⟩
    | succ e =>
      obtain ⟨-, hg⟩ := chkArms_get hchk
      exact hg e (by simp at he; omega) (by simp at heA; omega)
  obtain ⟨sb, hsb, hjb⟩ := harm
  have heL : e < (a0 :: as).length := by simp; omega
  obtain ⟨hl, hP, hreach⟩ := walkB_block W hk1 (iha e heL) ih
    (segAtB_ok W.hyp hsb hrun hpse.book hpse.bnd) hjb hsj hpse.book hpse.bnd hne hj
  refine ⟨(Core.holdsB_match_iff _ _ _ _).mpr ⟨e, heL, wd_of hce, hl⟩, hP, hreach⟩

/-- What a call into frame `fp[q] = pv` gives the caller: the callee ran from its entry and came
back to the return point, its contract holding of its frame. -/
theorem callB_ok (W : WalkEnvB S Prog cert L fp f X Kb) {B : Book} {bnd : List (ℕ × ℕ)}
    (hB : BookHoldsB S L fp B) (hbnd : BndHolds L fp bnd) {j q r k1 : ℕ} {f' : String}
    {ca : List ℕ} {nr : ℕ} (hj : calleeAt X (X.G.sig j).entry = some j)
    (hco : callOk X B bnd (X.G.sig j) f' q ca nr = true) {pv : E}
    (hq : L.read (fp * gpow q) = some pv) (hpK : IsInK pv)
    (hret : retRegs L (pv.limb 0) = some ⟨gpow r, fp⟩) (hk1 : k1 < Kb)
    (hsafe : SafeB S guest L k1 ⟨gpow (X.G.sig j).entry, pv.limb 0⟩) :
    ∃ k2 < k1, PostB S Prog X.G L cert j (pv.limb 0) ∧ SafeB S guest L k2 ⟨gpow r, fp⟩ ∧
      f' = (X.G.sig j).name ∧ ca.length = (X.G.sig j).nargs ∧ nr = (X.G.sig j).nret ∧
      ca.map (wd L fp) = frameWords L (pv.limb 0) 2 (X.G.sig j).nargs ∧
      (∀ p ∈ (X.G.sig j).post, 2 ≤ p.1 ∧ p.1 < 2 + (X.G.sig j).nargs + (X.G.sig j).nret) ∧
      storesOk B q 2 ca = true := by
  simp only [callOk, Bool.and_eq_true, beq_iff_eq] at hco
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hst⟩, henvst⟩, hpre⟩, hmem⟩, hsem⟩, hpost⟩ := hco
  obtain ⟨hgood, -⟩ := calleeAt_some hj
  have hPre : Pre X.G L j (pv.limb 0) :=
    ⟨hgood, W.jt, envStoresOkB_sound hB henvst hq hpK, preOkB_sound W.mem hB hbnd hpre hst hq,
      memOkB_sound hB W.known hmem hst hq, semOk_sound W.sems hsem fun i hi ↦ by
        obtain ⟨pv', hq', -, v, h1, h2⟩ := storesOkB_sound hB hst i hi
        obtain rfl := Option.some.inj (hq'.symm.trans hq)
        rw [wd_of h1, wd_of h2]⟩
  obtain ⟨k2, hk2, hPost, hsafe2⟩ := (W.callees j).call hk1 hPre hret hsafe
  refine ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, ?_, fun p hp ↦ ?_, hst⟩
  · rw [storesOkB_words hB hst hq, hna]
  · have := List.all_eq_true.mp hpost p hp
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
    exact this

theorem walkB_call (W : WalkEnvB S Prog cert L fp f X Kb) (f' : String) (args rets : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.call f' args rets :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨se, e, q, r, j, st', hse, hk, hj, hco, hle, hsucc, hac, heq⟩ := chkL_call hne
  rw [heq] at hne hjn ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAtB_ok hp hse
  obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
  rw [hk] at hextra hreg
  obtain ⟨pv, hq, hret⟩ := hextra
  obtain ⟨pv', a, hq', hpK, ha, rfl⟩ := hreg
  obtain rfl := Option.some.inj (hq.symm.trans hq')
  simp only [Tgt.Is] at ha
  subst ha
  obtain ⟨-, hentry⟩ := calleeAt_some hj
  rw [← hentry] at hj hsafe
  obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, hpost, hst⟩ :=
    callB_ok W hpse.book hpse.bnd hj hco hq hpK hret (by omega) hsafe
  have hr2 : SegRunB S L fp f X Kb (r - X.entry) k2 := by
    refine segRunB_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl)) (by rw [hsucc]; simp) henv
      (by omega) ?_
    rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
    exact hsafe2
  obtain ⟨sr, hsr, hfw⟩ := afterCall_some hac
  obtain ⟨k3, hk3, hp3, htest, -, -, -⟩ :=
    fwdB_ok (test := fun B ↦ loadsOk B q (2 + args.length) (cellsOf X.loc rets))
      (segAtB_ok W.hyp hsr hr2 hpse.book hpse.bnd)
  rw [hfw] at hp3 htest
  have hloads : storesOk st'.book q (2 + args.length) (cellsOf X.loc rets) = true := htest rfl
  have hca := cellsOf_length X.loc args
  have hcr := cellsOf_length X.loc rets
  have hna' : args.length = (X.G.sig j).nargs := hca ▸ hna
  have hcall : RLB S Prog L cert f' (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOkB_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.1
  have hb4 : BndHolds L fp
      (postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd) := by
    refine BndHolds.append (postBnd_sound (pv := pv) (storesOkB_at hpse.book hst hq)
      (fun i hi ↦ ?_) (fun p hp ↦ ?_) hPost.2) hp3.bnd
    · obtain ⟨v, h1, h2⟩ := storesOkB_at hp3.book hloads hq i hi
      exact ⟨v, h1, by rw [hca]; exact h2⟩
    · obtain ⟨h1, h2⟩ := hpost p hp
      refine ⟨h1, ?_⟩
      rw [hca, hcr, hna', hnr]
      exact h2
  have hp4 : PosOkB S L fp f X Kb ⟨st'.seg, st'.its, st'.book, st'.psi,
      postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd,
      st'.fresh⟩ k3 :=
    ⟨hp3.seg, hp3.book, hp3.psi, hb4, hp3.run, hp3.exits, hp3.fresh⟩
  obtain ⟨hl, hP, hreach⟩ := ih _ P k3 N hp4 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
  exact ⟨⟨hcall, hl⟩, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩

theorem walkB_dispatch (W : WalkEnvB S Prog cert L fp f X Kb) (v : Core.V) (fs : List String)
    (args rets : List Core.V) (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.dispatch v fs args rets :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨se, t, q, r, base, st', hse, hk, htb, hbd, hle, hsucc, htc, hac, heq⟩ :=
    chkL_dispatch hne
  rw [heq] at hne hjn ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAtB_ok hp hse
  obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
  rw [hk] at hextra hreg
  obtain ⟨pv, hq, hret⟩ := hextra
  obtain ⟨pv', a, hq', hpK, ⟨w, hw, -, rfl⟩, rfl⟩ := hreg
  obtain rfl := Option.some.inj (hq.symm.trans hq')
  obtain ⟨e, he, hce⟩ := boundOkB_sound W.mem hpse.book hpse.bnd hbd
  obtain ⟨cv, hcv, -, w', hw', hload⟩ := tableBaseB_sound hpse.book htb
  obtain rfl := Option.some.inj (hcv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  obtain ⟨pc, j, hslot, hj, hok⟩ := tableCallsOk_get htc e he
  have hadd : gpow e * gpow base = gpow (base + (0 + e)) := by
    rw [Nat.zero_add, gpow, gpow, gpow, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, W.jt _ _ hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0] at hsafe
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hco, hpost0⟩ := hok
  obtain ⟨-, hentry⟩ := calleeAt_some hj
  rw [← hentry] at hj hsafe
  obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, -, -⟩ :=
    callB_ok W hpse.book hpse.bnd hj hco hq hpK hret (by omega) hsafe
  have hr2 : SegRunB S L fp f X Kb (r - X.entry) k2 := by
    refine segRunB_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl)) (by rw [hsucc]; simp) henv
      (by omega) ?_
    rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
    exact hsafe2
  obtain ⟨sr, hsr, hfw⟩ := afterCall_some hac
  obtain ⟨k3, hk3, hp3, htest, -, -, -⟩ :=
    fwdB_ok (test := fun B ↦ loadsOk B q (2 + args.length) (cellsOf X.loc rets))
      (segAtB_ok W.hyp hsr hr2 hpse.book hpse.bnd)
  rw [hfw] at hp3 htest
  have hloads : storesOk st'.book q (2 + args.length) (cellsOf X.loc rets) = true := htest rfl
  have hca := cellsOf_length X.loc args
  have hcr := cellsOf_length X.loc rets
  have hna' : args.length = (X.G.sig j).nargs := hca ▸ hna
  have hcall : RLB S Prog L cert fs[e] (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOkB_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.1
  obtain ⟨hl, hP, hreach⟩ := ih st' P k3 N hp3 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
  exact ⟨⟨⟨e, he, wd_of hce, hcall⟩, hl⟩, hP,
    fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩

theorem walkB_callIf (W : WalkEnvB S Prog cert L fp f X Kb) (c : Core.V) (f' : String) (args : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGoodB S Prog cert L fp f X Kb ss st P) :
    WalkGoodB S Prog cert L fp f X Kb (.callIf c f' args :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨st', x, hb, hform⟩ := chkL_callIf hne
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, hpsi, hbnd, hB', hcase⟩ := branchAtB_ok hp hb
  have hσ : val L fp X.loc c = cv := wd_of hc
  obtain ⟨k₀', hk₀', hkk₀, -⟩ := hp.run
  rcases hform with ⟨e, q, r, j, se, sr, hk, hj, hco, hpost0, hle, hsucc, hend, hsr, heq⟩ |
    ⟨e, Sz, j, hk, hj, rfl, htail, heq⟩
  · rw [heq] at hne hjn ⊢
    have cont : ∀ k2, k2 < k → SegRunB S L fp f X Kb (r - X.entry) k2 →
        Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc) ss N (RetWordsB S L fp X Kb) ∧
          (∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc)) ∧
          (∀ J, chkL X ss sr P = .join J → ∃ k' ≤ k, ArriveB S L fp f X Kb J k') := by
      intro k2 hk2 hr2
      obtain ⟨hl, hP, hreach⟩ := ih sr P k2 N (segAtB_ok W.hyp hsr hr2 hB' (hbnd ▸ hp.bnd)) hne
        (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
      exact ⟨hl, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩
    rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
    · obtain ⟨k2, hk2, -, hr2⟩ := endOfB_ok W.hyp hp' hend
      obtain ⟨hl, hP, hreach⟩ := cont k2 (by omega) hr2
      exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd hσ h0, hl⟩, hP, hreach⟩
    · obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
      rw [hk] at hextra hreg
      obtain ⟨pv, hq, hret⟩ := hextra
      obtain ⟨pv', a, hq', hpK, ha, rfl⟩ := hreg
      obtain rfl := Option.some.inj (hq.symm.trans hq')
      simp only [Tgt.Is] at ha
      subst ha
      obtain ⟨-, hentry⟩ := calleeAt_some hj
      rw [← hentry] at hj hsafe
      obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, -, -⟩ :=
        callB_ok W hB' (hbnd ▸ hp.bnd) hj hco hq hpK hret (by omega) hsafe
      have hr2 : SegRunB S L fp f X Kb (r - X.entry) k2 := by
        refine segRunB_of_safe W.hyp hp.seg hx (by rw [hsucc]; simp) henv (by omega) ?_
        rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
        exact hsafe2
      obtain ⟨hl, hP, hreach⟩ := cont k2 (by omega) hr2
      have hcall : RLB S Prog L cert f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.1
        rw [← hnr, frameWords_zero, ← hargs, ← map_val, ← hname] at h1
        exact h1
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hl⟩, hP, hreach⟩
  · rw [heq]
    simp only [tailOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Bool.not_eq_true',
      List.all_eq_true] at htail
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hxnr⟩, hpre⟩, hmem0⟩, hxpost⟩, hsem⟩, hargs⟩, henv⟩,
      hr0⟩, hr1⟩, hpend⟩, hmain⟩, hend⟩ := htail
    have hP : ∀ a ∈ P, a.HoldsB S L.read (val L fp X.loc) := fun a ha ↦
      atomOkB_sound W.hyp.ctx.pows hB' (hpsi ▸ hp.psi) (List.all_eq_true.mp hpend a ha)
    have hrw : RetWordsB S L fp X Kb [] → Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read
        (val L fp X.loc) [.ret []] N (RetWordsB S L fp X Kb) := id
    have hwords : ∀ (h : ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ SafeB S guest L k' r),
        RetWordsB S L fp X Kb [] := fun h ↦
      ⟨by rw [hxnr]; rfl, fun _ ↦ h, by rw [hxpost]; intro p hp; simp at hp⟩
    rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
    · split at hend
      · rename_i se hse
        obtain ⟨k2, hk2, -, -, -, -, k₀2, hk₀2, hr2⟩ := endAtB_ok hp' hse
        have hkind : se.seg.exit.kind = .ret := of_decide_eq_true hend
        obtain ⟨hlt, -, -, rr, hreg, hsafe⟩ := hr2
        rw [hkind] at hreg
        exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd hσ h0, hwords ⟨k2, by omega, rr, hreg, hsafe⟩⟩, hP,
          fun J hJ ↦ by simp at hJ⟩
      · simp at hend
    · obtain ⟨hlt, hxenv, -, rr, hreg, hsafe⟩ := hr
      rw [hk] at hreg
      obtain ⟨a, b, ha, hb', rfl⟩ := hreg
      simp only [Tgt.Is] at ha hb'
      subst ha hb'
      obtain ⟨hgood, hentry⟩ := calleeAt_some hj
      have hPre : Pre X.G L j (fp * gpow Sz) := by
        refine ⟨hgood, W.jt, envOf_holds fun p hp ↦ ?_, fun p hq0 ↦ ?_,
          by rw [hmem0]; intro p hp; simp at hp, semOk_sound W.sems hsem fun i hi ↦ ?_⟩
        rotate_left
        · have := List.all_eq_true.mp hpre p hq0
          simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
          obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
          obtain ⟨e, he, hr⟩ := boundOkB_sound W.mem hB' (hbnd ▸ hp.bnd) hbd
          refine ⟨e, he, ?_⟩
          have hs := sameOkB_read hB' (tailArgsOk_sound hargs (p.1 - 2) hlt)
          rw [nth_eq hlt] at hr
          rw [show 2 + (p.1 - 2) = p.1 by omega, hr] at hs
          rw [mul_assoc, gpow, gpow, ← pow_add, ← gpow]
          exact hs
        · have := sameOkB_sound hB' (tailArgsOk_sound hargs i hi)
          rw [← this]
          unfold wd
          rw [mul_assoc, gpow, gpow, ← pow_add]
        have := henv p hp
        rw [Sym.beq_eq this.1]
        have h2 := tailEnvOkB_sound hB' hxenv this.2
        rw [mul_assoc, gpow, gpow, ← pow_add, ← gpow]
        simpa [Sym.val, gpow_zero'] using h2
      have hret : retRegs L (fp * gpow Sz) = retRegs L fp := by
        have e0 := sameOkB_read hB' hr0
        have e1 := sameOkB_read hB' hr1
        unfold retRegs
        rw [mul_assoc, mul_assoc, gpow, gpow, ← pow_add, ← pow_add, ← gpow, ← gpow, e0, e1]
      rw [← hentry] at hsafe
      obtain ⟨k2, hk2, rr, hrr, hPost, hsafe2⟩ :=
        (W.callees j).tail (by omega) hPre hret hsafe
      have hcall : RLB S Prog L cert f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.1
        rw [hnr, frameWords_zero, ← hname] at h1
        convert h1 using 1
        rw [map_val]
        apply List.ext_getElem (by simp [frameWords, cellsOf_length] at hna ⊢; omega)
        intro i h1' h2'
        simp only [List.getElem_map, frameWords, List.getElem_range]
        have := sameOkB_sound hB' (tailArgsOk_sound hargs i (by simpa using h1'))
        rw [← this]
        unfold wd
        rw [mul_assoc, gpow, gpow, ← pow_add]
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hwords ⟨k2, by omega, rr, hrr, hsafe2⟩⟩, hP,
        fun J hJ ↦ by simp at hJ⟩

theorem walkB_ret (W : WalkEnvB S Prog cert L fp f X Kb) (vs : List Core.V) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) : WalkGoodB S Prog cert L fp f X Kb (.ret vs :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨hr, heq⟩ := chkL_ret hne
  rw [heq]
  unfold retOk at hr
  split at hr
  · rename_i se hse
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hr
    obtain ⟨⟨⟨⟨hkind, hlen⟩, hrun⟩, hpend⟩, hpost⟩ := hr
    obtain ⟨k2, hk2, hpse, -, -, -, k₀, hk₀, hreach⟩ := endAtB_ok hp hse
    refine ⟨⟨by rw [runAt_words hrun, hlen], fun hm ↦ ?_, fun p hp' ↦
      boundOkB_sound W.mem hpse.book hpse.bnd (hpost p hp')⟩, pendOkB_sound W hpse hpend,
      fun J hJ ↦ by simp at hJ⟩
    rw [hm] at hkind
    simp only [Bool.cond_false, decide_eq_true_eq] at hkind
    obtain ⟨hlt, -, -, rr, hreg, hsafe⟩ := hreach
    rw [hkind] at hreg
    exact ⟨k2, by omega, rr, hreg, hsafe⟩
  · simp at hr

mutual
/-- **The walk is sound.** -/
theorem walkB_sound (W : WalkEnvB S Prog cert L fp f X Kb) :
    ∀ (ss : List Core.Stmt) (st : CS) (P : List Core.Atom), WalkGoodB S Prog cert L fp f X Kb ss st P
  | [], st, P => walkB_nil W st P
  | .atom a :: ss, st, P => walkB_atom W a ss st P (walkB_sound W ss)
  | .ite c z n :: ss, st, P =>
    walkB_ite W c z n ss st P (walkB_sound W z) (walkB_sound W n) (walkB_sound W ss)
  | .match_ v arms :: ss, st, P => walkB_match W v arms ss st P (armsB_sound W arms) (walkB_sound W ss)
  | .call f' args rets :: ss, st, P => walkB_call W f' args rets ss st P (walkB_sound W ss)
  | .callIf c f' args :: ss, st, P => walkB_callIf W c f' args ss st P (walkB_sound W ss)
  | .dispatch v fs args rets :: ss, st, P => walkB_dispatch W v fs args rets ss st P (walkB_sound W ss)
  | .ret vs :: ss, st, P => walkB_ret W vs ss st P

theorem armsB_sound (W : WalkEnvB S Prog cert L fp f X Kb) :
    ∀ (arms : List (List Core.Stmt)) (e : ℕ) (he : e < arms.length) (st : CS)
      (P : List Core.Atom), WalkGoodB S Prog cert L fp f X Kb arms[e] st P
  | [], _, he, _, _ => absurd he (Nat.not_lt_zero _)
  | a :: _, 0, _, st, P => walkB_sound W a st P
  | _ :: as, e + 1, he, st, P => armsB_sound W as e (by simpa using he) st P
end

end Walk

/-! ## A function -/

section Reach

variable {C : Core.CallRel} {rd : Core.Reader} {σ : Core.Val}

mutual
/-- A statement holding leads on to its continuation or to a return. -/
theorem holdsB_reach : ∀ (s : Core.Stmt) {next : Prop} {kret : List E → Prop},
    Core.Stmt.HoldsB S C rd σ s next kret → next ∨ ∃ rs, kret rs
  | .atom _, _, _, h => Or.inl h.2
  | .ite c z n, _, _, h => by
    by_cases hc : σ c = 0
    · exact holdsListB_reach z (h.2.1 hc)
    · exact holdsListB_reach n (h.2.2 hc)
  | .match_ x arms, _, _, h => holdsArmsB_reach x arms 0 h
  | .call .., _, _, h => Or.inl h.2
  | .callIf .., _, _, h => Or.inl h.2.2
  | .dispatch .., _, _, h => Or.inl h.2
  | .ret _, _, _, h => Or.inr ⟨_, h⟩

theorem holdsListB_reach : ∀ (ss : List Core.Stmt) {next : Prop} {kret : List E → Prop},
    Core.Stmt.HoldsListB S C rd σ ss next kret → next ∨ ∃ rs, kret rs
  | [], _, _, h => Or.inl h
  | s :: ss, _, _, h => (holdsB_reach s h).elim (holdsListB_reach ss) Or.inr

theorem holdsArmsB_reach (x : Core.V) : ∀ (arms : List (List Core.Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, Core.Stmt.HoldsArmsB S C rd σ x j arms next kret → next ∨ ∃ rs, kret rs
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => h.elim (fun h ↦ holdsListB_reach a h.2) (holdsArmsB_reach x as (j + 1))
end

end Reach

section Fn

variable {κ : ℕ} {L : MemImage κ} {G : Glob} {f : CompiledFn} {cf : Core.Fn} {C : Cert}
  {cert : String → Cert}
  {Prog : Core.Program}

theorem bookOfB_holds {fp : K} : ∀ (ps : List (ℕ × Exec.Atom)) {B : Book}, BookHoldsB S L fp B →
    (∀ p ∈ ps, p.2.HoldsB S L fp) → BookHoldsB S L fp (bookOf ps B)
  | [], _, hB, _ => hB
  | p :: ps, B, hB, hp => by
    simp only [bookOf, Trie.seq_eq]
    refine bookOfB_holds ps (fun o a ha ↦ ?_) (fun q hq ↦ hp q (List.mem_cons_of_mem _ hq))
    rcases look_addKey ha with rfl | ha
    · exact hp p List.mem_cons_self
    · exact hB o a ha

/-! ### The cells of a window -/

/-! ### The valuation of a block -/

section Congr

variable {CR : Core.CallRel} {rd : Core.Reader} {σ σ' : Core.Val}

theorem atomB_congr {a : Core.Atom} (h : ∀ v ∈ atomVals a, σ v = σ' v) :
    a.HoldsB S rd σ ↔ a.HoldsB S rd σ' := by
  cases a with
  | frameAddr q run =>
    simp only [atomVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Atom.HoldsB, h.1]
    refine and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_congr' fun hk ↦ ?_
    rw [h.2 _ (List.getElem_mem hk)]
  | hint => simp [Core.Atom.HoldsB]
  | _ => simp_all [atomVals, Core.Atom.HoldsB]

mutual
theorem holdsB_congr : ∀ (s : Core.Stmt) {next : Prop} {kret : List E → Prop},
    (∀ v ∈ stmtVals s, σ v = σ' v) →
      (Core.Stmt.HoldsB S CR rd σ s next kret ↔ Core.Stmt.HoldsB S CR rd σ' s next kret)
  | .atom a, _, _, h => by
    simp only [Core.Stmt.HoldsB]
    rw [atomB_congr (by simpa [stmtVals] using h)]
  | .ite c z n, _, _, h => by
    simp only [stmtVals, List.mem_cons, List.mem_append, forall_eq_or_imp] at h
    simp only [Core.Stmt.HoldsB, h.1]
    rw [holdsListB_congr z fun v hv ↦ h.2 v (Or.inl hv), holdsListB_congr n fun v hv ↦ h.2 v (Or.inr hv)]
  | .match_ x arms, _, _, h => by
    simp only [stmtVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Stmt.HoldsB]
    exact holdsArmsB_congr x arms 0 h.1 h.2
  | .call f args rets, _, _, h => by
    simp only [stmtVals, List.mem_append] at h
    simp only [Core.Stmt.HoldsB]
    rw [List.map_congr_left fun v hv ↦ h v (Or.inl hv), List.map_congr_left fun v hv ↦ h v (Or.inr hv)]
  | .callIf c f args, _, _, h => by
    simp only [stmtVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Stmt.HoldsB, h.1]
    rw [List.map_congr_left h.2]
  | .dispatch x fs args rets, _, _, h => by
    simp only [stmtVals, List.mem_cons, List.mem_append, forall_eq_or_imp] at h
    simp only [Core.Stmt.HoldsB, h.1]
    rw [List.map_congr_left fun v hv ↦ h.2 v (Or.inl hv),
      List.map_congr_left fun v hv ↦ h.2 v (Or.inr hv)]
  | .ret vs, _, _, h => by
    simp only [Core.Stmt.HoldsB]
    rw [List.map_congr_left fun v hv ↦ h v (by simpa [stmtVals] using hv)]

theorem holdsListB_congr : ∀ (ss : List Core.Stmt) {next : Prop} {kret : List E → Prop},
    (∀ v ∈ stmtsVals ss, σ v = σ' v) →
      (Core.Stmt.HoldsListB S CR rd σ ss next kret ↔ Core.Stmt.HoldsListB S CR rd σ' ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, _, _, h => by
    simp only [stmtsVals, List.mem_append] at h
    simp only [Core.Stmt.HoldsListB]
    rw [holdsListB_congr ss fun v hv ↦ h v (Or.inr hv)]
    exact holdsB_congr s fun v hv ↦ h v (Or.inl hv)

theorem holdsArmsB_congr (x : Core.V) : ∀ (arms : List (List Core.Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, σ x = σ' x → (∀ v ∈ armsVals arms, σ v = σ' v) →
      (Core.Stmt.HoldsArmsB S CR rd σ x j arms next kret ↔ Core.Stmt.HoldsArmsB S CR rd σ' x j arms next kret)
  | [], _, _, _, _, _ => Iff.rfl
  | a :: as, j, _, _, hx, h => by
    simp only [armsVals, List.mem_append] at h
    simp only [Core.Stmt.HoldsArmsB, hx]
    rw [holdsListB_congr a fun v hv ↦ h v (Or.inl hv), holdsArmsB_congr x as (j + 1) hx fun v hv ↦ h v (Or.inr hv)]
end

end Congr

/-! ### A window -/

variable (S) in
/-- **The run at window `i`'s start** with `k` steps left: there, its environment and the facts
and bounds handed on hold. -/
def WinStartB (L : MemImage κ) (fp : K) (f : CompiledFn) (C : Cert) (i k : ℕ) : Prop :=
  SafeB S guest L k ⟨gpow (f.entry + (C.cutAt i).J), fp⟩ ∧ EnvHolds L fp (envOf (C.cutAt i).env) ∧
    (∀ p ∈ (C.cutAt i).facts, p.2.HoldsB S L fp) ∧ BndHolds L fp (C.cutAt i).bnd

variable (S) in
/-- What a function's return does, in every window's context. -/
abbrev RetOfB (L : MemImage κ) (fp : K) (G : Glob) (f : CompiledFn) (cf : Core.Fn) (C : Cert)
    (main : Bool) (Kb : ℕ) : List E → Prop :=
  RetWordsB S L fp (C.fxAt G f cf main 0 [] .nil .nil) Kb

/-- **A checked window's run**, from its start with `k ≤ Kb` steps left, the windows' cells
consecutive: its statements hold under the function's valuation, and the run reaches the next
window's start, or, the last window, its statements end by the return; the first window has the
parameters in their cells. -/
theorem checkWinB_run {main : Bool} {i : ℕ} (hc : checkWin G f cf C main i = true)
    (hcont : Cont C C.cuts.length) (hiN : i ≤ C.cuts.length)
    (hf : f ∈ Data.functions) (hpows : C.facts.pows.Ok) (hκ : κ ≤ 32) {fp : K}
    (hfp : C.facts.fpOne = true → fp = 1) {Kb : ℕ}
    (hC : ∀ j, FunSpecLtB S guest L Kb (G.sig j).entry (Pre G L j) (PostB S Prog G L cert j))
    (hjt : JTHolds G L) (hmem : MemPre L fp C.mem) (hknown : MemKnown L fp (C.cutAt i).known)
    (hsems : SemHolds G L fp (C.cutAt i).sems) {k : ℕ} (hk : k ≤ Kb) (hs : WinStartB S L fp f C i k) :
    (i = 0 → ∀ m (hm : m < cf.params.length), C.locs.getD cf.params[m].idx 0 = 2 + m) ∧
    (i < C.cuts.length → Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C)
        (C.stmtsAt cf i) True (RetOfB S L fp G f cf C main Kb) ∧
        (C.cutAt i).start ≤ (C.cutAt (i + 1)).start ∧ ∃ k' ≤ k, WinStartB S L fp f C (i + 1) k') ∧
    (C.cuts.length ≤ i → Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C)
        (C.stmtsAt cf i) False (RetOfB S L fp G f cf C main Kb)) := by
  have hins := (checkWin_parts hc).2
  unfold checkWin at hc
  rcases hR : execWin C.facts f (C.cutAt i).J (C.cutAt i).env (C.endAt f i) with ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, hcov⟩, hlink⟩, h0⟩, hc⟩ := hc
  have hval : ∀ {v : Core.V} {c : ℕ}, getF (C.locAt i) v.idx = some c → C.locs.getD v.idx 0 = c :=
    fun h ↦ locAt_val hcont hiN hins rfl h
  have hcongr : ∀ v ∈ stmtsVals (C.stmtsAt cf i), val L fp (C.locAt i) v = valG L fp C v := by
    intro v hv
    have := List.all_eq_true.mp hcov v hv
    obtain ⟨c, hcv⟩ := Option.isSome_iff_exists.mp this
    simp only [val, valG, cellOf, getF_eq] at hcv ⊢
    rw [hcv, hval (by rwa [getF_eq]), Option.getD_some]
  set X : Fx := C.fxAt G f cf main i segs (index segs) (C.locAt i) with hX
  have hctx : Exec.Ctx C.facts κ fp := ⟨hpows, hfp, hκ⟩
  have H : WalkHypB S L fp f X := ⟨hctx, guest_fetches hf, rfl, fun s hs ↦
    execWinB_good hctx (guest_fetches hf) _ _ _ s (by rw [hR]; exact hs), rfl, hlink⟩
  have W : WalkEnvB S Prog cert L fp f X Kb := ⟨H, hjt, hmem, hknown, hsems, hC⟩
  have hret : RetWordsB S L fp X Kb = RetOfB S L fp G f cf C main Kb := rfl
  have hconv : ∀ {N : Prop}, Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (val L fp X.loc)
      (C.stmtsAt cf i) N (RetWordsB S L fp X Kb) →
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C) (C.stmtsAt cf i) N
        (RetOfB S L fp G f cf C main Kb) := fun h ↦
    hret ▸ (holdsListB_congr _ hcongr).mp h
  refine ⟨fun hi m hm ↦ ?_, ?_⟩
  · subst hi
    simp only [beq_self_eq_true, Bool.cond_true, Bool.and_eq_true] at h0
    have := runAt_sound h0.1 m hm
    unfold cellOf at this
    rcases hg : getF (C.locAt 0) cf.params[m].idx with _ | c
    · rw [hg, Option.getD_none] at this; omega
    · rw [hg, Option.getD_some] at this
      rw [hval hg, this]
  split at hc
  · rename_i st hst
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hsub, hend⟩ := hc
    have hrun : SegRunB S L fp f X Kb (C.cutAt i).J k := by
      refine ⟨hs.1, fun s hs' hs0 ↦ ?_, fun _ hn ↦ ?_⟩
      swap
      · unfold segAt at hst
        rw [getF_eq, hn] at hst
        cases hst
      have hmem : s ∈ X.segs := index_get hs'
      have hs'' : st.seg = s := by
        unfold segAt at hst
        rw [getF_eq, hs'] at hst
        simp only [hs0, beq_self_eq_true, Bool.cond_true, Option.some.injEq] at hst
        rw [← hst]
      have he : EnvHolds L fp s.env := hs'' ▸ hs.2.1.sub hsub
      refine ⟨hmem, he, k, hk, le_rfl, (H.good s hmem).1 k he ?_⟩
      rw [hs0]
      exact hs.1
    have hp := segAtB_ok H hst hrun (bookOfB_holds _ BookHoldsB.nil hs.2.2.1) hs.2.2.2
    unfold winEnd at hend
    by_cases hi : i < C.cuts.length
    · have hb : Nat.blt i C.cuts.length = true := Nat.blt_eq.mpr hi
      rw [hb] at hend
      simp only [Bool.cond_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hend
      obtain ⟨⟨hchk, hle⟩, henv⟩ := hend
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd hi (Nat.not_lt.mpr h)⟩
      obtain ⟨hl, -, harr⟩ := walkB_sound W (C.stmtsAt cf i) st [] k True hp
        (by rw [hchk]; simp) (fun _ _ _ _ _ ↦ trivial)
      obtain ⟨k', hk', ⟨hsafe, hseg, hwend⟩, hhand⟩ := harr _ hchk
      refine ⟨hconv hl, hle, k', hk', hsafe, ?_, ?_⟩
      · split at henv
        · rename_i s hs'
          simp only [Bool.and_eq_true, beq_iff_eq] at henv
          rw [getF_eq] at hs'
          exact (hseg s hs' henv.1).2.1.sub henv.2
        · rename_i hs'
          rw [getF_eq] at hs'
          have := hwend (by simp only [hX, Cert.fxAt, hb, Bool.cond_true]) hs'
          simpa only [hX, Cert.fxAt, hb, Bool.cond_true] using this
      · have hw : X.win = some ((C.cutAt (i + 1)).J, (C.cutAt (i + 1)).facts, (C.cutAt (i + 1)).bnd) := by
          simp only [hX, Cert.fxAt, hb, Bool.cond_true]
        exact hhand _ _ _ hw rfl
    · have hb : Nat.blt i C.cuts.length = false := blt_false (Nat.not_lt.mp hi)
      rw [hb] at hend
      simp only [Bool.cond_false, beq_iff_eq] at hend
      refine ⟨fun h ↦ absurd h hi, fun _ ↦ ?_⟩
      obtain ⟨hl, -, -⟩ := walkB_sound W (C.stmtsAt cf i) st [] k False hp
        (by rw [hend]; simp) (fun J hJ ↦ by rw [hend] at hJ; cases hJ)
      exact hconv hl
  · simp at hc

/-- **A checked function's run**, from its entry with `k` steps left, every window checked and
each window's memory bounds and semantic pairs given by the statements before it: its located
core relation holds of its frame, and a run of a function other than `main` returns in fewer
steps. Its frame is in the memory and its body holds under the frame's valuation, `cert cf.name`
being its certificate. -/
theorem checkWinsB_run {main : Bool} (hc : ∀ i ≤ C.cuts.length, checkWin G f cf C main i = true)
    (hf : f ∈ Data.functions) (hfind : Prog.find? cf.name = some cf) (hpows : C.facts.pows.Ok)
    (hκ : κ ≤ 32) {fp : K} (hfp : C.facts.fpOne = true → fp = 1) {k : ℕ}
    (hcert : cert cf.name = C)
    (hC : ∀ i, FunSpecLtB S guest L k (G.sig i).entry (Pre G L i) (PostB S Prog G L cert i))
    (hjt : JTHolds G L) (henv : EnvHolds L fp C.facts.entryEnv) (hpre : BndHolds L fp C.pre)
    (hmem : MemPre L fp C.mem) (hsem : SemHolds G L fp C.sem)
    (hknown : ∀ i ≤ C.cuts.length, 0 < i → Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read
      (valG L fp C) (cf.body.take (C.cutAt i).start) True (fun _ ↦ True) →
        MemKnown L fp (C.cutAt i).known ∧ SemHolds G L fp (C.cutAt i).sems)
    (hsafe : SafeB S guest L k ⟨gpow f.entry, fp⟩) :
    RLB S Prog L cert cf.name (frameWords L fp 2 cf.params.length)
        (frameWords L fp (2 + cf.params.length) C.nret) ∧ BndHolds L fp C.post ∧
      (main = false → ∃ k' < k, ∃ r, retRegs L fp = some r ∧ SafeB S guest L k' r) ∧
      InMem κ fp ∧ cf.params.map (valG L fp C) = frameWords L fp 2 cf.params.length ∧
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C) cf.body False
        (fun rs ↦ rs = frameWords L fp (2 + cf.params.length) C.nret) := by
  have hcont := cont_of hc
  have run := fun i (hi : i ≤ C.cuts.length) {k'} hk' hs (hkn : _ ∧ _) ↦
    checkWinB_run (Prog := Prog) (hc i hi) hcont hi hf hpows hκ hfp hC hjt hmem hkn.1 hkn.2 (k := k')
      hk' hs
  have hkn0 : MemKnown L fp (C.cutAt 0).known ∧ SemHolds G L fp (C.cutAt 0).sems :=
    ⟨fun _ h ↦ by simp [Cert.cutAt] at h, hsem⟩
  have hs0 : WinStartB S L fp f C 0 k :=
    ⟨by simpa [Cert.cutAt] using hsafe, henv, by simp [Cert.cutAt], hpre⟩
  have reach : ∀ i ≤ C.cuts.length, ∃ k' ≤ k, WinStartB S L fp f C i k' ∧
      Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C)
        (cf.body.take (C.cutAt i).start) True (RetOfB S L fp G f cf C main k) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨k, le_rfl, hs0, ?_⟩
      simp [Cert.cutAt, Core.Stmt.HoldsListB]
    | succ i ih =>
      intro hi
      obtain ⟨k', hk', hs, hl⟩ := ih (by omega)
      have hkn : MemKnown L fp (C.cutAt i).known ∧ SemHolds G L fp (C.cutAt i).sems := by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact hkn0
        · exact hknown i (by omega) hi0
            (Core.holdsListB_mono (fun _ _ _ h ↦ h) _ id (fun _ _ ↦ trivial) hl)
      obtain ⟨hw, hle, k'', hk'', hs'⟩ := (run i (by omega) hk' hs hkn).2.1 (by omega)
      refine ⟨k'', by omega, hs', ?_⟩
      rw [← stmtsAt_lt (by omega) hle, Core.holdsListB_append]
      exact Core.holdsListB_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ hw) (fun _ h ↦ h) hl
  obtain ⟨k', hk', hs, hl⟩ := reach _ le_rfl
  have hkn : MemKnown L fp (C.cutAt C.cuts.length).known ∧
      SemHolds G L fp (C.cutAt C.cuts.length).sems := by
    rcases Nat.eq_zero_or_pos C.cuts.length with h0 | hi0
    · rw [h0]; exact hkn0
    · exact hknown _ le_rfl hi0 (Core.holdsListB_mono (fun _ _ _ h ↦ h) _ id (fun _ _ ↦ trivial) hl)
  have hr := run _ le_rfl hk' hs hkn
  have hlast := hr.2.2 le_rfl
  have hall : Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C) cf.body False
      (RetOfB S L fp G f cf C main k) := by
    rw [← stmtsAt_last (C := C) (i := C.cuts.length) le_rfl, Core.holdsListB_append]
    exact Core.holdsListB_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ hlast) (fun _ h ↦ h) hl
  have hparams := (run 0 (Nat.zero_le _) le_rfl hs0 hkn0).1 rfl
  obtain ⟨rs, hw, hback, hpost⟩ := (holdsListB_reach cf.body hall).resolve_left id
  have hpar : cf.params.map (valG L fp C) = frameWords L fp 2 cf.params.length := by
    apply List.ext_getElem (by simp [frameWords])
    intro m h1 h2
    simp only [List.getElem_map, frameWords, List.getElem_range, valG]
    rw [hparams m (by simpa using h1)]
  have hbody : Core.Stmt.HoldsListB S (RLB S Prog L cert) L.read (valG L fp C) cf.body False
      (fun rs ↦ rs = frameWords L fp (2 + cf.params.length) C.nret) :=
    Core.holdsListB_mono (fun _ _ _ h ↦ h) cf.body id (fun rs h ↦ h.1) hall
  have hA : InMem κ fp := by
    cases main with
    | true =>
      have h1 : fp = 1 := hfp (checkWin_fpOne (hc 0 (Nat.zero_le _))).symm
      exact ⟨0, Nat.two_pow_pos _, by rw [h1]; simp [gpow]⟩
    | false =>
      obtain ⟨-, -, r, hr, -⟩ := hback rfl
      unfold retRegs at hr
      obtain ⟨d, hd, -⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨i, hi, -⟩ := (Core.read_some_iff (by omega) L _ d).mp hd
      exact ⟨i, i.isLt, by simpa [gpow] using hi⟩
  have hval : frameVal L cert cf.name fp = valG L fp C := by rw [frameVal, hcert]
  refine ⟨(Core.relLB_iff Prog _ _ _).mpr ⟨cf, fp, hfind, hA, ?_, ?_⟩, hpost,
    fun hm ↦ hback hm, hA, hpar, hbody⟩
  · rw [hval]; exact hpar
  · rw [hval]; exact hbody

end Fn

end
end LeanVM.Guest.Check
