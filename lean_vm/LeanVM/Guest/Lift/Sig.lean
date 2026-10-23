/-
  LeanVM.Guest.Lift.Sig

  The signature verifiers' completeness in the uniform placed form (`CompleteAtD`), from B1's
  `Rel`-level completeness: they place nothing and call nothing, and their loads read the caller's
  words.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Sig.Interface

/-!
# The signature verifiers, placed

**A pure function whose loads read the caller's words** is complete in the placed form
(`completeAtD_of_relIn`): if on every memory defined below `2^κ` and holding the caller's words
`Lin` its relation holds by a tree loading from `Lin` only (`Program.RelIn`), then on a memory
`rd1` kept on `Lin` and below `2^κ` (`lowLin`) one tree serves, placed at every frame pointer, every
memory defined below `2^κ` and holding `Lin` (`relAtIn_uniform_pure`).

**Leaf bodies.** `Stmt.leafOk lok`: a body of atoms, branches and arms only (no call, no
`callIf`, no dispatch), every atom placing nothing (`atomUnplaced`) and passing `lok`. Its walks'
events are its atoms and branch conditions (`walk_leafOk`), so a valid tree of it has no callee,
and its function is pure on its own (`pureIn_of_leafOk`).

**`verify_lean_xmss`** is such a body whose only loads are the claim's four words at its argument
(`claimLoad`, by the kernel: `xmss_leafOk`). With B1's completeness (`verify_lean_xmss_rel`), on a
memory defined below `2^κ`, `κ ≥ 6`, holding a signed claim at `p` whose four words lie in the
caller's words, it is complete placed (`verify_lean_xmss_completeAtD`).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 (LowDef Within CompleteAtD Returns disj_nil relAtIn_dmono)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Placed completeness from `RelIn` on every low memory -/

/-- The memory `rd1` kept on the caller's words and below `2^κ`. -/
noncomputable def lowLin (rd1 : Reader) (κ : ℕ) (Lin : Layout) : Reader :=
  B1.Main.restrict rd1 fun i => RegionL Lin i ∨ i < 2 ^ κ

theorem lowLin_low {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hl : LowDef κ rd1) :
    LowDef κ (lowLin rd1 κ Lin) := fun i hi => by
  rw [lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inr hi⟩]
  exact hl i hi

theorem lowLin_memL {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL : MemL rd1 Lin) :
    MemL (lowLin rd1 κ Lin) Lin :=
  B1.Main.memL_restrict hL fun _ hi => Or.inl hi

/-- **A pure function loading the caller's words, placed**: its relation on every memory defined
below `2^κ` and holding `Lin`, by trees loading from `Lin`, gives it at every frame pointer by one
tree. -/
theorem completeAtD_of_relIn {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {κ : ℕ} {Lin : Layout} {args rets : List E}
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) g args rets) :
    CompleteAtD fs cert κ g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (h _ (lowLin_low (Lin := Lin) hl1) (lowLin_memL hL1))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inl hi⟩, B1.Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := B1.Main.restrict_supp' rd1 _ _ _ hv
    · rw [B1.Main.memL_agree hL' hL1 i hi, ← B1.Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## Leaf bodies -/

mutual
/-- A statement of atoms, branches and arms only, its atoms placing nothing and passing `lok`. -/
def Stmt.leafOk (lok : Atom → Bool) : Stmt → Bool
  | .atom a => atomUnplaced a && lok a
  | .ite _ z n => Stmt.leafOkList lok z && Stmt.leafOkList lok n
  | .match_ _ arms => Stmt.leafOkArms lok arms
  | .ret _ => true
  | _ => false

/-- A block of `leafOk` statements. -/
def Stmt.leafOkList (lok : Atom → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.leafOk lok s && Stmt.leafOkList lok ss

/-- Arms of `leafOk` blocks. -/
def Stmt.leafOkArms (lok : Atom → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.leafOkList lok a && Stmt.leafOkArms lok as
end

/-- An event of a leaf body's walk: an atom passing `lok`, or a branch condition. -/
def EvLeafOk (lok : Atom → Bool) : Ev → Prop
  | .atom a => lok a = true
  | .inK _ => True
  | _ => False

section Walk

variable {lok : Atom → Bool} {σ : Val}

mutual
theorem walk1_leafOk : ∀ (s : Stmt), Stmt.leafOk lok s = true → (walk1 σ s).All (EvLeafOk lok)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      exact h.2
  | .ite c z n, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_leafOk z h.1
      · exact walk_leafOk n h.2
  | .match_ x arms, h => walkArms_leafOk x arms 0 h
  | .call .., h => by simp [Stmt.leafOk] at h
  | .callIf .., h => by simp [Stmt.leafOk] at h
  | .dispatch .., h => by simp [Stmt.leafOk] at h
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_leafOk : ∀ (ss : List Stmt), Stmt.leafOkList lok ss = true →
    (walk σ ss).All (EvLeafOk lok)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.leafOkList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_leafOk ss h.2) (walk1_leafOk s h.1)

theorem walkArms_leafOk (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    Stmt.leafOkArms lok arms = true → (walkArms σ x j arms).All (EvLeafOk lok)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.leafOkArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_leafOk a h.1
      · exact walkArms_leafOk x as (j + 1) h.2
end

end Walk

mutual
theorem leafOk_pure {lok : Atom → Bool} (S : List String) :
    ∀ (s : Stmt), Stmt.leafOk lok s = true → Stmt.pure S s = true
  | .atom _, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      exact h.1
  | .ite _ z n, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      simp only [Stmt.pure, leafOkList_pure S z h.1, leafOkList_pure S n h.2, Bool.and_self]
  | .match_ _ arms, h => by
      simp only [Stmt.leafOk] at h
      simp only [Stmt.pure, leafOkArms_pure S arms h]
  | .call .., h => by simp [Stmt.leafOk] at h
  | .callIf .., h => by simp [Stmt.leafOk] at h
  | .dispatch .., h => by simp [Stmt.leafOk] at h
  | .ret _, _ => rfl

theorem leafOkList_pure {lok : Atom → Bool} (S : List String) :
    ∀ (ss : List Stmt), Stmt.leafOkList lok ss = true → Stmt.pureList S ss = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.leafOkList, Bool.and_eq_true] at h
      simp only [Stmt.pureList, leafOk_pure S s h.1, leafOkList_pure S ss h.2, Bool.and_self]

theorem leafOkArms_pure {lok : Atom → Bool} (S : List String) :
    ∀ (arms : List (List Stmt)), Stmt.leafOkArms lok arms = true → Stmt.pureArms S arms = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Stmt.leafOkArms, Bool.and_eq_true] at h
      simp only [Stmt.pureArms, leafOkList_pure S a h.1, leafOkArms_pure S as h.2, Bool.and_self]
end

/-- A function with a leaf body is pure on its own. -/
theorem pureIn_of_leafOk {lok : Atom → Bool} {g : String} {fn : Fn}
    (hf : coreProgram.find? g = some fn) (h : Stmt.leafOkList lok fn.body = true) :
    coreProgram.PureIn [g] := by
  intro g' hg' fn' hf'
  rw [List.mem_singleton] at hg'
  subst hg'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact leafOkList_pure _ _ h

theorem calls_nil_of_leafOk {lok : Atom → Bool} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk lok e) :
    calls es = [] := by
  rw [calls, List.filterMap_eq_nil_iff]
  intro e he
  have := h e he
  cases e <;> simp_all [EvLeafOk, Ev.call?]

/-- **A leaf's relation, loading from `R`**: when its walk's loads lie in `R`. -/
theorem relIn_of_leaf {lok : Atom → Bool} {g : String} {fn : Fn} {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hf : coreProgram.find? g = some fn)
    (hleaf : Stmt.leafOkList lok fn.body = true)
    (hload : ∀ σ es vs, fn.params.map σ = args → walk σ fn.body = .ret es vs →
      ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i)
    (h : coreProgram.Rel rd g args rets) : coreProgram.RelIn rd R g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree coreProgram_wf h
  refine ⟨t, hn, hv, hb, ?_⟩
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs, hw, -, -, hkv⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hall := walk_leafOk (σ := σ) _ hleaf
    rw [hw] at hall
    have hc := calls_nil_of_leafOk hall
    rw [hc] at hkv
    match kids, hkv with
    | [], _ =>
      rw [Tree.LoadsR, events_node hf hw]
      exact ⟨hload σ es vs hp hw, trivial⟩

/-! ## `verify_lean_xmss` -/

/-- A load of the argument `.n 0` at an offset below 4; no other load. -/
def claimLoad : Atom → Bool
  | .load _ p off => decide (p = .n 0) && decide (off < 4)
  | _ => true

set_option maxRecDepth 100000 in
/-- **`verify_lean_xmss`'s body**: atoms, branches and arms, its loads the claim's words. -/
theorem xmss_leafOk : Stmt.leafOkList claimLoad Data.core19.body = true := by decide +kernel

theorem loads_claim {σ : Val} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk claimLoad e) :
    ∀ A ∈ loadAddrs σ es, ∃ off < 4, A = (σ (.n 0)).limb 0 * gpow off := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [EvLeafOk, claimLoad, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact ⟨off, hok.2, by rw [← hea, hok.1]⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem xmss_pure : coreProgram.PureIn ["verify_lean_xmss"] :=
  pureIn_of_leafOk B1.Sig.find_verify_lean_xmss xmss_leafOk

set_option maxRecDepth 100000 in
/-- **`verify_lean_xmss` loads only the claim**, from B1's completeness. -/
theorem verify_lean_xmss_relIn (hc : B1.Sig.verify_lean_xmss_complete_Spec) {rd : Reader}
    {R : ℕ → Prop} {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hrd : B1.Sig.MemOK rd 64)
    (hat : B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
      (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true)
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i) :
    coreProgram.RelIn rd R "verify_lean_xmss" [p] [] :=
  relIn_of_leaf B1.Sig.find_verify_lean_xmss xmss_leafOk
    (fun σ es vs hp hw A hA => by
      have hall : (Out.ret es vs).All (EvLeafOk claimLoad) := by
        have := walk_leafOk (σ := σ) Data.core19.body xmss_leafOk
        exact (show walk σ Data.core19.body = .ret es vs from hw) ▸ this
      obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
      rw [B1.Sig.core19_params] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
      rw [hp]
      exact hreg off hoff)
    (B1.Sig.verify_lean_xmss_rel hc hrd hat hv)

/-- **`verify_lean_xmss` is complete, placed**: on memories defined below `2^κ`, `κ ≥ 6`, holding
the caller's words `Lin`, among them the four words of a claim at `p` that `sig` verifies. -/
theorem verify_lean_xmss_completeAtD (hc : B1.Sig.verify_lean_xmss_complete_Spec) {κ : ℕ}
    (hκ : 6 ≤ κ) {Lin : Layout} {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i)
    (hat : ∀ rd, LowDef κ rd → MemL rd Lin →
      B1.Sig.ClaimAt rd p (B1.Sig.cellOf128 pk.root) (B1.Sig.cellOf128 pk.parameter)
        (B1.Sig.cellOf128 (m.extractLsb' 0 128)) (B1.Sig.cellOf128 (m.extractLsb' 128 128)))
    (hv : Node.xmssVerify pk m sig = true) :
    CompleteAtD fs cert κ "verify_lean_xmss" Lin [p] (Returns []) :=
  completeAtD_of_relIn xmss_pure (List.mem_singleton_self _) fun rd hl hL =>
    verify_lean_xmss_relIn hc
      (fun i hi => hl i (lt_of_lt_of_le hi (show 64 ≤ 2 ^ κ from
        (show (64 : ℕ) = 2 ^ 6 from rfl) ▸ Nat.pow_le_pow_right (by decide) hκ)))
      (hat rd hl hL) hv hreg

end
end LeanVM.Guest.Lift
