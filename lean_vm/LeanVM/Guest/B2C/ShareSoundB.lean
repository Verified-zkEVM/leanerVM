/-
  LeanVM.Guest.B2C.ShareSoundB

  Soundness of the sharing check (`ShareSound.lean`) under any functional semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.ShareSound
public import LeanVM.Guest.CheckSoundB
public import LeanVM.Guest.Memory.EvalB

/-!
# Soundness of the sharing check under any `BLAKE2S` semantics

`ShareSound.lean`'s keys and invariant with `S : BlakeSem` a parameter: `KeyHoldsB` (a
compression key asks `S.check` of its cells), `InvB`, `ConcB`, and the lemmas (`nameVB_inv`,
`keysOfB_sound`, `pfOkB_sound`, `stepAtomB_inv`, `swLB_sound`, `refinesB_inv`, `chainB_sound`,
`shareOkB_path`, …). The compiled code shares equal compressions, so a key's output being a
function of its inputs (`KeyHoldsB.unique`) needs the semantics functional (`SemFunctional S`, the
body of `E2E/Complete/Table.lean`'s `Functional`): the lemmas that read a pending value's keys
(`pfOkB_sound` and what rests on it, `shareOkB_path`) take `hfun : SemFunctional S`.

* `keyHoldsB_deployed`, `invB_deployed`, `concB_deployed`: at `blakeDeployed`, they are
  `ShareSound.lean`'s; `semFunctional_deployed`: the deployed semantics is functional.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

variable {S : BlakeSem}

/-! ## Keys -/

variable (S) in
/-- **What a key says** of an output word and its inputs' words: a sum, a product, one of the two
words of a compression, a load at offset `op - 4`. -/
def KeyHoldsB (rd : Reader) (out : E) : ℕ → List E → Prop
  | 0, [a, b] => out = a + b
  | 1, [a, b] => out = a * b
  | 2, [m0, m1, m2, m3, c0, c1, md] => ∃ o1, S.check ![m0, m1, m2, m3] c0 c1 out o1 md
  | 3, [m0, m1, m2, m3, c0, c1, md] => ∃ o0, S.check ![m0, m1, m2, m3] c0 c1 o0 out md
  | n + 4, [p] => LoadHolds rd p n out
  | _, _ => False

/-- **A semantics of `BLAKE2S` is functional** when a row's inputs determine its output (the
body of `E2E/Complete/Table.lean`'s `Functional`): the compiled code shares equal compressions,
so its shared cells are sound only then. -/
def SemFunctional (S : BlakeSem) : Prop :=
  ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 o0' o1' md : E}, S.check m cv0 cv1 o0 o1 md →
    S.check m cv0 cv1 o0' o1' md → o0 = o0' ∧ o1 = o1'

/-- **A key's output is a function of its inputs**, the semantics being functional. -/
theorem KeyHoldsB.unique (hfun : SemFunctional S) {rd : Reader} {x y : E} :
    ∀ {op : ℕ} {ins : List E}, KeyHoldsB S rd x op ins → KeyHoldsB S rd y op ins → x = y
  | 0, [_, _], hx, hy => hx.trans hy.symm
  | 1, [_, _], hx, hy => hx.trans hy.symm
  | 2, [_, _, _, _, _, _, _], ⟨_, hx⟩, ⟨_, hy⟩ => (hfun hx hy).1
  | 3, [_, _, _, _, _, _, _], ⟨_, hx⟩, ⟨_, hy⟩ => (hfun hx hy).2
  | _ + 4, [_], hx, hy => Option.some.inj (hx.2.symm.trans hy.2)

/-- A sum's and a product's inputs in either order. -/
theorem keyHoldsB_keyCells {rd : Reader} {x : E} {Ψ : ℕ → E} (op : ℕ) (cs : List ℕ) :
    KeyHoldsB S rd x op ((keyCells op cs).map Ψ) ↔ KeyHoldsB S rd x op (cs.map Ψ) := by
  match op, cs with
  | 0, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [KeyHoldsB, add_comm]
  | 1, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [KeyHoldsB, mul_comm]
  | 0, [] => simp [keyCells]
  | 0, [_] => simp [keyCells]
  | 0, _ :: _ :: _ :: _ => simp [keyCells]
  | 1, [] => simp [keyCells]
  | 1, [_] => simp [keyCells]
  | 1, _ :: _ :: _ :: _ => simp [keyCells]
  | n + 2, cs => simp [keyCells]

/-! ## The invariant -/

section Inv

variable (cg : V → ℕ) (rd : Reader) (σ : Val)

variable (S) in
/-- **What the state says** of a path whose values named so far are `pre`, for the cells' words
`Ψ`, the values' cells being `cg`. -/
structure InvB (st : SSt) (pre : List V) (Ψ : ℕ → E) : Prop where
  vn : ∀ v ∈ pre, v = V.n v.idx
  occ : ∀ v ∈ pre, 2 ≤ cg v → st.occ.testBit (cg v)
  good : ∀ v ∈ pre, 2 ≤ cg v → isPend st v.idx = false → σ v = Ψ (cg v)
  named : ∀ n, isNamed st n = true → 2 ≤ cg (V.n n) →
    σ (V.n n) = Ψ (cg (V.n n)) ∧ st.occ.testBit (cg (V.n n))
  kc : ∀ c x, getF st.cst c = some x → st.occ.testBit c ∧ Ψ c = tw x
  keys : ∀ c, ∀ k ∈ (getF st.keys c).getD [], KeyHoldsB S rd (Ψ c) k.1 (k.2.map Ψ) ∧
    st.occ.testBit c ∧ ∀ c' ∈ k.2, st.occ.testBit c'
  pend : ∀ p ∈ st.pend, cg (V.n p.v) = p.c ∧ 2 ≤ p.c ∧ st.occ.testBit p.c ∧
    (∀ x, p.kc = some x → σ (V.n p.v) = tw x) ∧
    (∀ k ∈ p.keys, KeyHoldsB S rd (σ (V.n p.v)) k.1 (k.2.map fun u ↦ σ (V.n u))) ∧
    (∀ x ∈ p.eqs, σ (V.n p.v) = σ (V.n x))

variable {cg rd σ}

variable {loc : Loc} {sh : ℕ}

/-- **Naming a value** keeps the invariant: `Ψ` changes only at a cell nothing occupied. -/
theorem nameVB_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} {st : SSt} {pre : List V} {Ψ : ℕ → E} {v : V}
    (hI : InvB S cg rd σ st pre Ψ) (hv : v = V.n v.idx) (hcg : loc.cell v = cg v)
    (hkc : ∀ x, kc v.idx = some x → σ v = tw x) :
    ∃ Ψ', InvB S cg rd σ (nameV loc sh kc st v) (pre ++ [v]) Ψ' ∧ Step st Ψ (nameV loc sh kc st v) Ψ' := by
  have hvn : ∀ u ∈ pre ++ [v], u = V.n u.idx := fun u hu ↦ by
    rcases List.mem_append.mp hu with hu | hu
    · exact hI.vn u hu
    · rw [List.mem_singleton.mp hu]; exact hv
  have hcv : cg (V.n v.idx) = cg v := by rw [← hv]
  cases hnp : (isNamed st v.idx || isPend st v.idx)
  · -- a value not named before
    have hnp' := hnp
    simp only [Bool.or_eq_false_iff] at hnp'
    obtain ⟨hn, hp⟩ := hnp'
    by_cases h2 : loc.cell v < 2
    · rw [nameV_low hnp h2]
      refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, fun n hn' hc ↦ ?_, hI.kc, hI.keys, hI.pend⟩,
        Step.refl _ _⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.occ u hu hc
        · rw [List.mem_singleton.mp hu] at hc; omega
      · rcases List.mem_append.mp hu with hu | hu
        · exact hI.good u hu hc hpe
        · rw [List.mem_singleton.mp hu] at hc; omega
      · simp only [isNamed_eq, testBit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hn'
        rcases hn' with hn' | rfl
        · exact hI.named n (by rw [isNamed_eq]; exact hn') hc
        · rw [hcv] at hc; omega
    · have h2' : 2 ≤ loc.cell v := by omega
      cases ho : st.occ.testBit (loc.cell v)
      · -- the first value at its cell
        rw [nameV_fresh hnp h2' ho]
        have ho' : st.occ.testBit (cg v) = false := by rw [← hcg]; exact ho
        have hne : ∀ c', st.occ.testBit c' = true → c' ≠ cg v := fun c' h he ↦ by
          rw [he, ho'] at h; cases h
        refine ⟨Function.update Ψ (cg v) (σ v), ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_,
          fun n hn' hc ↦ ?_, fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp ↦ ?_⟩, fun c hc ↦ ?_⟩
        · rw [testBit_setBit, Bool.or_eq_true, decide_eq_true_eq]
          rcases List.mem_append.mp hu with hu | hu
          · exact Or.inl (hI.occ u hu hc)
          · rw [List.mem_singleton.mp hu, hcg]; exact Or.inr rfl
        · rcases List.mem_append.mp hu with hu | hu
          · rw [Function.update_of_ne (hne _ (hI.occ u hu hc))]
            exact hI.good u hu hc hpe
          · rw [List.mem_singleton.mp hu, Function.update_self]
        · simp only [isNamed_eq, testBit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hn'
          rcases hn' with hn' | rfl
          · obtain ⟨h1, h3⟩ := hI.named n (by rw [isNamed_eq]; exact hn') hc
            rw [Function.update_of_ne (hne _ h3), testBit_setBit, h3, Bool.true_or]
            exact ⟨h1, rfl⟩
          · rw [hcv, ← hv, Function.update_self, testBit_setBit, hcg]
            simp
        · rcases getF_cstAt hx with ⟨rfl, hk⟩ | hx
          · rw [hcg, testBit_setBit, Function.update_self]
            exact ⟨by simp, hkc x hk⟩
          · obtain ⟨h1, h3⟩ := hI.kc c x hx
            rw [testBit_setBit, h1, Bool.true_or, Function.update_of_ne (hne c h1)]
            exact ⟨rfl, h3⟩
        · obtain ⟨h1, h3, h4⟩ := hI.keys c k hk
          rw [Function.update_of_ne (hne c h3), testBit_setBit, h3, Bool.true_or]
          refine ⟨?_, rfl, fun c' hc' ↦ by rw [testBit_setBit, h4 c' hc', Bool.true_or]⟩
          have : k.2.map (Function.update Ψ (cg v) (σ v)) = k.2.map Ψ :=
            List.map_congr_left fun c' hc' ↦ Function.update_of_ne (hne c' (h4 c' hc')) _ _
          rw [this]; exact h1
        · obtain ⟨h1, h3, h4, h5⟩ := hI.pend p hp
          exact ⟨h1, h3, by rw [testBit_setBit, h4, Bool.true_or], h5⟩
        · exact ⟨by rw [testBit_setBit, hc, Bool.true_or], Function.update_of_ne (hne c hc) _ _⟩
      · -- pending
        rw [nameV_occ hnp h2' ho]
        refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, ?_⟩,
          Step.refl _ _⟩
        · rcases List.mem_append.mp hu with hu | hu
          · exact hI.occ u hu hc
          · rw [List.mem_singleton.mp hu, ← hcg]; exact ho
        · rcases List.mem_append.mp hu with hu | hu
          · refine hI.good u hu hc ?_
            simp only [isPend, List.any_cons, Bool.or_eq_false_iff] at hpe ⊢
            exact hpe.2
          · rw [List.mem_singleton.mp hu] at hpe
            simp [isPend] at hpe
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨by rw [hcv, hcg], h2', ho, (fun _ h ↦ by cases h), (fun _ h ↦ by cases h),
              (fun _ h ↦ by cases h)⟩
          · exact hI.pend p hp
  · -- named or pending already
    rw [nameV_skip hnp]
    refine ⟨Ψ, ⟨hvn, fun u hu hc ↦ ?_, fun u hu hc hpe ↦ ?_, hI.named, hI.kc, hI.keys, hI.pend⟩,
      Step.refl _ _⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.occ u hu hc
      · rw [List.mem_singleton.mp hu] at hc ⊢
        rcases Bool.or_eq_true_iff.mp hnp with hn | hp
        · rw [← hcv] at hc ⊢; exact (hI.named _ hn hc).2
        · obtain ⟨p, hp, hpv⟩ := isPend_iff.mp hp
          obtain ⟨h1, -, h3, -⟩ := hI.pend p hp
          rw [← hcv, ← hpv, h1]; exact h3
    · rcases List.mem_append.mp hu with hu | hu
      · exact hI.good u hu hc hpe
      · rw [List.mem_singleton.mp hu] at hc hpe ⊢
        rw [hpe, Bool.or_false] at hnp
        rw [← hcv] at hc ⊢
        rw [hv]; exact (hI.named _ hnp hc).1

end Inv

section Steps

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

theorem nameAllB_inv {kc : ℕ → Option (ℕ × ℕ × ℕ)} : ∀ (vs : List V) {st : SSt} {pre : List V}
    {Ψ : ℕ → E}, InvB S cg rd σ st pre Ψ → FitV loc cg vs → (∀ v ∈ vs, ∀ x, kc v.idx = some x → σ v = tw x) →
    ∃ Ψ', InvB S cg rd σ (nameAll loc sh kc st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameAll loc sh kc st vs) Ψ'
  | [], st, pre, Ψ, hI, _, _ => ⟨Ψ, by simpa [nameAll] using hI, by simpa [nameAll] using Step.refl st Ψ⟩
  | v :: vs, st, pre, Ψ, hI, hf, hk => by
    simp only [nameAll, SSt.seq_eq]
    obtain ⟨hv, hc⟩ := hf v List.mem_cons_self
    obtain ⟨Ψ1, hI1, hs1⟩ := nameVB_inv (sh := sh) hI hv hc (hk v List.mem_cons_self)
    obtain ⟨Ψ2, hI2, hs2⟩ := nameAllB_inv vs hI1 (hf.mono fun u hu ↦ List.mem_cons_of_mem _ hu)
      fun u hu ↦ hk u (List.mem_cons_of_mem _ hu)
    exact ⟨Ψ2, by simpa using hI2, hs1.trans hs2⟩

theorem constOfB_sound {a : Core.Atom} {v : ℕ} {x : ℕ × ℕ × ℕ} (ha : a.HoldsB S rd σ) (hvn : VnA a)
    (h : constOf a v = some x) : σ (V.n v) = tw x := by
  cases a with
  | const d c =>
    simp only [constOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [← hd, ← hvn d (by simp [Memory.atomUses]), tw_limbs]
    exact ha
  | assertNe x' i p =>
    simp only [constOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with hd
    obtain rfl := Option.some.inj h
    rw [← hd, ← hvn p (by simp [Memory.atomUses]), tw_one]
    exact ha.2
  | _ => simp [constOf] at h

theorem keysOfB_sound {a : Core.Atom} {v : ℕ} {k : ℕ × List ℕ} (ha : a.HoldsB S rd σ) (hvn : VnA a)
    (h : k ∈ keysOf a v) : KeyHoldsB S rd (σ (V.n v)) k.1 (k.2.map fun u ↦ σ (V.n u)) := by
  cases a with
  | add d x y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hx := hvn x (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    have ha' : σ d = σ x + σ y := ha
    rcases h with (h | h) | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he <;> simp only [KeyHoldsB, List.map_cons, List.map_nil]
    · rw [← hd, ← hx, ← hy]; exact ha'
    · rw [← hd, ← hx, ← hy, ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [← hd, ← hx, ← hy, ha', add_comm (σ x), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  | mul d x y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hx := hvn x (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with he <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    subst h; subst he
    simp only [KeyHoldsB, List.map_cons, List.map_nil]
    rw [← hd, ← hx, ← hy]; exact ha
  | blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    have e : ∀ u ∈ [m0, m1, m2, m3, c0, c1, o0, o1, md], σ (V.n u.idx) = σ u := fun u hu ↦ by
      rw [← hvn u (by simpa [Memory.atomUses] using hu)]
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he <;>
      simp only [KeyHoldsB, List.map_cons, List.map_nil, e m0 (by simp), e m1 (by simp),
        e m2 (by simp), e m3 (by simp), e c0 (by simp), e c1 (by simp), e md (by simp),
        e o0 (by simp), e o1 (by simp)]
    · exact ⟨_, ha⟩
    · exact ⟨_, ha⟩
  | load d p off =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hp := hvn p (by simp [Memory.atomUses])
    simp only [keysOf, Bool.cond_eq_ite, nbeq_iff] at h
    split_ifs at h with he <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    subst h; subst he
    simp only [KeyHoldsB, List.map_cons, List.map_nil]
    rw [← hd, ← hp]; exact ha
  | _ => simp [keysOf] at h

theorem eqsOfB_sound {a : Core.Atom} {v x : ℕ} (ha : a.HoldsB S rd σ) (hvn : VnA a) (h : x ∈ eqsOf a v) :
    σ (V.n v) = σ (V.n x) := by
  cases a with
  | copy d y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    have ha' : σ d = σ y := ha
    simp only [eqsOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he
    · rw [← hd, ← hy]; exact ha'
    · rw [← hd, ← hy]; exact ha'.symm
  | assertEq d y =>
    have hd := hvn d (by simp [Memory.atomUses])
    have hy := hvn y (by simp [Memory.atomUses])
    have ha' : σ d = σ y := eq_of_add_eq_zero ha
    simp only [eqsOf, Bool.cond_eq_ite, nbeq_iff, List.mem_append] at h
    rcases h with h | h <;> split_ifs at h with he <;> simp only [List.mem_singleton,
      List.not_mem_nil] at h <;> subst h <;> subst he
    · rw [← hd, ← hy]; exact ha'
    · rw [← hd, ← hy]; exact ha'.symm
  | _ => simp [eqsOf] at h

/-- **An atom's facts** about the pending values hold. -/
theorem addFactsB_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : InvB S cg rd σ st pre Ψ) (ha : a.HoldsB S rd σ) (hvn : VnA a) :
    InvB S cg rd σ ⟨st.occ, st.cst, st.keys, st.named, addFacts a st.pend⟩ pre Ψ := by
  refine ⟨hI.vn, hI.occ, fun u hu hc hp ↦ hI.good u hu hc (by rwa [isPend_addFacts] at hp),
    hI.named, hI.kc, hI.keys, fun p hp ↦ ?_⟩
  simp only [addFacts, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.pend q hq
  refine ⟨h1, h2, h3, fun x hx ↦ ?_, fun k hk ↦ ?_, fun x hx ↦ ?_⟩
  · simp only at hx
    cases hk : q.kc with
    | some y =>
      rw [hk] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx]; exact h4 y hk
    | none => rw [hk] at hx; exact constOfB_sound ha hvn hx
  · rcases List.mem_append.mp hk with hk | hk
    · exact keysOfB_sound ha hvn hk
    · exact h5 k hk
  · rcases List.mem_append.mp hx with hx | hx
    · exact eqsOfB_sound ha hvn hx
    · exact h6 x hx

/-- **A pending value shown** holds its cell's word. -/
theorem pfOkB_sound (hfun : SemFunctional S) (hA : LocAgree loc cg) {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : InvB S cg rd σ st pre Ψ) {p : PF} (hp : p ∈ st.pend) (h : pfOk loc st p = true) :
    σ (V.n p.v) = Ψ p.c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.pend p hp
  simp only [pfOk, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (h | ⟨k, hk, hok⟩) | ⟨x, hx, hok⟩
  · cases hkc : p.kc with
    | none => rw [hkc] at h; simp at h
    | some x =>
      rw [hkc] at h
      cases ho : getF st.cst p.c with
      | none => rw [ho] at h; simp at h
      | some y =>
        rw [ho] at h
        simp only [beq_iff_eq] at h
        subst h
        rw [h4 x hkc, (hI.kc p.c x ho).2]
  · simp only [keyOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hok
    obtain ⟨hin, k', hk', hkk⟩ := hok
    simp only [nbeq_iff, beq_iff_eq] at hkk
    obtain ⟨hop, hcs⟩ := hkk
    have hK := (hI.keys p.c k' hk').1
    rw [hop, hcs, keyHoldsB_keyCells, List.map_map] at hK
    have hmap : k.2.map (Ψ ∘ cellN loc) = k.2.map fun u ↦ σ (V.n u) := by
      refine List.map_congr_left fun u hu ↦ ?_
      have := hin u hu
      simp only [knownIn, Bool.and_eq_true, Nat.ble_eq] at this
      have hc : cellN loc u = cg (V.n u) := hA _ this.2
      rw [Function.comp_apply, hc]
      exact ((hI.named u this.1 (hc ▸ this.2)).1).symm
    rw [hmap] at hK
    exact (h5 k hk).unique hfun hK
  · simp only [Bool.and_eq_true, nbeq_iff] at hok
    obtain ⟨hn, hc⟩ := hok
    have hc' : cellN loc x = cg (V.n x) := hA _ (show 2 ≤ cellN loc x by rw [hc]; exact h2)
    rw [h6 x hx, ← hc, hc']
    exact (hI.named x hn (by rw [← hc', hc]; exact h2)).1

/-- **Showing pending values** keeps the invariant. -/
theorem dischargeB_inv (hfun : SemFunctional S) (hA : LocAgree loc cg) : ∀ (n : ℕ) {st : SSt} {pre : List V} {Ψ : ℕ → E},
    InvB S cg rd σ st pre Ψ → InvB S cg rd σ (discharge loc n st) pre Ψ ∧ (discharge loc n st).occ = st.occ
  | 0, st, pre, Ψ, hI => ⟨hI, rfl⟩
  | n + 1, st, pre, Ψ, hI => by
    simp only [discharge]
    rcases hs : splitPend loc st st.pend with ⟨ok, rest⟩
    obtain ⟨h1, h2, h3⟩ := splitPend_spec st st.pend hs
    cases ok with
    | nil => exact ⟨hI, rfl⟩
    | cons p ok =>
      simp only [natSeq_eq, SSt.seq_eq]
      have hokv : ∀ q ∈ p :: ok, σ (V.n q.v) = Ψ q.c := fun q hq ↦
        pfOkB_sound hfun hA hI (h1 q hq).1 (h1 q hq).2
      refine (dischargeB_inv hfun hA n ?_).imp id (fun h ↦ h)
      refine ⟨hI.vn, hI.occ, fun u hu hc hpe ↦ ?_, fun m hm hc ↦ ?_, hI.kc, hI.keys,
        fun q hq ↦ hI.pend q (h2 q hq)⟩
      · by_cases hold : isPend st u.idx = true
        · obtain ⟨q, hq, hqv⟩ := isPend_iff.mp hold
          rcases h3 q hq with hq' | hq'
          · obtain ⟨e1, -⟩ := hI.pend q hq
            rw [hI.vn u hu, ← hqv, hokv q hq', ← e1]
          · have : isPend ⟨st.occ, st.cst, st.keys, (p :: ok).foldl (fun s p ↦ setBit s p.v) st.named,
                rest⟩ u.idx = true := isPend_iff.mpr ⟨q, hq', hqv⟩
            rw [hpe] at this; cases this
        · exact hI.good u hu hc (by simpa using hold)
      · rw [isNamed_eq] at hm
        rcases testBit_foldl_pf _ _ _ hm with ⟨q, hq, rfl⟩ | hm
        · obtain ⟨e1, -, e3, -⟩ := hI.pend q (h1 q hq).1
          rw [e1]
          exact ⟨hokv q hq, e3⟩
        · exact hI.named m (by rw [isNamed_eq]; exact hm) hc

end Steps

section Record

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- An entry of `cellKeys`: an output and inputs of the atom, the key holding of their words. -/
theorem cellKeysB_sound {a : Core.Atom} (ha : a.HoldsB S rd σ) {c op : ℕ} {ins : List ℕ}
    (h : (c, op, ins) ∈ cellKeys loc a) :
    ∃ out ∈ Memory.atomUses a, ∃ insV : List V, (∀ u ∈ insV, u ∈ Memory.atomUses a) ∧
      c = loc.cell out ∧ ins = keyCells op (insV.map loc.cell) ∧
      KeyHoldsB S rd (σ out) op (insV.map σ) := by
  cases a with
  | add d x y =>
    have ha' : σ d = σ x + σ y := ha
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨d, by simp [Memory.atomUses], [x, y], by simp [Memory.atomUses], rfl, rfl, ha'⟩
    · refine ⟨x, by simp [Memory.atomUses], [d, y], by simp [Memory.atomUses], rfl, rfl, ?_⟩
      show σ x = σ d + σ y
      rw [ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · refine ⟨y, by simp [Memory.atomUses], [d, x], by simp [Memory.atomUses], rfl, rfl, ?_⟩
      show σ y = σ d + σ x
      rw [ha', add_comm (σ x), add_assoc, CharTwo.add_self_eq_zero, add_zero]
  | mul d x y =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, by simp [Memory.atomUses], [x, y], by simp [Memory.atomUses], rfl, rfl, ha⟩
  | blake2s m0 m1 m2 m3 c0 c1 o0 o1 md =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨o0, by simp [Memory.atomUses], [m0, m1, m2, m3, c0, c1, md], by simp [Memory.atomUses],
        rfl, rfl, ⟨σ o1, ha⟩⟩
    · exact ⟨o1, by simp [Memory.atomUses], [m0, m1, m2, m3, c0, c1, md], by simp [Memory.atomUses],
        rfl, rfl, ⟨σ o0, ha⟩⟩
  | load d p off =>
    simp only [cellKeys, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, by simp [Memory.atomUses], [p], by simp [Memory.atomUses], rfl, rfl, ha⟩
  | _ => simp [cellKeys] at h

/-- **Recording an atom's cell facts** keeps the invariant. -/
theorem recordB_inv {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : InvB S cg rd σ st pre Ψ) (ha : a.HoldsB S rd σ) (hvn : VnA a)
    (hfit : FitV loc cg (Memory.atomUses a)) :
    InvB S cg rd σ (record loc sh a st) pre Ψ ∧ Step st Ψ (record loc sh a st) Ψ := by
  unfold record
  cases hall : (Memory.atomUses a).all fun v ↦ isNamed st v.idx
  · rw [Bool.cond_false]; exact ⟨hI, Step.refl _ _⟩
  rw [Bool.cond_true]
  simp only [List.all_eq_true] at hall
  -- every value of the atom holds its cell's word, its cell occupied
  have hval : ∀ u ∈ Memory.atomUses a, 2 ≤ loc.cell u →
      σ u = Ψ (loc.cell u) ∧ st.occ.testBit (loc.cell u) := fun u hu hc ↦ by
    obtain ⟨hv, hcg⟩ := hfit u hu
    have hcv : cg (V.n u.idx) = loc.cell u := by rw [← hv, hcg]
    have := hI.named u.idx (hall u hu) (by rw [hcv]; exact hc)
    rw [hcv, ← hv] at this
    exact this
  refine ⟨⟨hI.vn, hI.occ, hI.good, hI.named, fun c x hx ↦ ?_, fun c k hk ↦ ?_, hI.pend⟩,
    Step.refl _ _⟩
  · rcases getF_recCst hx with hx | ⟨-, hc2, ⟨d, y, rfl, rfl, rfl⟩ | ⟨u, i, p, rfl, rfl, rfl⟩⟩
    · exact hI.kc c x hx
    · have hdv := hval d (by simp [Memory.atomUses]) hc2
      refine ⟨hdv.2, ?_⟩
      rw [← hdv.1, tw_limbs]; exact ha
    · have hpv := hval p (by simp [Memory.atomUses]) hc2
      refine ⟨hpv.2, ?_⟩
      rw [← hpv.1, tw_one]; exact ha.2
  · rcases mem_foldl_keys _ _ c k hk with hk | ⟨hk, hc2, hins⟩
    · exact hI.keys c k hk
    · obtain ⟨out, hout, insV, hinsV, rfl, hins', hK⟩ := cellKeysB_sound ha hk
      have hcell : ∀ c' ∈ k.2, ∃ u ∈ insV, c' = loc.cell u := fun c' hc' ↦ by
        rw [hins', mem_keyCells] at hc'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc'
        exact ⟨u, hu, rfl⟩
      have hmap : insV.map σ = (insV.map loc.cell).map Ψ := by
        rw [List.map_map]
        refine List.map_congr_left fun u hu ↦ ?_
        exact (hval u (hinsV u hu) (hins _ (by rw [hins', mem_keyCells]; exact List.mem_map_of_mem hu))).1
      rw [hmap, (hval out hout hc2).1, ← keyHoldsB_keyCells, ← hins'] at hK
      refine ⟨hK, (hval out hout hc2).2, fun c' hc' ↦ ?_⟩
      obtain ⟨u, hu, rfl⟩ := hcell c' hc'
      exact (hval u (hinsV u hu) (hins _ hc')).2

end Record

section Atoms

variable {loc : Loc} {sh : ℕ} {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- **An atom on the path** keeps the invariant, its values named. -/
theorem stepAtomB_inv (hfun : SemFunctional S) (hA : LocAgree loc cg) {a : Core.Atom} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : InvB S cg rd σ st pre Ψ) (ha : a.HoldsB S rd σ) (hfit : FitV loc cg (Memory.atomUses a)) :
    ∃ Ψ', InvB S cg rd σ (stepAtom loc sh st a) (pre ++ Memory.atomUses a) Ψ' ∧
      Step st Ψ (stepAtom loc sh st a) Ψ' := by
  have hvn : VnA a := fun u hu ↦ (hfit u hu).1
  unfold stepAtom
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAllB_inv (sh := sh) (kc := constOf a) (Memory.atomUses a) hI hfit
    fun v hv x hx ↦ by rw [hvn v hv]; exact constOfB_sound ha hvn hx
  have hI2 := addFactsB_inv hI1 ha hvn
  obtain ⟨hI3, ho3⟩ := dischargeB_inv hfun hA (_ + 1) hI2
  obtain ⟨hI4, hs4⟩ := recordB_inv (sh := sh) hI3 ha hvn hfit
  refine ⟨Ψ1, hI4, hs1.trans ((Step.of_occ fun c h ↦ ?_).trans hs4)⟩
  rw [ho3]; exact h

/-- **Other values named** keep the invariant. -/
theorem nameStepB_inv (hfun : SemFunctional S) (hA : LocAgree loc cg) {vs : List V} {st : SSt} {pre : List V} {Ψ : ℕ → E}
    (hI : InvB S cg rd σ st pre Ψ) (hfit : FitV loc cg vs) :
    ∃ Ψ', InvB S cg rd σ (nameStep loc sh st vs) (pre ++ vs) Ψ' ∧ Step st Ψ (nameStep loc sh st vs) Ψ' := by
  unfold nameStep
  simp only [SSt.seq_eq]
  obtain ⟨Ψ1, hI1, hs1⟩ := nameAllB_inv (sh := sh) (kc := fun _ ↦ none) vs hI hfit
    fun v hv x hx ↦ by cases hx
  obtain ⟨hI2, ho2⟩ := dischargeB_inv hfun hA (_ + 1) hI1
  refine ⟨Ψ1, hI2, hs1.trans (Step.of_occ fun c h ↦ ?_)⟩
  rw [ho2]; exact h

end Atoms

/-! ## Joins -/

section Join

variable {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- **After a join**, for the branch taken: the facts from before the branch, with the branch's
cell words. -/
theorem joinStB_inv {st1 b : SSt} {bs : List SSt} {pre1 preb : List V} {Ψ1 Ψb : ℕ → E}
    (hI1 : InvB S cg rd σ st1 pre1 Ψ1) (hIb : InvB S cg rd σ b preb Ψb) (hs : Step st1 Ψ1 b Ψb)
    (hb : b ∈ bs) (hp : b.pend = []) :
    InvB S cg rd σ (joinSt st1 bs) preb Ψb ∧ Step st1 Ψ1 (joinSt st1 bs) Ψb := by
  have hsome : ∀ c, b.occ.testBit c = true → (joinSt st1 bs).occ.testBit c = true := fun c h ↦
    (testBit_foldl_lor bs st1.occ c).mpr (Or.inr ⟨b, hb, h⟩)
  have hsome1 : ∀ c, st1.occ.testBit c = true → (joinSt st1 bs).occ.testBit c = true := fun c h ↦
    (testBit_foldl_lor bs st1.occ c).mpr (Or.inl h)
  refine ⟨⟨hIb.vn, fun u hu hc ↦ hsome _ (hIb.occ u hu hc), fun u hu hc _ ↦ ?_, fun n hn hc ↦ ?_,
    fun c x hx ↦ ?_, fun c k hk ↦ ?_, fun p hp' ↦ by simp [joinSt] at hp'⟩,
    fun c hc ↦ ⟨hsome1 c hc, (hs c hc).2⟩⟩
  · exact hIb.good u hu hc (by simp [isPend, hp])
  · have hnb : isNamed b n = true := by
      rw [isNamed_eq] at hn ⊢
      simp only [joinSt] at hn
      cases bs with
      | nil => cases hb
      | cons b0 bs' =>
        obtain ⟨h1, h2⟩ := testBit_foldl_land bs' b0.named n hn
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact h1
        · exact h2 b hb'
    exact ⟨(hIb.named n hnb hc).1, hsome _ (hIb.named n hnb hc).2⟩
  · obtain ⟨h1, h2⟩ := hI1.kc c x hx
    exact ⟨hsome1 c h1, by rw [(hs c h1).2]; exact h2⟩
  · obtain ⟨h1, h2, h3⟩ := hI1.keys c k hk
    refine ⟨?_, hsome1 c h2, fun c' hc' ↦ hsome1 c' (h3 c' hc')⟩
    rw [(hs c h2).2]
    have : k.2.map Ψb = k.2.map Ψ1 := List.map_congr_left fun c' hc' ↦ (hs c' (h3 c' hc')).2
    rw [this]; exact h1

end Join

/-! ## Paths -/

section Walk

open LeanVM.Guest.Memory

variable {loc : Loc} {sh : ℕ} {tt : Exec.Trie ℕ} {P : Plumb} {cg : V → ℕ} {rd : Reader} {σ : Val}

variable (S) in
/-- What a walk gives of an outcome: at a fall-through, the end state with the path's values named;
at a return, a state with every value named and nothing pending (or the end state itself). -/
def ConcB (cg : V → ℕ) (rd : Reader) (σ : Val) (st : SSt) (Ψ : ℕ → E) (pre : List V)
    (st' : SSt) : Out → Prop
  | .fall es => ∃ pre' Ψ', InvB S cg rd σ st' pre' Ψ' ∧ Step st Ψ st' Ψ' ∧ (∀ v ∈ pre, v ∈ pre') ∧
      ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre'
  | .ret es vs => ∃ st'' pre' Ψ', InvB S cg rd σ st'' pre' Ψ' ∧ Step st Ψ st'' Ψ' ∧
      (st''.pend = [] ∨ st'' = st') ∧
      (∀ v ∈ pre, v ∈ pre') ∧ (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ pre') ∧ ∀ v ∈ vs, v ∈ pre'
  | .stuck => True

/-- Names `vs` after `pre`: a fall-through naming `vs`. -/
theorem concB_names {st st' : SSt} {Ψ Ψ' : ℕ → E} {pre vs : List V} {es : List Ev}
    (hI : InvB S cg rd σ st' (pre ++ vs) Ψ') (hs : Step st Ψ st' Ψ')
    (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) : ConcB S cg rd σ st Ψ pre st' (.fall es) :=
  ⟨pre ++ vs, Ψ', hI, hs, fun _ hv ↦ List.mem_append_left _ hv,
    fun e he v hv ↦ List.mem_append_right _ (hu e he v hv)⟩

/-- A statement's outcome followed by the rest of its block's. -/
theorem concB_seq {st st1 st' : SSt} {Ψ : ℕ → E} {pre : List V} {o1 o2 : Out}
    (h1 : ConcB S cg rd σ st Ψ pre st1 o1)
    (h2 : ∀ es1, o1 = .fall es1 → ∀ pre1 Ψ1, InvB S cg rd σ st1 pre1 Ψ1 → Step st Ψ st1 Ψ1 →
      (∀ v ∈ pre, v ∈ pre1) → ConcB S cg rd σ st1 Ψ1 pre1 st' o2)
    (hr : ∀ es vs, o1 = .ret es vs → st1.pend = []) : ConcB S cg rd σ st Ψ pre st' (o1.seq o2) := by
  cases o1 with
  | fall es1 =>
    obtain ⟨pre1, Ψ1, hI1, hs1, hp1, hu1⟩ := h1
    have h2' := h2 es1 rfl pre1 Ψ1 hI1 hs1 hp1
    cases o2 with
    | fall es2 =>
      obtain ⟨pre2, Ψ2, hI2, hs2, hp2, hu2⟩ := h2'
      exact ⟨pre2, Ψ2, hI2, hs1.trans hs2, fun v hv ↦ hp2 v (hp1 v hv), fun e he v hv ↦
        (List.mem_append.mp he).elim (fun he ↦ hp2 v (hu1 e he v hv)) (fun he ↦ hu2 e he v hv)⟩
    | ret es2 vs =>
      obtain ⟨st'', pre2, Ψ2, hI2, hs2, hp, hp2, hu2, hv2⟩ := h2'
      exact ⟨st'', pre2, Ψ2, hI2, hs1.trans hs2, hp, fun v hv ↦ hp2 v (hp1 v hv), fun e he v hv ↦
        (List.mem_append.mp he).elim (fun he ↦ hp2 v (hu1 e he v hv)) (fun he ↦ hu2 e he v hv), hv2⟩
    | stuck => trivial
  | ret es vs =>
    obtain ⟨st'', pre', Ψ', hI', hs', hp, h3⟩ := h1
    refine ⟨st'', pre', Ψ', hI', hs', Or.inl ?_, h3⟩
    rcases hp with hp | rfl
    · exact hp
    · exact hr es vs rfl
  | stuck => trivial

/-- A conclusion for the values `vs` named first, before the events `es`. -/
theorem concB_pre {st st' : SSt} {Ψ : ℕ → E} {pre vs : List V} {es : List Ev} {o : Out}
    (h : ConcB S cg rd σ st Ψ (pre ++ vs) st' o) (hu : ∀ e ∈ es, ∀ v ∈ e.uses, v ∈ vs) :
    ConcB S cg rd σ st Ψ pre st' (o.pre es) := by
  cases o with
  | fall es' =>
    obtain ⟨pre', Ψ', hI, hs, hp, hu'⟩ := h
    refine ⟨pre', Ψ', hI, hs, fun v hv ↦ hp v (List.mem_append_left _ hv), fun e he v hv ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hp v (List.mem_append_right _ (hu e he v hv))
    · exact hu' e he v hv
  | ret es' vs' =>
    obtain ⟨st'', pre', Ψ', hI, hs, hpe, hp, hu', hv⟩ := h
    refine ⟨st'', pre', Ψ', hI, hs, hpe, fun v hv ↦ hp v (List.mem_append_left _ hv), fun e he v hv ↦ ?_,
      hv⟩
    rcases List.mem_append.mp he with he | he
    · exact hp v (List.mem_append_right _ (hu e he v hv))
    · exact hu' e he v hv
  | stuck => trivial

/-- A conclusion for fewer values named before. -/
theorem concB_shrink {st st' : SSt} {Ψ : ℕ → E} {pre vs : List V} {o : Out}
    (h : ConcB S cg rd σ st Ψ (pre ++ vs) st' o) : ConcB S cg rd σ st Ψ pre st' o := by
  cases o with
  | fall es =>
    obtain ⟨pre', Ψ', hI, hs, hp, hu⟩ := h
    exact ⟨pre', Ψ', hI, hs, fun v hv ↦ hp v (List.mem_append_left _ hv), hu⟩
  | ret es vs' =>
    obtain ⟨st'', pre', Ψ', hI, hs, hpe, hp, hu, hv⟩ := h
    exact ⟨st'', pre', Ψ', hI, hs, hpe, fun v hv ↦ hp v (List.mem_append_left _ hv), hu, hv⟩
  | stuck => trivial

/-- **A branch's conclusion** after the join, from before the branch. -/
theorem concB_join {st st1 b : SSt} {bs : List SSt} {Ψ Ψ1 : ℕ → E} {pre1 : List V} {o : Out}
    (hI1 : InvB S cg rd σ st1 pre1 Ψ1) (hs1 : Step st Ψ st1 Ψ1) (hb : b ∈ bs)
    (hC : ConcB S cg rd σ st1 Ψ1 pre1 b o) (hp : b.pend = []) :
    ConcB S cg rd σ st Ψ pre1 (joinSt st1 bs) o := by
  cases o with
  | fall es =>
    obtain ⟨pre', Ψ', hI', hs', hp1, hu⟩ := hC
    obtain ⟨hIj, hsj⟩ := joinStB_inv hI1 hI' hs' hb hp
    exact ⟨pre', Ψ', hIj, hs1.trans hsj, hp1, hu⟩
  | ret es vs =>
    obtain ⟨st'', pre', Ψ', hI', hs', hp2, hp1, hu, hvs⟩ := hC
    refine ⟨st'', pre', Ψ', hI', hs1.trans hs', Or.inl ?_, hp1, hu, hvs⟩
    rcases hp2 with hp2 | rfl
    · exact hp2
    · exact hp
  | stuck => trivial

mutual
/-- **One statement**: what the walk gives of its outcome on a path. -/
theorem swSB_sound (hfun : SemFunctional S) (hA : LocAgree loc cg) : ∀ (s : Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swS loc sh tt P st s = some st' → InvB S cg rd σ st pre Ψ → FitV loc cg (Stmt.uses s) →
    (∀ e ∈ (walk1 σ s).evs, e.HoldsB S rd σ) → ConcB S cg rd σ st Ψ pre st' (walk1 σ s)
  | .atom a, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      have ha : a.HoldsB S rd σ := he (.atom a) (by simp [walk1, Out.evs])
      obtain ⟨Ψ', hI', hs⟩ := stepAtomB_inv hfun hA hI ha hv
      refine concB_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      exact hv'
  | .ite c z n, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases hz : swL loc sh tt P (nameStep loc sh st [c]) z <;> cases hn : swL loc sh tt P (nameStep loc sh st [c]) n <;>
        rw [hz, hn] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i sz sn
      have hc := hv c List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStepB_inv hfun hA hI (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hc)
      have hu : ∀ e ∈ [Ev.inK c], ∀ v ∈ e.uses, v ∈ [c] := fun e he v hv ↦ by
        simp only [List.mem_singleton] at he; subst he; exact hv
      simp only [walk1] at he ⊢
      by_cases hc0 : σ c = 0
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine concB_pre (concB_join hI1 hs1 List.mem_cons_self ?_ (swL_pend z hz)) hu
        exact swLB_sound hfun hA z hz hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
      · simp only [hc0, ↓reduceIte] at he ⊢
        refine concB_pre (concB_join hI1 hs1 (by simp) ?_ (swL_pend n hn)) hu
        exact swLB_sound hfun hA n hn hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv])
          fun e he' ↦ he e (evs_pre he')
  | .match_ x arms, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swS, SSt.seq_eq, Bool.cond_eq_ite] at h
      split_ifs at h with hp
      cases ha : swArms loc sh tt P (nameStep loc sh st [x]) arms <;> rw [ha] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i bs
      have hx := hv x List.mem_cons_self
      obtain ⟨Ψ1, hI1, hs1⟩ := nameStepB_inv hfun hA hI (fun u hu ↦ by rw [List.mem_singleton.mp hu]; exact hx)
      simp only [walk1] at he ⊢
      rcases swArmsB_sound hfun hA x arms 0 ha hI1 (hv.mono fun v hv ↦ by simp [Stmt.uses, hv]) he with
        hst | ⟨b, hb, hC, hbp⟩
      · rw [hst]; trivial
      · exact concB_shrink (concB_join hI1 hs1 hb hC hbp)
  | .call f args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStepB_inv hfun hA hI hv
      refine concB_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_singleton] at he'
      subst he'
      simpa [Ev.uses, Stmt.uses] using hv'
  | .callIf c f args, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStepB_inv hfun hA hI hv
      refine concB_names hI' hs fun e he' v hv' ↦ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl
      · simp only [Ev.uses, List.mem_singleton] at hv'
        simp [Stmt.uses, hv']
      · split_ifs at hv' <;> simp_all [Ev.uses, Stmt.uses]
  | .dispatch x fs args rets, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStepB_inv hfun hA hI hv
      simp only [walk1]
      rcases pick_cases_sh (σ := σ) (x := x) (args := args) (rets := rets) fs 0 with hp | ⟨g, hp⟩
      · rw [hp]; trivial
      · rw [hp]
        refine concB_names hI' hs fun e he' v hv' ↦ ?_
        simp only [List.mem_singleton] at he'
        subst he'
        simp only [Ev.uses] at hv' ⊢
        exact List.mem_cons_of_mem _ hv'
  | .ret vs, st, st', pre, Ψ, h, hI, hv, _ => by
      simp only [swS, Option.some.injEq] at h
      subst h
      obtain ⟨Ψ', hI', hs⟩ := nameStepB_inv hfun hA hI hv
      simp only [walk1]
      exact ⟨nameStep loc sh st (stmtNames (.ret vs)), pre ++ stmtNames (.ret vs), Ψ', hI', hs, Or.inr rfl,
        fun _ hv ↦ List.mem_append_left _ hv, fun e he ↦ absurd he List.not_mem_nil,
        fun v hv ↦ List.mem_append_right _ hv⟩

/-- **A block**: what the walk gives of its outcome on a path. -/
theorem swLB_sound (hfun : SemFunctional S) (hA : LocAgree loc cg) : ∀ (ss : List Stmt) {st st' : SSt} {pre : List V} {Ψ : ℕ → E},
    swL loc sh tt P st ss = some st' → InvB S cg rd σ st pre Ψ → FitV loc cg (Stmt.usesList ss) →
    (∀ e ∈ (walk σ ss).evs, e.HoldsB S rd σ) → ConcB S cg rd σ st Ψ pre st' (walk σ ss)
  | [], st, st', pre, Ψ, h, hI, _, _ => by
      simp only [swL, Bool.cond_eq_ite] at h
      split_ifs at h
      cases h
      exact ⟨pre, Ψ, hI, Step.refl _ _, fun _ hv ↦ hv, fun e he ↦ by simp at he⟩
  | s :: ss, st, st', pre, Ψ, h, hI, hv, he => by
      simp only [swL] at h
      cases hs : swS loc sh tt P st s with
      | none => rw [hs] at h; cases h
      | some st1 =>
        rw [hs] at h
        simp only [SSt.seq_eq, Bool.cond_eq_ite] at h
        split_ifs at h with hm
        rw [walk] at he ⊢
        by_cases hst : (walk1 σ s).seq (walk σ ss) = .stuck
        · rw [hst]; trivial
        obtain ⟨he1, he2⟩ := seq_evs hst
        have hvs : FitV loc cg (Stmt.uses s) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        have hvss : FitV loc cg (Stmt.usesList ss) := hv.mono fun v hv ↦ by simp [Stmt.usesList, hv]
        refine concB_seq (swSB_sound hfun hA s hs hI hvs fun e h ↦ he e (he1 e h))
          (fun es1 h1 pre1 Ψ1 hI1 _ _ ↦ swLB_sound hfun hA ss h hI1 hvss fun e h ↦ he e (he2 es1 h1 e h))
          fun es vs hr ↦ ?_
        have := mayRet_of_walk1 hr
        simp only [this, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
        simpa using hm

/-- **The arms of a `match`**: the arm taken. -/
theorem swArmsB_sound (hfun : SemFunctional S) (hA : LocAgree loc cg) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {st : SSt} {bs : List SSt}
    {pre : List V} {Ψ : ℕ → E}, swArms loc sh tt P st arms = some bs → InvB S cg rd σ st pre Ψ →
    FitV loc cg (Stmt.usesArms arms) → (∀ e ∈ (walkArms σ x j arms).evs, e.HoldsB S rd σ) →
    walkArms σ x j arms = .stuck ∨
      ∃ b ∈ bs, ConcB S cg rd σ st Ψ pre b (walkArms σ x j arms) ∧ b.pend = []
  | [], j, _, _, _, _, _, _, _, _ => Or.inl (by simp [walkArms])
  | a :: as, j, st, bs, pre, Ψ, h, hI, hv, he => by
      simp only [swArms] at h
      cases ha : swL loc sh tt P st a <;> cases has : swArms loc sh tt P st as <;> rw [ha, has] at h <;>
        simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i b bs'
      unfold walkArms at he ⊢
      split_ifs at he ⊢
      · exact Or.inr ⟨b, List.mem_cons_self, swLB_sound hfun hA a ha hI (hv.mono fun v hv ↦ by
          simp [Stmt.usesArms, hv]) he, swL_pend a ha⟩
      · rcases swArmsB_sound hfun hA x as (j + 1) has hI (hv.mono fun v hv ↦ by simp [Stmt.usesArms, hv]) he with
          h | ⟨b', hb', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨b', List.mem_cons_of_mem _ hb', h⟩
end

end Walk

/-! ## Snapshots -/

section Snaps

variable {cg : V → ℕ} {rd : Reader} {σ : Val}

/-- **A window's end state refines the next one's snapshot**: the snapshot's state holds for the
same words, every occupied cell staying occupied. -/
theorem refinesB_inv {m : SSt} {pre : List V} {Ψ : ℕ → E} {s : Snap} (hI : InvB S cg rd σ m pre Ψ)
    (hr : refines m s = true) : InvB S cg rd σ s.st [] Ψ ∧ Step m Ψ s.st Ψ := by
  simp only [refines, Bool.and_eq_true, List.all_eq_true, nbeq_iff, beq_iff_eq, List.any_eq_true] at hr
  obtain ⟨⟨⟨hocc, hnm⟩, hcst⟩, hky⟩ := hr
  have hsub : ∀ c, m.occ.testBit c = true → s.occ.testBit c = true := fun c h ↦ by
    have := congrArg (fun x ↦ x.testBit c) hocc
    simp only [testBit_land', h, Bool.true_and] at this
    exact this
  refine ⟨⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ h ↦ absurd h List.not_mem_nil,
    fun _ h ↦ absurd h List.not_mem_nil, fun n hn hc ↦ ?_, fun c x hx ↦ ?_, fun c k hk ↦ ?_,
    fun p hp ↦ by simp [Snap.st] at hp⟩, fun c hc ↦ ⟨hsub c hc, rfl⟩⟩
  · rw [isNamed_eq] at hn
    simp only [Snap.st] at hn
    have hn' := hnm n ((testBit_bitsOf _ _).mp hn)
    rw [bitN_eq] at hn'
    obtain ⟨h1, h2⟩ := hI.named n (by rw [isNamed_eq]; exact hn') hc
    exact ⟨h1, hsub _ h2⟩
  · simp only [Snap.st] at hx
    rcases getF_foldl_cst _ _ hx with hx | hx
    · have := hcst _ hx
      obtain ⟨h1, h2⟩ := hI.kc c x this
      exact ⟨hsub c h1, h2⟩
    · simp [getF_eq] at hx
  · simp only [Snap.st] at hk
    rcases mem_foldl_snapKeys _ _ hk with hk | hk
    · obtain ⟨k', hk', he⟩ := hky _ hk
      subst he
      obtain ⟨h1, h2, h3⟩ := hI.keys c k' hk'
      exact ⟨h1, hsub c h2, fun c' hc' ↦ hsub c' (h3 c' hc')⟩
    · simp [getF_eq] at hk

end Snaps

/-! ## The windows chained -/

section Chain

open LeanVM.Guest.Memory

variable {j : ℕ} {rd : Reader} {σ : Val}

/-- **The windows chained**: from window `i`'s start, on a path from there that returns, every value
named before or on it holds its cell's word, and the cells occupied at the start keep theirs. -/
theorem chainB_sound (hfun : SemFunctional S) (hS : ShareOk j)
    (hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c → cellJ j v = c) :
    ∀ k i, i + k = (snapsOf j).length → ∀ (pre : List V) (Ψ : ℕ → E),
      InvB S (cellJ j) rd σ (startSt j i) pre Ψ → ∀ es vs, walk σ (fromW (coreOf j).body (snapsOf j) i) = .ret es vs →
      (∀ e ∈ es, e.HoldsB S rd σ) → ∃ Ψf : ℕ → E,
        (∀ v ∈ pre ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v → σ v = Ψf (cellJ j v)) ∧
        ∀ c, (startSt j i).occ.testBit c = true → Ψf c = Ψ c := by
  intro k
  induction k with
  | zero =>
    intro i hi pre Ψ hI es vs hw he
    have hiN : i ≤ (snapsOf j).length := by omega
    obtain ⟨-, hval, m, hsw, -⟩ := shareWin_spec (hS.2 i hiN)
    rw [fromW_last (by omega)] at hw
    have hfit : FitV (locW (certOf j) (winW (snapsOf j) i)) (cellJ j) (Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i)) :=
      fitV_of (hA i hiN) fun v hv ↦ hval v (List.mem_append_left _ hv)
    have hC := swLB_sound hfun (locAgree_strong (hA i hiN)) _ hsw hI hfit (by rw [evs_ret hw]; exact he)
    rw [hw] at hC
    obtain ⟨st'', pre', Ψ', hI', hs', hpe, hpre, hus, hvs⟩ := hC
    have hpe' : st''.pend = [] := by
      rcases hpe with hpe | rfl
      · exact hpe
      · exact swL_pend _ hsw
    refine ⟨Ψ', fun v hv hc ↦ ?_, fun c hc ↦ (hs' c hc).2⟩
    have hv' : v ∈ pre' := by
      simp only [List.mem_append, List.mem_flatMap] at hv
      rcases hv with (hv | ⟨e, he', hv⟩) | hv
      · exact hpre v hv
      · exact hus e he' v hv
      · exact hvs v hv
    exact hI'.good v hv' hc (by simp [isPend, hpe'])
  | succ k ih =>
    intro i hi pre Ψ hI es vs hw he
    have hiN : i < (snapsOf j).length := by omega
    obtain ⟨-, hval, m, hsw, href⟩ := shareWin_spec (hS.2 i hiN.le)
    obtain ⟨-, -, hmono, -, -⟩ := shareStatic_spec hS.1
    rw [fromW_split hiN (snapsOk_spec hmono hiN).1, walk_append_sh] at hw
    have hfit : FitV (locW (certOf j) (winW (snapsOf j) i)) (cellJ j) (Stmt.usesList (stmtsW (coreOf j).body (snapsOf j) i)) :=
      fitV_of (hA i hiN.le) fun v hv ↦ hval v (List.mem_append_left _ hv)
    have hAi := locAgree_strong (hA i hiN.le)
    cases hW : walk σ (stmtsW (coreOf j).body (snapsOf j) i) with
    | stuck => rw [hW] at hw; simp [Out.seq] at hw
    | ret es' vs' =>
      rw [hW] at hw
      simp only [Out.seq, Out.ret.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hC := swLB_sound hfun hAi _ hsw hI hfit (by rw [evs_ret hW]; exact he)
      rw [hW] at hC
      obtain ⟨st'', pre', Ψ', hI', hs', hpe, hpre, hus, hvs⟩ := hC
      have hpe' : st''.pend = [] := by
        rcases hpe with hpe | rfl
        · exact hpe
        · exact swL_pend _ hsw
      refine ⟨Ψ', fun v hv hc ↦ ?_, fun c hc ↦ (hs' c hc).2⟩
      have hv' : v ∈ pre' := by
        simp only [List.mem_append, List.mem_flatMap] at hv
        rcases hv with (hv | ⟨e, he', hv⟩) | hv
        · exact hpre v hv
        · exact hus e he' v hv
        · exact hvs v hv
      exact hI'.good v hv' hc (by simp [isPend, hpe'])
    | fall es1 =>
      rw [hW] at hw
      simp only [Out.seq] at hw
      cases hD : walk σ (fromW (coreOf j).body (snapsOf j) (i + 1)) with
      | fall _ => rw [hD] at hw; simp [Out.pre] at hw
      | stuck => rw [hD] at hw; simp [Out.pre] at hw
      | ret es2 vs2 =>
        rw [hD] at hw
        simp only [Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hC := swLB_sound hfun hAi _ hsw hI hfit (by
          rw [hW]; exact fun e he' ↦ he e (List.mem_append_left _ he'))
        rw [hW] at hC
        obtain ⟨pre', Ψ', hI', hs', hpre, hus⟩ := hC
        have hpe : m.pend = [] := swL_pend _ hsw
        obtain ⟨hIs, hss⟩ := refinesB_inv hI' (href hiN)
        have hst : startSt j (i + 1) = (snapAt (snapsOf j) (i + 1)).st := rfl
        obtain ⟨Ψf, hf1, hf2⟩ := ih (i + 1) (by omega) [] Ψ' (hst ▸ hIs) es2 vs2 hD
          fun e he' ↦ he e (List.mem_append_right _ he')
        have hkeep : ∀ c, m.occ.testBit c = true → Ψf c = Ψ' c := fun c hc ↦
          hf2 c (by rw [hst]; exact (hss c hc).1)
        refine ⟨Ψf, fun v hv hc ↦ ?_, fun c hc ↦ ?_⟩
        · have old : v ∈ pre' → σ v = Ψf (cellJ j v) := fun hv' ↦ by
            rw [hkeep _ (hI'.occ v hv' hc)]
            exact hI'.good v hv' hc (by simp [isPend, hpe])
          rcases List.mem_append.mp hv with hv | hv
          · rcases List.mem_append.mp hv with hv | hv
            · exact old (hpre v hv)
            · rw [List.flatMap_append] at hv
              rcases List.mem_append.mp hv with hv | hv
              · obtain ⟨e, he', hv⟩ := List.mem_flatMap.mp hv
                exact old (hus e he' v hv)
              · exact hf1 v (List.mem_append_left _ (by simpa using hv)) hc
          · exact hf1 v (List.mem_append_right _ hv) hc
        · rw [hkeep c (hs' c hc).1, (hs' c hc).2]

end Chain

/-! ## The check of a function -/

section FnPath

open LeanVM.Guest.Memory

variable {j : ℕ} {rd : Reader} {σ : Val}

theorem initStB_inv (P : Plumb) (cg : V → ℕ) : InvB S cg rd σ (initSt P) [] (initW P) where
  vn _ h := absurd h List.not_mem_nil
  occ _ h := absurd h List.not_mem_nil
  good _ h := absurd h List.not_mem_nil
  named n hn _ := by simp [isNamed_eq, initSt] at hn
  kc c x hx := by
    refine ⟨?_, by simp only [initW, hx]⟩
    rcases getF_initCst _ _ hx with ⟨q, hq, rfl⟩ | hx
    · simp only [initSt]
      exact (testBit_bitsOf _ _).mpr (List.mem_map_of_mem hq)
    · simp [getF_eq] at hx
  keys c k hk := by simp [initSt, getF_eq] at hk
  pend p hp := by simp [initSt] at hp

/-- **The sharing check's conclusion on a path** of function `j` that returns: one word per cell
for every value the path names, a fixed cell's constant. -/
theorem shareOkB_path (hfun : SemFunctional S) {G : Glob} {f : CompiledFn} {main : Bool} (hS : ShareOk j)
    (hchk : ∀ i ≤ (certOf j).cuts.length, checkWin G f (coreOf j) (certOf j) main i = true)
    {es : List Ev} {vs : List V} (hw : walk σ (coreOf j).body = .ret es vs) (he : ∀ e ∈ es, e.HoldsB S rd σ) :
    ∃ Ψ : ℕ → E, (∀ v ∈ (coreOf j).params ++ es.flatMap Ev.uses ++ vs, 2 ≤ cellJ j v →
      σ v = Ψ (cellJ j v)) ∧
      ∀ o a b c, (o, PC.k a b c) ∈ (plumbOf j).stat → Ψ o = OInstr.imm a b c := by
  have hcont := cont_of hchk
  obtain ⟨-, hlists, hsn, -, hpv⟩ := shareStatic_spec hS.1
  have hA : ∀ i ≤ (snapsOf j).length, ∀ v c, (locW (certOf j) (winW (snapsOf j) i)).get? v.idx = some c →
      cellJ j v = c := fun i hi v c h ↦
    locW_get hcont (winW_le hsn hi) (checkWin_parts (hchk _ (winW_le hsn hi))).2 rfl (shareWin_spec (hS.2 i hi)).1 h
  have hA0 : ∀ v c, (locW (certOf j) 0).get? v.idx = some c → cellJ j v = c := hA 0 (Nat.zero_le _)
  obtain ⟨Ψ1, hI1, hs1⟩ := nameStepB_inv hfun (sh := bitsOf (plumbOf j).sh) (locAgree_strong hA0)
    (initStB_inv (plumbOf j) (cellJ j) (rd := rd) (σ := σ)) (fitV_of hA0 hpv)
  have hst0 : startSt j 0 = nameStep (locW (certOf j) 0) (bitsOf (plumbOf j).sh) (initSt (plumbOf j))
      (coreOf j).params := rfl
  have hfrom : fromW (coreOf j).body (snapsOf j) 0 = (coreOf j).body := by
    simp only [fromW, startW, beq_self_eq_true, Bool.cond_true, List.drop_zero]
  obtain ⟨Ψf, hf1, hf2⟩ := chainB_sound hfun hS hA _ 0 (Nat.zero_add _) (coreOf j).params Ψ1 (hst0 ▸ by
    simpa using hI1) es vs (by rw [hfrom]; exact hw) he
  refine ⟨Ψf, fun v hv hc ↦ hf1 v (by simpa [List.append_assoc] using hv) hc, fun o a b c ho ↦ ?_⟩
  simp only [listsOk, Exec.Trie.seq_eq, natSeq_eq, Bool.and_eq_true, List.all_eq_true] at hlists
  have := hlists.1.1.1.1.1 _ ho
  simp only [beq_iff_eq] at this
  have hocc : (initSt (plumbOf j)).occ.testBit o = true :=
    (testBit_bitsOf _ _).mpr (List.mem_map_of_mem (f := Prod.fst) ho)
  have h0 : initW (plumbOf j) o = OInstr.imm a b c := by simp only [initW, this.2]; rfl
  rw [hf2 o (by rw [hst0]; exact (hs1 o hocc).1), (hs1 o hocc).2, h0]

end FnPath


/-! ## At the deployed semantics -/

section Deployed

/-- At the deployed semantics, `KeyHoldsB` is `ShareSound.lean`'s `KeyHolds`. -/
theorem keyHoldsB_deployed (rd : Reader) (out : E) (op : ℕ) (ins : List E) :
    KeyHoldsB blakeDeployed rd out op ins = KeyHolds rd out op ins := rfl

/-- At the deployed semantics, `InvB` is `ShareSound.lean`'s `Inv`. -/
theorem invB_deployed (cg : V → ℕ) (rd : Reader) (σ : Val) (st : SSt) (pre : List V) (Ψ : ℕ → E) :
    InvB blakeDeployed cg rd σ st pre Ψ = Inv cg rd σ st pre Ψ :=
  propext ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩, fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7⟩⟩

/-- At the deployed semantics, `ConcB` is `ShareSound.lean`'s `Conc`. -/
theorem concB_deployed (cg : V → ℕ) (rd : Reader) (σ : Val) (st : SSt) (Ψ : ℕ → E) (pre : List V)
    (st' : SSt) (o : Memory.Out) : ConcB blakeDeployed cg rd σ st Ψ pre st' o = Conc cg rd σ st Ψ pre st' o := by
  cases o <;> simp only [ConcB, Conc, invB_deployed]

/-- **The deployed semantics is functional**: a compression's output words are those of its
digest. -/
theorem semFunctional_deployed : SemFunctional blakeDeployed := fun hx hy =>
  ⟨cellWords_inj hx.2.2.2.1 hy.2.2.2.1 (append4_inj (hx.2.2.2.2.2.2.trans hy.2.2.2.2.2.2.symm)).1,
    cellWords_inj hx.2.2.2.2.1 hy.2.2.2.2.1 (append4_inj (hx.2.2.2.2.2.2.trans hy.2.2.2.2.2.2.symm)).2⟩

end Deployed

end
end LeanVM.Guest.B2C
