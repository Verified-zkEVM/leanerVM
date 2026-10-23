/-
  LeanVM.Guest.B1.Place.OsKidsC

  The callee relation of a placed body: every call complete on the caller's words. After mumbai's
  `B1/Whir/OsKidsA.lean`.
-/

module

public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Whir.Flat

/-!
# The callees of a placed body, from its `Rel`-level walk

`osKC fs cert κ Lk`: the relation "the callee is `CompleteAtD` on the words `Lk`, returning the
frame's words". A flat block proved at that relation (`AllOk`, as `open_stacked`'s blocks are,
generic in the relation) gives every taken call's placed completeness (`kids_of_allOk`), what
`os_kids_block` takes. `osKC_of`: a callee's `CompleteRelD` on a meaning holding on every memory
holding `Lk`. `os_readsAt_shift`, `os_reads_noLow`: reading the caller's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- A callee complete on the words `Lk`, returning its frame's words. -/
def osKC (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Layout) : CallRel :=
  fun f a r => CompleteAtD fs cert κ f Lk a (Returns r)

/-- **A callee complete on its meaning**, the meaning holding on every memory holding `Lk`. -/
theorem osKC_of {f : String} {Pre : Reader → List E → List E → Prop}
    (h : CompleteRelD fs cert κ f Pre) {Lk : Layout} {args rets : List E}
    (hp : ∀ rd, LowDef κ rd → MemL rd Lk → Pre rd args rets) : osKC fs cert κ Lk f args rets :=
  h args rets Lk hp

/-- **The calls of a flat block proved at `osKC`**, each taken one complete placed. -/
theorem kids_of_allOk {Lk : Layout} {rd : Reader} {σ : Val} :
    ∀ {pre : List Stmt}, AllOk (osKC fs cert κ Lk) rd σ pre →
      ∀ c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
        CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ))
  | [], _, c, hc, _ => by simp at hc
  | s :: pre, h, c, hc, ht => by
    have h0 : StmtOk (osKC fs cert κ Lk) rd σ s := h s (List.mem_cons_self ..)
    have h1 : AllOk (osKC fs cert κ Lk) rd σ pre := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    match s, h0 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact kids_of_allOk h1 c hc ht
    | .call f args rets, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h0
      · exact kids_of_allOk h1 c hc ht
    | .callIf cv f args, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        exact h0.2 ht
      · exact kids_of_allOk h1 c hc ht
    | .ret _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact kids_of_allOk h1 c hc ht
    | .ite .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact kids_of_allOk h1 c hc ht
    | .match_ .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact kids_of_allOk h1 c hc ht
    | .dispatch .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact kids_of_allOk h1 c hc ht

theorem os_readsAt_shift {rd : Reader} {cur : E} {xs : List E} (h : ReadsAt rd cur xs) {p n : ℕ}
    (hp : p + n ≤ xs.length) : ReadsAt rd (cur * gen ^ p) ((xs.drop p).take n) := by
  intro k hk
  simp only [List.length_take, List.length_drop] at hk
  rw [loadHolds_mul_gen_pow, List.getElem_take, List.getElem_drop]
  exact h (p + k) (by omega)

/-- **Words every defined-low memory holding `Lin` holds, every memory holding `Lin` holds.** -/
theorem os_reads_noLow {Lin : Layout} {p : E} {xs : List E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd p xs) {rd : Reader} (hL : MemL rd Lin) :
    ReadsAt rd p xs := by
  let rd' : Reader := fun A => match rd A with | some v => some v | none => some 0
  have hsome : ∀ A v, rd A = some v → rd' A = some v := fun A v h => by simp only [rd', h]
  have hlow : LowDef κ rd' := fun i _ => by
    simp only [rd']; split <;> rfl
  have hL' : MemL rd' Lin := fun q hq k hk => ⟨(hL q hq k hk).1, hsome _ _ (hL q hq k hk).2⟩
  intro k hk
  have h' := hall rd' hlow hL' k hk
  obtain ⟨i, hi, q, hq, h1, h2⟩ := os_addr_in_regionL (A := p.limb 0 * Parameters.gpow k) (v := xs[k])
    (fun rd2 hl2 hm2 => (hall rd2 hl2 hm2 k hk).2) hlow hL'
  have hc := (hL q hq (i - q.1) (by omega)).2
  rw [Main.addr_ofK, show q.1 + (i - q.1) = i by omega] at hc
  obtain ⟨v, hv⟩ : ∃ v, rd (Parameters.gpow i) = some v := ⟨_, hc⟩
  refine ⟨h'.1, ?_⟩
  have e := h'.2
  rw [hi, hsome _ _ hv] at e
  rw [hi, hv, e]

end
end LeanVM.Guest.B1
