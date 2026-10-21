/-
  LeanVM.Guest.B1.Comp.Da.PlacedIn

  `RelInTW` (`B1/Da/WeightIn.lean`) and the self-calling loops by region (`B1/Da/LoopIn.lean`)
  under any semantics of `BLAKE2S`, and the placed relations of the functions free of `BLAKE2S`
  carried over from the deployed ones.
-/

module

public import LeanVM.Guest.B1.Da.LoopIn
public import LeanVM.Guest.B1.Comp.FreeTree
public import LeanVM.Guest.Memory.GuestRelInB
public import LeanVM.Guest.Memory.StraightB

/-!
# Trees of known words within weights, under any semantics

`WeightIn.lean`'s `RelInTW` with `S : BlakeSem` a parameter (`RelInTWS S`): `relInTWS_of_inv`
builds the tree of a `Program.RelB S` proof by an invariant on instances, its words and weights
by `Tot`; `relAtInWS_of_relInTWS_pure` places a pure function's anywhere; `loop_relInTWS` is
`loop_relInT` (`LoopIn.lean`). `relAtInWS_of_freeOn`: the deployed placed relation within weights
(`Main.RelAtInW`) of a function free of `BLAKE2S` holds under any semantics.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInW RelAtInWS)

@[expose] public section

variable {S : BlakeSem} (fs : String → ℕ)

variable (S) in
/-- **`RelInTW` under `S`.** -/
def RelInTWS (rd : Reader) (R : ℕ → Prop) (n : ℕ) (f : String) (args rets : List E)
    (W : (String → ℕ) → ℕ) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.ValidB S coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.LoadsR coreProgram R ∧ t.total fs = n ∧ ∀ θ, t.weight θ ≤ W θ

theorem kids_of_relInTWS {rd : Reader} {σ : Val} {R : ℕ → Prop}
    (Tot : (String → ℕ) → String → List E → ℕ) :
    ∀ cs : List Call, (∀ c ∈ cs, c.taken = false → coreProgram.Takes c.f c.args.length = true) →
    (∀ c ∈ cs, c.taken = true → ∃ rets, c.rets.map σ = rets ∧
      RelInTWS S fs rd R (Tot fs c.f (c.args.map σ)) c.f (c.args.map σ) rets
        fun θ => Tot θ c.f (c.args.map σ)) →
    ∃ ks, Tree.KidsValidB S coreProgram rd σ cs ks ∧ Tree.BufsOkKids coreProgram ks ∧
      Tree.LoadsRKids coreProgram R ks ∧ Tree.totalKids fs ks = callsTot fs (Tot fs) σ cs ∧
      ∀ θ, Tree.weightKids θ ks ≤ callsTot θ (Tot θ) σ cs
  | [], _, _ => ⟨[], by simp [Tree.KidsValidB], by rw [Tree.BufsOkKids]; trivial,
      by rw [Tree.LoadsRKids]; trivial, by simp [Tree.totalKids, callsTot],
      fun θ => by simp [Tree.weightKids, callsTot]⟩
  | c :: cs, hw, hc => by
      obtain ⟨ks, hv, hb, hl, ht, hwt⟩ := kids_of_relInTWS Tot cs
        (fun c' h => hw c' (List.mem_cons_of_mem _ h)) (fun c' h => hc c' (List.mem_cons_of_mem _ h))
      by_cases htk : c.taken = true
      · obtain ⟨rets, hrets, k, hn, hkv, hkb, hkl, hkt, hkw⟩ := hc c List.mem_cons_self htk
        refine ⟨k :: ks, ⟨hn, by rw [ite_eq_left htk, hrets]; exact hkv, hv⟩,
          by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, by rw [Tree.LoadsRKids]; exact ⟨hkl, hl⟩, ?_,
          fun θ => ?_⟩
        · rw [totalKids_cons, hkt, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_left htk]
        · have := hwt θ
          have := hkw θ
          simp only [Tree.weightKids, callsTot, List.map_cons, List.sum_cons, ite_eq_left htk] at *
          omega
      · obtain ⟨σ', hph⟩ := phantom_of_takes (P := coreProgram) (f := c.f) (ws := c.args.map σ)
          (by rw [List.length_map]; exact hw c List.mem_cons_self (by simpa using htk))
        refine ⟨.phantom c.f σ' :: ks, ⟨rfl, by rw [ite_eq_right htk]; exact ⟨⟨_, _, rfl⟩, hph⟩, hv⟩,
          by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hb⟩,
          by rw [Tree.LoadsRKids, Tree.LoadsR]; exact ⟨trivial, hl⟩, ?_, fun θ => ?_⟩
        · rw [totalKids_cons, ht, callsTot, callsTot, List.map_cons, List.sum_cons, ite_eq_right htk]
          rfl
        · have := hwt θ
          simp only [Tree.weightKids, Tree.weight, callsTot, List.map_cons, List.sum_cons,
            ite_eq_right htk] at *
          omega

/-- **`RelInTWS` by an invariant on instances**, the words at every frame function by `Tot`
(`relInTW_of_inv`). -/
theorem relInTWS_of_inv {rd : Reader} {R : ℕ → Prop} (Inv : String → List E → Prop)
    (Tot : (String → ℕ) → String → List E → ℕ)
    (hinv : ∀ f args σ fn es vs, Inv f args → coreProgram.find? f = some fn → fn.params.map σ = args →
      walk σ fn.body = .ret es vs → (∀ e ∈ es, e.OkB S (coreProgram.RelB S rd) rd σ) →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i) ∧
        (∀ c ∈ calls es, c.taken = true → Inv c.f (c.args.map σ)) ∧
        ∀ θ, Tot θ f args = θ f + callsTot θ (Tot θ) σ (calls es) + (allocs σ es).sum) :
    ∀ {f : String} {args rets : List E}, Inv f args → coreProgram.RelB S rd f args rets →
      RelInTWS S fs rd R (Tot fs f args) f args rets fun θ => Tot θ f args := by
  intro f args rets hI hrel
  obtain ⟨n, hn⟩ := hrel
  induction n generalizing f args rets with
  | zero => exact hn.elim
  | succ n ih =>
    obtain ⟨fn, hf, σ, hp, hh⟩ := hn
    have hs := walkB_sat (P := coreProgram) fn.body
      (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
    cases hw : walk σ fn.body with
    | fall es => rw [hw] at hs; exact hs.2.elim
    | stuck => rw [hw] at hs; exact hs.elim
    | ret es vs =>
      rw [hw] at hs
      obtain ⟨hok, hr⟩ := hs
      have hok' : ∀ e ∈ es, e.OkB S (coreProgram.RelB S rd) rd σ := fun e he =>
        ⟨(hok e he).1, fun g a r heq => relNB_le_rel coreProgram n _ _ _ ((hok e he).2 g a r heq)⟩
      obtain ⟨hload, hcalls, htot⟩ := hinv f args σ fn es vs hI hf hp hw hok'
      obtain ⟨ks, hkv, hkb, hkl, hkt, hkw⟩ := kids_of_relInTWS fs Tot (calls es)
        (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw)
        (fun c hc ht => ⟨_, rfl, ih (hcalls c hc ht)
          ((hok _ (mem_calls_taken hc ht)).2 c.f c.args c.rets rfl)⟩)
      refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, fun e he => (hok e he).1, hkv⟩,
        ?_, ?_, ?_, fun θ => ?_⟩
      · rw [Tree.BufsOk, events_node hf hw]
        exact ⟨rfl, hkb⟩
      · rw [Tree.LoadsR, events_node hf hw]
        exact ⟨hload, hkl⟩
      · rw [total_node, hkt, htot fs]
      · show Tree.weight θ (Memory.Tree.node f σ (allocs σ es) ks) ≤ Tot θ f args
        rw [htot θ]
        have := hkw θ
        simp only [Tree.weight]
        omega

/-- **A pure function's `RelInTWS` is placed anywhere**, within the same weights
(`relAtInW_of_relInTW_pure`). -/
theorem relAtInWS_of_relInTWS_pure (cert : String → V → ℕ) {Sz : List String}
    (hS : coreProgram.PureIn Sz) {rd : Reader} {R : ℕ → Prop} {n : ℕ} {g : String} (hg : g ∈ Sz)
    {args rets : List E} {W : (String → ℕ) → ℕ} (h : RelInTWS S fs rd R n g args rets W) :
    ∀ fp, RelAtInWS S fs cert wId rd R (fun _ => False) fp n g args rets W := by
  obtain ⟨t, hn, hv, hb, hl, ht, hw⟩ := h
  exact fun fp => ⟨t, hn, hv, hb, placedB_of_pure hS t hv hb (hn ▸ hg) fp, ht,
    loadsIn_of_loadsR t R fp hl, fun _ h => h.elim, hw⟩

/-- **A self-calling loop by region under `S`** (`loop_relInT`). -/
theorem loop_relInTWS {rd : Reader} {R : ℕ → Prop} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Main.Stmt.straight = true) {c : V} {targs : List V}
    (hcs : pre.filterMap Main.Stmt.callS = [(some c, f, targs, [])])
    (hal : pre.filterMap Main.Stmt.allocSz = []) {ps : List E} {n : ℕ} (hn : n < 2 ^ 33)
    (hit : ∀ j < n, ∀ σ : Val, fn.params.map σ = gen ^ j :: ps →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.OkB S (coreProgram.RelB S rd) rd σ) →
      (∀ A ∈ loadAddrs σ (pre.flatMap (Main.slEvs σ)), ∃ i, A = gpow i ∧ R i) ∧
        (σ c ≠ 0 ↔ j + 1 < n) ∧ targs.map σ = gen ^ (j + 1) :: ps)
    {j : ℕ} (hj : j < n) (h : coreProgram.RelB S rd f (gen ^ j :: ps) []) :
    RelInTWS S fs rd R ((n - j) * fs f + fs f) f (gen ^ j :: ps) [] fun θ => (n - j) * θ f + θ f := by
  have key := relInTWS_of_inv fs (R := R) (fun f' args => f' = f ∧ ∃ j < n, args = gen ^ j :: ps)
    (fun θ _ args => (n - logG (args.headD 0)) * θ f + θ f)
    (fun f' args σ fn' es vs hI hf' hp hw hok => ?_) ⟨rfl, j, hj, rfl⟩ h
  · simpa [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)] using key
  obtain ⟨rfl, j, hj, rfl⟩ := hI
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hb, Main.walk_straight σ _ _ hs] at hw
  obtain ⟨rfl, -⟩ : pre.flatMap (Main.slEvs σ) = es ∧ _ := by
    injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal', -, hcl⟩ := Main.straight_parts σ _ hs
  obtain ⟨hld, htk, hta⟩ := hit j hj σ hp hok
  have hcalls : calls (pre.flatMap (Main.slEvs σ)) = [⟨f', targs, [], decide (σ c ≠ 0)⟩] := by
    rw [hcl, hcs]; rfl
  refine ⟨hld, fun c' hc' ht => ?_, ?_⟩
  · rw [hcalls] at hc'
    obtain rfl := List.mem_singleton.mp hc'
    simp only [decide_eq_true_eq] at ht
    exact ⟨rfl, j + 1, htk.mp ht, hta⟩
  · intro θ
    rw [hcalls, hal', hal, callsTot]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, List.headD_cons, hta]
    rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)]
    by_cases hj1 : j + 1 < n
    · simp only [htk.mpr hj1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega), show n - j = (n - (j + 1)) + 1 by omega]
      ring
    · have : ¬ σ c ≠ 0 := fun h => hj1 (htk.mp h)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show n - j = 1 by omega]
      ring

/-- **The deployed placed relation within weights of a function free of `BLAKE2S`** holds under
any semantics. -/
theorem relAtInWS_of_freeOn {F : List String} (hP : coreProgram.FreeOn F = true) {f : String}
    (hf : f ∈ F) (cert : String → V → ℕ) {Θ : Type} {w : Θ → String → ℕ} {rd : Reader}
    {R D : ℕ → Prop} {fp n : ℕ} {args rets : List E} {Bw : Θ → ℕ}
    (h : RelAtInW fs cert w rd R D fp n f args rets Bw) :
    RelAtInWS S fs cert w rd R D fp n f args rets Bw := by
  obtain ⟨t, hnm, hv, h'⟩ := LeanVM.Guest.B1.relAtInWS_deployed.mpr h
  exact ⟨t, hnm, (validB_freeOn (S' := blakeDeployed) hP t args rets (hnm ▸ hf)).mpr hv, h'⟩

end
end LeanVM.Guest.B1.Digest
