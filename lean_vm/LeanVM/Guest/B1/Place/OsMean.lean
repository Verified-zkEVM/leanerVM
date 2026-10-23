/-
  LeanVM.Guest.B1.Place.OsMean

  open_stacked's callees by name: their meanings, a call relation dispatching on them, and the
  callees' placed completeness from a body proved at it on every memory.
-/

module

public import LeanVM.Guest.B1.Place.OsCallees
public import LeanVM.Guest.B1.Place.OsKidsC

/-!
# The callees' meanings, by name

`osKindOf f`: the kind of callee `f` names, read from `osKindTable` (the names `OsCalleesAtD`
covers, each with its meaning `OsKind.Pre`). `OsCalleesAtD.kindD`: a named callee is complete
placed on its meaning.

`osCR rd Sp`: the call relation of the memory `rd`, each named callee's meaning, the other callees
`Sp` (the squeeze loops, `opening_queries`, the residual loops, placed apart).

`os_calls_of_allOk`: a block holding at a relation `C` makes `C` hold of each taken call's frame.
`os_kid_named`, `os_kid_special`: a body holding at `osCR rd Sp` on every memory holding `Lk`
(and one such memory existing) makes each taken call with a name complete placed on `Lk`, and
each other one satisfy `Sp`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- The kinds of `open_stacked`'s named callees. -/
inductive OsKind where
  | fold
  | can
  | grind (n : ℕ)
  | ood (n : ℕ)
  | fm (n : ℕ)
  | rw (f r : ℕ)
  | cap (d : ℕ)
  | ffm (n : ℕ)
  deriving DecidableEq

/-- A kind's meaning. -/
def OsKind.Pre : OsKind → Reader → List E → List E → Prop
  | .fold => MeaningOpeningFold
  | .can => fun _ a r => MeaningAssertCanonical a r
  | .grind n => fun _ a r => MeaningGrindCheck n a r
  | .ood n => MeaningOpeningOodPoint n
  | .fm n => MeaningOpeningFinalMessage n
  | .rw f r => MeaningOpeningRowWeights f r
  | .cap d => MeaningVerifyMerkleCap d
  | .ffm n => MeaningFoldFinalMsg n

/-- The named callees and their kinds. -/
def osKindTable : List (String × OsKind) :=
  [("opening_fold", .fold), ("assert_canonical", .can), ("grind_check__L17", .grind 17),
    ("opening_row_weights__L4_L0", .rw 4 0), ("opening_row_weights__L6_L1", .rw 6 1)] ++
  oodPointNames.map (fun p ↦ (p.1, .ood p.2)) ++
  finalMessageNames.map (fun p ↦ (p.1, .fm p.2)) ++
  merkleCapNames.map (fun p ↦ (p.1, .cap p.2)) ++
  foldFinalMsgNames.map (fun p ↦ (p.1, .ffm p.2))

/-- The kind a name names. -/
def osKindOf (f : String) : Option OsKind := osKindTable.lookup f

theorem os_mem_of_lookup {f : String} {K : OsKind} :
    ∀ (l : List (String × OsKind)), l.lookup f = some K → (f, K) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      have : f = a := by simpa using hb
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (os_mem_of_lookup l h)

/-- **A named callee is complete placed on its meaning.** -/
theorem OsCalleesAtD.kindD (h : OsCalleesAtD fs cert κ) {f : String} {K : OsKind}
    (hK : osKindOf f = some K) : CompleteRelD fs cert κ f K.Pre := by
  have hm := os_mem_of_lookup osKindTable hK
  simp only [osKindTable, List.mem_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rcases hm with ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩) | ⟨p, hp, rfl, rfl⟩
  · exact h.fold
  · exact h.canonical
  · exact h.grind
  · exact h.rowWeights4
  · exact h.rowWeights6
  · exact h.ood p hp
  · exact h.finalMsg p hp
  · exact h.merkleCap p hp
  · exact h.foldFinal p hp

/-- **The call relation of a memory**: a named callee's meaning there, else `Sp`. -/
def osCR (rd : Reader) (Sp : String → List E → List E → Prop) : CallRel := fun f a r ↦
  match osKindOf f with
  | some K => K.Pre rd a r
  | none => Sp f a r

theorem osCR_named {rd : Reader} {Sp : String → List E → List E → Prop} {f : String} {K : OsKind}
    (hK : osKindOf f = some K) {a r : List E} (h : K.Pre rd a r) : osCR rd Sp f a r := by
  unfold osCR; rw [hK]; exact h

theorem osCR_special {rd : Reader} {Sp : String → List E → List E → Prop} {f : String}
    (hK : osKindOf f = none) {a r : List E} (h : Sp f a r) : osCR rd Sp f a r := by
  unfold osCR; rw [hK]; exact h

/-- **A block holding at `C` makes `C` hold of each taken call's frame.** -/
theorem os_calls_of_allOk {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ {pre : List Stmt}, AllOk C rd σ pre →
      ∀ c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
        C c.f (c.args.map σ) (c.rets.map σ)
  | [], _, c, hc, _ => by simp at hc
  | s :: pre, h, c, hc, ht => by
    have h0 : StmtOk C rd σ s := h s (List.mem_cons_self ..)
    have h1 : AllOk C rd σ pre := fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    match s, h0 with
    | .atom _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .call f args rets, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h0
      · exact os_calls_of_allOk h1 c hc ht
    | .callIf cv f args, h0 =>
      simp only [List.filterMap_cons, Main.Stmt.callS, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [Main.mkCall, decide_eq_true_eq] at ht
        exact h0.2 ht
      · exact os_calls_of_allOk h1 c hc ht
    | .ret _, _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .ite .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .match_ .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht
    | .dispatch .., _ =>
      simp only [List.filterMap_cons, Main.Stmt.callS] at hc
      exact os_calls_of_allOk h1 c hc ht

theorem os_allOk_mono {C C' : CallRel} {rd : Reader} {σ : Val} (hC : ∀ f a r, C f a r → C' f a r) :
    ∀ {ss : List Stmt}, AllOk C rd σ ss → AllOk C' rd σ ss := fun h s hs ↦ by
  have h0 := h s hs
  match s, h0 with
  | .atom _, h0 => exact h0
  | .call .., h0 => exact hC _ _ _ h0
  | .callIf .., h0 => exact ⟨h0.1, fun hc ↦ hC _ _ _ (h0.2 hc)⟩
  | .ret _, h0 => exact h0
  | .ite .., h0 => exact h0
  | .match_ .., h0 => exact h0
  | .dispatch .., h0 => exact h0

/-- **A named call of a body proved at `osCR` on every memory holding `Lk`** is complete placed
on `Lk`. -/
theorem os_kid_named (hk : OsCalleesAtD fs cert κ) {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp) rd σ pre)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    {K : OsKind} (hK : osKindOf c.f = some K) :
    CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) :=
  hk.kindD hK _ _ Lk fun rd hl hm ↦ by
    have h := os_calls_of_allOk (hall rd hl hm) c hc ht
    unfold osCR at h; rw [hK] at h; exact h

/-- **Another call of such a body** satisfies `Sp`, one memory holding `Lk` existing. -/
theorem os_kid_special {Lk : Layout} {σ : Val} {pre : List Stmt}
    {Sp : String → List E → List E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lk → AllOk (osCR rd Sp) rd σ pre)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk)
    {c : Call} (hc : c ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (ht : c.taken = true)
    (hK : osKindOf c.f = none) : Sp c.f (c.args.map σ) (c.rets.map σ) := by
  obtain ⟨rd0, hl, hm⟩ := hex
  have h := os_calls_of_allOk (hall rd0 hl hm) c hc ht
  unfold osCR at h; rw [hK] at h; exact h

end
end LeanVM.Guest.B1
