/-
  LeanVM.Guest.B1.Comp.Whir.LocT.Decode

  The stacked opening's decoder on frame valuations: the predicate `OsQ` its placed tree satisfies.
-/

module

public import LeanVM.Guest.Located.VerifySubB
public import LeanVM.Guest.Memory.LoadEqns
public import LeanVM.Guest.B2C.NodeAgree

/-!
# Decoding the stacked opening's openings from a tree

V_I's decoder of `open_stacked`'s openings (`wOLB S fr L`, `Located/VerifySubB.lean`) reads each
callee's valuation at the frame `fr` names (`frameDecB`, `loopDecB`) and the memory `L.read`. Here
the same decoder with the frame valuations a function `V` of the call (callee, argument and return
words) and the memory a reader `rd`: `wlV`, `wqDecV`, `wqV` (`wlLB`, `wqDecB`, `wqLB`). At
`V := fun f a r => valAt L f (frameOfB S fr L f a r)` and `rd := L.read` they are V_I's
(`wqLB_eq_wqV`, `wOLB_eq`).

`KidsLink V t`: every entered call to a decoded callee (`osDecNames`) of every node of `t` has, under
`V`, a valuation agreeing with the callee tree it is placed with on that tree's named cells
(`B2C.NodeAgree`). `OsDec μ r os t`: on every reader satisfying `t`'s load equations, every `V` linked
to `t` and every valuation agreeing with `t`'s node on its named cells, the openings decoded are
`os` — what `open_stacked`'s placed completeness over a model gives (`CompleteOpenAtBCL`, `OsQ`).
`CellsOk`, `nodeAgree_read`: such a valuation is the node's at the named values whose cells lie in
its frame.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Located
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- A frame valuation function: the valuation of a call's callee, by its name, argument and return
words. -/
abbrev FrameVals : Type := String → List E → List E → Val

/-- `frameDecB` at frame valuations. -/
def frameDecV {α : Type} (V : FrameVals) (f : String) (wit : Val → α) (args rets : List E) : α :=
  wit (V f args rets)

/-- `loopDecB` at frame valuations. -/
noncomputable def loopDecV {α : Type} (V : FrameVals) (f : String) (Wf : List E → E) (wit : Val → α)
    (args _rets : List E) : List α :=
  match args with
  | [] => []
  | x :: ps => (List.range (loopCount x (Wf ps))).map fun j => frameDecV V f wit (x * gen ^ j :: ps) []

/-- `wlLB` at frame valuations and a reader. -/
noncomputable def wlV (rd : Reader) (V : FrameVals) (base I blocks pd cd : ℕ) (loop : String) :
    List E → List E → List Opening :=
  loopDecV V loop (fun ps => ps.getD 0 0) (oqOpeningOf base I blocks pd cd rd)

/-- `wqDecB` at frame valuations and a reader. -/
noncomputable def wqDecV (rd : Reader) (V : FrameVals) (name loop : String) (base I blocks pd cd : ℕ)
    (args rets : List E) : List Opening :=
  frameDecV V name (fun σ => oqQueriesOs (wlV rd V base I blocks pd cd loop) σ) args rets

/-- `wqLB` at frame valuations and a reader. -/
noncomputable def wqV (rd : Reader) (V : FrameVals) (cfg : OsCfg) (i : ℕ) (args rets : List E) :
    List Opening :=
  match oqLookup (cfg.lv i).queriesFn with
  | some (loop, base, I, blocks, pd, cd) => wqDecV rd V (cfg.lv i).queriesFn loop base I blocks pd cd args rets
  | none => []

/-- The frame valuations V_I's decoder reads. -/
noncomputable def frameValsOf (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ) :
    FrameVals :=
  fun f a r => valAt L f (frameOfB S fr L f a r)

theorem wqLB_eq_wqV (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ) :
    wqLB S fr L = wqV L.read (frameValsOf S fr L) := rfl

/-- **V_I's decoder of `open_stacked`'s openings at frame valuations.** -/
theorem wOLB_eq (S : BlakeSem) (fr : String → List E → Option ℕ) {κ : ℕ} (L : MemImage κ) (name : String)
    (args rets : List E) :
    wOLB S fr L name args rets =
      osOsOf (osCfgOf name) (frameValsOf S fr L name args rets) (wqV L.read (frameValsOf S fr L) (osCfgOf name)) :=
  rfl

/-- The callees the decoders read through frame valuations: the `opening_queries` specializations
and their loop helpers. -/
def osDecNames : List String := oqTable.map (·.1) ++ oqTable.map (·.2.1)

theorem mem_osDecNames_name {name loop : String} {base I blocks pd cd : ℕ}
    (h : oqLookup name = some (loop, base, I, blocks, pd, cd)) : name ∈ osDecNames := by
  unfold oqLookup at h
  rcases hf : oqTable.find? (fun e => e.1 == name) with _ | e
  · rw [hf] at h; cases h
  · have hn : e.1 = name := by simpa using List.find?_some hf
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some hf, hn⟩)

theorem mem_osDecNames_loop {name loop : String} {base I blocks pd cd : ℕ}
    (h : oqLookup name = some (loop, base, I, blocks, pd, cd)) : loop ∈ osDecNames := by
  unfold oqLookup at h
  rcases hf : oqTable.find? (fun e => e.1 == name) with _ | e
  · rw [hf] at h; cases h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact List.mem_append_right _ (List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some hf, by rw [h]⟩)

/-- Each entered call of `cs` to a decoded callee (`osDecNames`) has, under `V`, a valuation
agreeing with the callee tree it is placed with on the cells that tree's path names
(`B2C.NodeAgree`). -/
def KidsLinkCalls (V : FrameVals) (σ : Val) : List Call → List Tree → Prop
  | c :: cs, k :: ks => (c.taken = true → c.f ∈ osDecNames → B2C.NodeAgree k (V c.f (c.args.map σ) (c.rets.map σ))) ∧
      KidsLinkCalls V σ cs ks
  | _, _ => True

mutual
/-- **Every entered call of every node of `t` has, under `V`, its callee tree's valuation.** -/
def KidsLink (V : FrameVals) : Tree → Prop
  | t@(.node _ σ _ ks) => KidsLinkCalls V σ (calls (t.events coreProgram)) ks ∧ KidsLinkKids V ks
  | .phantom .. => True

/-- `KidsLink` of the callees. -/
def KidsLinkKids (V : FrameVals) : List Tree → Prop
  | [] => True
  | k :: ks => KidsLink V k ∧ KidsLinkKids V ks
end

/-- **The opening's decoding**: on every reader satisfying the tree's load equations, every frame
valuation linked to it and every valuation agreeing with its node on its named cells, the openings
decoded are `os`. -/
def OsDec (μ r : ℕ) (os : List Opening) (t : Tree) : Prop :=
  ∀ (rd : Reader) (V : FrameVals) (σ' : Val), (∀ q ∈ t.loadEqns coreProgram, rd q.1 = some q.2) → KidsLink V t →
    B2C.NodeAgree t σ' → osOsOf (osCfgOf (openName μ r)) σ' (wqV rd V (osCfgOf (openName μ r))) = os

/-- The values `rs` of `f`'s frames have cells in its frame. -/
def CellsOk (f : String) (rs : List V) : Prop :=
  ∀ j, B2C.idxOf f = some j → ∀ v ∈ rs, 2 ≤ B2C.cellJ j v ∧ B2C.cellJ j v < B2C.fsN j

theorem cellsOk_of {f : String} {j : ℕ} (hj : B2C.idxOf f = some j) {rs : List V}
    (h : (rs.all fun v => Nat.ble 2 (B2C.cellJ j v) && Nat.blt (B2C.cellJ j v) (B2C.fsN j)) = true) :
    CellsOk f rs := by
  intro j' hj' v hv
  rw [hj] at hj'
  cases hj'
  have := List.all_eq_true.mp h v hv
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact this

/-- **A valuation agreeing with a node on its named cells is its valuation at a named value with a
cell in its frame.** -/
theorem nodeAgree_read {f : String} {σ σ' : Val} {bufs : List ℕ} {ks : List Tree} {fn : Fn}
    {es : List Memory.Ev} {vs : List V} (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs)
    (h : B2C.NodeAgree (.node f σ bufs ks) σ') {rs : List V} (hc : CellsOk f rs) {v : V} (hv : v ∈ rs)
    (hn : v ∈ B2C.namedOf fn.params es vs) : σ' v = σ v := by
  obtain ⟨j, hj⟩ : ∃ j, B2C.idxOf f = some j := by
    unfold B2C.idxOf
    rcases hi : coreProgram.indexOf? f with _ | i
    · rw [B2C.find?_none hi] at hf; cases hf
    · exact ⟨i + 1, rfl⟩
  obtain ⟨i, -, hi, -, hfi, hco, -⟩ := B2C.fn_of_idx hj
  rw [hf, Option.some.injEq] at hfi
  rw [← hfi] at hco
  obtain ⟨h2, h3⟩ := hc j hj v hv
  exact B2C.NodeAgree.eq h hj (by rw [hco]; exact hw) (by rw [hco]; exact hn) h2 h3

end
end LeanVM.Guest.B1
