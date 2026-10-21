/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OqCongr

  The queries' decoders read only values their frames' paths name.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OqIter

/-!
# The decoders read named values

`oqOpeningOf_congr`, `oqQueriesOs_congr`: the loop helper's and `opening_queries`' decoders agree
on valuations agreeing on the values they read; `oqIter_named`, `oqTop_named`: those values are
named by the frames' paths (`B2C.namedOf`), so a valuation agreeing with the frame on its named
cells decodes alike.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The loop helper's decoder reads the cap, the row, the bit run's pointer, the children.** -/
theorem oqOpeningOf_congr {base I blocks pd cd : ℕ} {rd : Reader} {σ σ' : Val} (h7 : σ' (.n 7) = σ (.n 7))
    (hrow : ∀ j < oqR base I, σ' (.n (8 + j)) = σ (.n (8 + j)))
    (hb : σ' (.n (oqK2 base I blocks + 8)) = σ (.n (oqK2 base I blocks + 8)))
    (hp : ∀ k < 4 * pd, σ' (.n (oqP base I blocks + k)) = σ (.n (oqP base I blocks + k))) :
    oqOpeningOf base I blocks pd cd rd σ' = oqOpeningOf base I blocks pd cd rd σ := by
  have hl : leafWords base I (rowv σ') = leafWords base I (rowv σ) :=
    List.map_congr_left fun j hj => by rw [rowv, rowv, hrow j (List.mem_range.mp hj)]
  have hs : ∀ q, pathSibs (fun k => σ' (.n (oqP base I blocks + k))) q pd =
      pathSibs (fun k => σ (.n (oqP base I blocks + k))) q pd := fun q =>
    List.map_congr_left fun l hl' => by
      have := List.mem_range.mp hl'
      beta_reduce
      rw [hp (4 * l) (by omega), hp (4 * l + 1) (by omega), hp (4 * l + 2) (by omega), hp (4 * l + 3) (by omega)]
  simp only [oqOpeningOf]
  rw [hl, hs, hb, h7]

/-- The values `opening_queries`' decoder reads. -/
def oqTopReads : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 8, .n 11, .n 12]

/-- **`opening_queries`' decoder reads its parameters and the loop's guard and entry.** -/
theorem oqQueriesOs_congr {wl : List E → List E → List Opening} {σ σ' : Val}
    (h : ∀ v ∈ oqTopReads, σ' v = σ v) : oqQueriesOs wl σ' = oqQueriesOs wl σ := by
  simp only [oqQueriesOs, h (.n 0) (by simp [oqTopReads]), h (.n 1) (by simp [oqTopReads]),
    h (.n 2) (by simp [oqTopReads]), h (.n 3) (by simp [oqTopReads]), h (.n 4) (by simp [oqTopReads]),
    h (.n 5) (by simp [oqTopReads]), h (.n 8) (by simp [oqTopReads]), h (.n 11) (by simp [oqTopReads]),
    h (.n 12) (by simp [oqTopReads])]

/-- The values the loop helper's decoder reads: the cap, the bit run's pointer, the row, the hinted
children. -/
def oqLoopReads (base I blocks pd : ℕ) : List V :=
  .n 7 :: .n (oqK2 base I blocks + 8) :: ((List.range (oqR base I)).map fun j => .n (8 + j)) ++
    (List.range (4 * pd)).map fun k => .n (oqP base I blocks + k)

/-- A value an atom of a straight-line path names is named. -/
theorem mem_named_atom {σ : Val} {params : List V} {pre : List Stmt} {vs : List V} {a : Atom}
    (h : Stmt.atom a ∈ pre) {v : V} (hv : v ∈ atomUses a) :
    v ∈ B2C.namedOf params (pre.flatMap (Main.slEvs σ)) vs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, mem_slEvs_of h, hv⟩))

/-- A parameter is named. -/
theorem mem_named_param {params : List V} {es : List Memory.Ev} {vs : List V} {v : V} (h : v ∈ params) :
    v ∈ B2C.namedOf params es vs :=
  List.mem_append_left _ (List.mem_append_left _ h)

/-- A conditional call's guard is named. -/
theorem mem_named_callIf_cond {σ : Val} {params : List V} {pre : List Stmt} {vs : List V} {c : V} {f : String}
    {args : List V} (h : Stmt.callIf c f args ∈ pre) : c ∈ B2C.namedOf params (pre.flatMap (Main.slEvs σ)) vs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨.inK c,
    List.mem_flatMap.mpr ⟨_, h, by simp [Main.slEvs]⟩, by simp [Ev.uses]⟩))

/-- A conditional call's arguments are named. -/
theorem mem_named_callIf_arg {σ : Val} {params : List V} {pre : List Stmt} {vs : List V} {c : V} {f : String}
    {args : List V} (h : Stmt.callIf c f args ∈ pre) {v : V} (hv : v ∈ args) :
    v ∈ B2C.namedOf params (pre.flatMap (Main.slEvs σ)) vs := by
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ?_))
  by_cases h0 : σ c = 0
  · exact ⟨.skip f args, List.mem_flatMap.mpr ⟨_, h, by simp [Main.slEvs, h0]⟩, by simpa [Ev.uses] using hv⟩
  · exact ⟨.call f args [], List.mem_flatMap.mpr ⟨_, h, by simp [Main.slEvs, h0]⟩, by simpa [Ev.uses] using hv⟩

/-- **The values the loop helper's decoder reads are named by its path.** -/
theorem oqIter_named {base I blocks pd cd : ℕ} (hs : OqShape base I blocks pd cd) (loop : String) (σ : Val)
    (vs : List V) :
    (∀ j < oqR base I, V.n (8 + j) ∈ B2C.namedOf [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      ((oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)) vs) ∧
    V.n (oqK2 base I blocks + 8) ∈ B2C.namedOf [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      ((oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)) vs ∧
    (∀ k < 4 * pd, V.n (oqP base I blocks + k) ∈ B2C.namedOf [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      ((oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)) vs) ∧
    V.n 7 ∈ B2C.namedOf [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      ((oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)) vs := by
  refine ⟨fun j hj => ?_, ?_, fun k hk => ?_, mem_named_param (by simp)⟩
  · have hm : Stmt.atom (.hint (.witness "merkle_leaf_rows" (.stack ((List.range (oqR base I)).map fun j => .n (8 + j)))))
        ∈ oqLoopPre base I blocks pd cd loop := by
      refine mem_oqLoopPre ?_
      simp only [oqLoopBody, List.mem_append]
      refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
      rcases hs.hbase with rfl | rfl
      · simp [oqRows, oqRows0, oqRowHint, oqR]
      · simp [oqRows, oqRows1, oqRowHint, oqR]
    exact mem_named_atom hm (by simpa [atomUses, hintUses, destUses] using hj)
  · have hm : Stmt.atom (.load (.n (oqK2 base I blocks + 8)) (.n (oqK2 base I blocks + 7)) 0) ∈
        oqLoopPre base I blocks pd cd loop := by
      refine mem_oqLoopPre ?_
      simp only [oqLoopBody, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (by simp [oqSumT])))
    exact mem_named_atom hm (by simp [atomUses])
  · have hm : Stmt.atom (.hint (.witness "merkle_children" (.stack ((List.range (4 * pd)).map fun j =>
        .n (oqP base I blocks + j))))) ∈ oqLoopPre base I blocks pd cd loop := by
      refine mem_oqLoopPre ?_
      simp only [oqLoopBody, List.mem_append]
      exact Or.inl (Or.inr (by simp [oqPathT]))
    exact mem_named_atom hm (by simpa [atomUses, hintUses, destUses] using hk)

end
end LeanVM.Guest.B1
