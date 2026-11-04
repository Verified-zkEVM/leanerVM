/-
  LeanVM.Guest.B1.Main.MainWalkChk

  `main`'s path, read off its blocks by kernel evaluation: its `HeapBuf`s, frames, loads.
-/

module

public import LeanVM.Guest.B1.Main.MainCChk
public import LeanVM.Guest.Memory.Uniform

/-!
# `main`'s path, checked

Every block of `main`'s body is straight (atoms, calls, conditional calls); the conditional calls
are the guarded loops; the blocks' `HeapBuf` hints, frames and loads are the listed ones.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest

@[expose] public section

/-- A statement of `main`'s blocks: an atom, a call, or a guarded loop on one of `cs`. -/
def mKind (cs : List ℕ) : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf c _ _ => decide (c = .n c.idx) && decide (c.idx ∈ cs)
  | _ => false

set_option maxRecDepth 100000 in
theorem mBlocks_straight : mPre.all Main.Stmt.straight = true ∧ mDa.all Main.Stmt.straight = true ∧
    mDaZ.all Main.Stmt.straight = true ∧ mMid.all Main.Stmt.straight = true ∧
    mLeaf.all Main.Stmt.straight = true ∧ mAgg.all Main.Stmt.straight = true ∧
    mPost.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_kind : mPre.all (mKind [61, 64, 377, 380]) = true ∧ mDa.all (mKind []) = true ∧
    mDaZ.all (mKind []) = true ∧ mMid.all (mKind [434]) = true ∧ mLeaf.all (mKind []) = true ∧
    mAgg.all (mKind []) = true ∧ mPost.all (mKind []) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_allocs : mPre.filterMap Main.Stmt.allocSz = [(.n 52, .inr (.n 51)),
      (.n 55, .inr (.n 54)), (.n 66, .inr (.n 42)), (.n 68, .inl 256),
      (.n 385, .inr (.n 384))] ∧ mDa.filterMap Main.Stmt.allocSz = [] ∧
    mDaZ.filterMap Main.Stmt.allocSz = [] ∧
    mMid.filterMap Main.Stmt.allocSz = [(.n 416, .inr (.n 415)), (.n 422, .inr (.n 421)),
      (.n 428, .inr (.n 427)), (.n 431, .inr (.n 430)), (.n 449, .inl 24)] ∧
    mLeaf.filterMap Main.Stmt.allocSz = [] ∧ mAgg.filterMap Main.Stmt.allocSz = [] ∧
    mPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_addrs : mPre.filterMap Main.Stmt.addrS = [] ∧ mDa.filterMap Main.Stmt.addrS = [] ∧
    mDaZ.filterMap Main.Stmt.addrS = [] ∧ mMid.filterMap Main.Stmt.addrS = [] ∧
    mLeaf.filterMap Main.Stmt.addrS = [] ∧ mAgg.filterMap Main.Stmt.addrS = [] ∧
    mPost.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPre_calls : mPre.filterMap Main.Stmt.callS =
    [(none, "exponent_tables", [], [.n 49]),
      (none, "claim_list_digest", [.n 52, .n 0], [.n 56, .n 57]),
      (none, "claim_list_digest", [.n 55, .n 3], [.n 58, .n 59]),
      (some (.n 61), "__loop0", [.n 62, .n 1, .n 52, .n 0], []),
      (some (.n 64), "__loop1", [.n 65, .n 4, .n 55, .n 3], []),
      (some (.n 377), "__loop2", [.n 378, .n 2, .n 40, .n 66, .n 52] ++ lxTagsV, []),
      (some (.n 380), "__loop3", [.n 381, .n 5, .n 41, .n 67, .n 2, .n 55, .n 68], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDa_calls : mDa.filterMap Main.Stmt.callS =
    [(none, "da_verify", [.n 49], [.n 390, .n 391, .n 392, .n 393])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDaZ_calls : mDaZ.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mMid_calls : mMid.filterMap Main.Stmt.callS =
    [(some (.n 434), "__loop4", [.n 435, .n 6, .n 431, .n 52, .n 66, .n 40, .n 55, .n 67, .n 41,
      .n 428, .n 385, .n 47, .n 48, .n 416, .n 49, .n 422], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeaf_calls : mLeaf.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_calls : mAgg.filterMap Main.Stmt.callS =
    [(none, "aggregate_claims", [.n 6, .n 416, .n 422, .n 428, .n 449], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPost_calls : mPost.filterMap Main.Stmt.callS =
    [(none, "statement_digest", [.n 47, .n 48, .n 56, .n 57, .n 58, .n 59, .n 476, .n 477, .n 449],
      [.n 478, .n 479])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_loads : mPre.filterMap B1.Stmt.loadS =
      (List.range 256).map (fun v => (.n 68, v)) ∧
    mDa.filterMap B1.Stmt.loadS = [(.n 387, 0), (.n 387, 1)] ∧
    mDaZ.filterMap B1.Stmt.loadS = [(.n 387, 0), (.n 387, 1)] ∧
    mMid.filterMap B1.Stmt.loadS = [(.n 431, 0), (.n 436, 0)] ∧
    mLeaf.filterMap B1.Stmt.loadS = (List.range 24).map (fun k => (.n 449, k)) ∧
    mAgg.filterMap B1.Stmt.loadS = [] ∧
    mPost.filterMap B1.Stmt.loadS = [(.n 448, 0), (.n 448, 1), (.n 480, 0), (.n 484, 0)] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_atoms : atomsIn mAgg = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem main_loop : coreProgram.loop "main" = false := by
  rw [Program.loop_of_find? find_main]; decide +kernel

end
end LeanVM.Guest.B1.Main
