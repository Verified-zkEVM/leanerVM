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
    mMid.all Main.Stmt.straight = true ∧ mLeaf.all Main.Stmt.straight = true ∧
    mAgg.all Main.Stmt.straight = true ∧ mPost.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_kind : mPre.all (mKind [71, 86, 89, 357, 360]) = true ∧ mDa.all (mKind []) = true ∧
    mMid.all (mKind [393]) = true ∧ mLeaf.all (mKind []) = true ∧ mAgg.all (mKind []) = true ∧
    mPost.all (mKind []) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_allocs : mPre.filterMap Main.Stmt.allocSz = [(.n 69, .inr (.n 68)),
      (.n 77, .inr (.n 76)), (.n 80, .inr (.n 79)), (.n 97, .inr (.n 58)),
      (.n 99, .inl 256)] ∧ mDa.filterMap Main.Stmt.allocSz = [] ∧
    mMid.filterMap Main.Stmt.allocSz = [(.n 374, .inr (.n 373)), (.n 380, .inr (.n 379)),
      (.n 386, .inr (.n 385)), (.n 389, .inr (.n 388)), (.n 397, .inl 24)] ∧
    mLeaf.filterMap Main.Stmt.allocSz = [] ∧ mAgg.filterMap Main.Stmt.allocSz = [] ∧
    mPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_addrs : mPre.filterMap Main.Stmt.addrS = [] ∧ mDa.filterMap Main.Stmt.addrS = [] ∧
    mMid.filterMap Main.Stmt.addrS = [] ∧ mLeaf.filterMap Main.Stmt.addrS = [] ∧
    mAgg.filterMap Main.Stmt.addrS = [] ∧ mPost.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPre_calls : mPre.filterMap Main.Stmt.callS =
    [(none, "exponent_tables", [], [.n 65, .n 66]),
      (some (.n 71), "__loop0", [.n 72, .n 50, .n 69], []),
      (none, "da_list_digest", [.n 69, .n 40], [.n 73, .n 74]),
      (none, "claim_list_digest", [.n 77, .n 0], [.n 81, .n 82]),
      (none, "claim_list_digest", [.n 80, .n 3], [.n 83, .n 84]),
      (some (.n 86), "__loop0", [.n 87, .n 1, .n 77, .n 0], []),
      (some (.n 89), "__loop1", [.n 90, .n 4, .n 80, .n 3], []),
      (some (.n 357), "__loop2", [.n 358, .n 2, .n 55, .n 97, .n 77], []),
      (some (.n 360), "__loop3", [.n 361, .n 5, .n 56, .n 97, .n 55, .n 2, .n 80, .n 99], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mDa_calls : mDa.filterMap Main.Stmt.callS =
    [(none, "da_verify", [.n 66], [.n 364, .n 365, .n 366, .n 367]),
      (none, "cover_da_root", [.n 69, .n 98, .n 50, .n 368], [.n 369, .n 370, .n 371, .n 372])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mMid_calls : mMid.filterMap Main.Stmt.callS =
    [(some (.n 393), "__loop4", [.n 394, .n 6, .n 389, .n 77, .n 97, .n 55, .n 80, .n 56, .n 386, .n 69,
      .n 98, .n 50, .n 63, .n 64, .n 374, .n 65, .n 66, .n 380], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mLeaf_calls : mLeaf.filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_calls : mAgg.filterMap Main.Stmt.callS =
    [(none, "aggregate_claims", [.n 6, .n 374, .n 380, .n 386, .n 397], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mPost_calls : mPost.filterMap Main.Stmt.callS =
    [(none, "statement_digest", [.n 63, .n 64, .n 81, .n 82, .n 83, .n 84, .n 73, .n 74, .n 397],
      [.n 424, .n 425])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mBlocks_loads : mPre.filterMap B1.Stmt.loadS =
      (List.range 256).map (fun v => (.n 99, v)) ∧
    mDa.filterMap B1.Stmt.loadS = [] ∧
    mMid.filterMap B1.Stmt.loadS = [(.n 389, 0), (.n 395, 0)] ∧
    mLeaf.filterMap B1.Stmt.loadS = (List.range 24).map (fun k => (.n 397, k)) ∧
    mAgg.filterMap B1.Stmt.loadS = [] ∧
    mPost.filterMap B1.Stmt.loadS = [(.n 426, 0), (.n 430, 0)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem mAgg_atoms : atomsIn mAgg = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem main_loop : coreProgram.loop "main" = false := by
  rw [Program.loop_of_find? find_main]; decide +kernel

end
end LeanVM.Guest.B1.Main
