/-
  LeanVM.Guest.B1.VerifySub.ExtractB

  `verify_sub`'s body as facts under any semantics of `BLAKE2S`: its relation is a valuation
  satisfying every statement before its final `ret`, and a run of statements free of `BLAKE2S`
  holds as deployed.
-/

module

public import LeanVM.Guest.B1.VerifySub.Extract

/-!
# Reading `verify_sub`'s body under any semantics

`Extract.lean` over `S : BlakeSem` (`CoreB.lean`): `verify_sub`'s relation `coreProgram.RelB S` is
a valuation satisfying `vsPre` under `S` (`VsHoldsB`, `verify_sub_holdsB`), and a run of its
statements holds under `S` (`VsHoldsB.slice`, `VsHoldsToB.slice'`).

A run of statements with no `BLAKE2S` atom, calling only the functions of `vsFree` (the
functions `verify_sub` calls that are free of `BLAKE2S`, closed under calls, `freeOn_vsFree` by
the kernel), holds as deployed (`VsHoldsB.sliceF`, `VsHoldsToB.sliceF'`, `atomF`, `callF`):
`Core.holdsListB_freeIn` carries it to the deployed semantics, where it is `Stmt.HoldsList` over
`coreProgram.Rel`. Every fact the deployed proof reads off such a run then carries over with
its proof unchanged; only the blocks that hash (`fs_next`, `squeeze`, the seed's compression)
and the calls that hash (`verify_bus_gkr`, `verify_tables`, `verify_flock`, `open_stacked`) are
read under `S` (`VsHoldsB.slice`, `call`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The functions free of `BLAKE2S` -/

/-- The functions `verify_sub` calls that are free of `BLAKE2S`, with every function they call. -/
def vsFree : List String :=
  ["log2_ceil_in_the_exponent__L15_L34", "verify_log2_ceil__L15_L34",
    "log2_ceil_in_the_exponent__L0_L34", "verify_log2_ceil__L0_L34", "g_power_of_word__L6",
    "check_opening_terminal", "rs_eq_run", "__loop8", "eq_prefix_chain", "__loop7",
    "column_selector__L0", "column_selector__L1", "column_selector__L2", "column_selector__L3",
    "column_selector__L4", "column_selector__L5", "column_selector__L6", "column_selector__L7",
    "column_selector__L8", "column_selector__L9", "column_selector__L10", "column_selector__L11",
    "column_selector__L12", "column_selector__L13", "column_selector__L14",
    "column_selector__L15", "column_selector__L16", "column_selector__L17",
    "column_selector__L18", "column_selector__L19", "column_selector__L20",
    "column_selector__L21", "column_selector__L22", "column_selector__L23",
    "column_selector__L24", "column_selector__L25", "column_selector__L26",
    "column_selector__L27", "column_selector__L28", "__loop83", "certify_placement",
    "assert_canonical", "__loop85", "__loop84"]

/-- `vsFree` is free of `BLAKE2S` and closed under calls. -/
theorem freeOn_vsFree : coreProgram.FreeOn vsFree = true := by decide +kernel

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-- **A function of `vsFree` under any semantics** is its deployed relation. -/
theorem relB_vsFree {f : String} (hf : f ∈ vsFree) (args rets : List E) :
    coreProgram.RelB S rd f args rets ↔ coreProgram.Rel rd f args rets :=
  relB_iff_rel_of_freeOn freeOn_vsFree hf args rets

/-- A run free of `BLAKE2S` over `vsFree` holds under `S` as deployed. -/
theorem holdsListB_vsFree {blk : List Stmt} (hf : Stmt.freeInList vsFree blk = true)
    {next : Prop} {kret : List E → Prop} :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk next kret ↔
      Stmt.HoldsList (coreProgram.Rel rd) rd σ blk next kret := by
  rw [holdsListB_freeIn (S' := blakeDeployed) (C' := coreProgram.RelB blakeDeployed rd)
    (fun f hf a r => relB_eq_of_freeOn freeOn_vsFree (List.contains_iff_mem.mp hf) a r) blk hf,
    holdsListB_deployed, relB_deployed]

/-! ## The body -/

variable (S) in
/-- The valuation `σ` satisfies every statement of `verify_sub` before its `ret`, under `S`. -/
def VsHoldsB (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ vsPre True fun rs => rs = []

theorem verify_sub_holdsB {args : List E} (h : coreProgram.RelB S rd "verify_sub" args []) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args ∧
      VsHoldsB S rd σ := by
  rw [relB_iff_sem find_verify_sub, core15_body, core15_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsListB_append, holdsListB_noRet _ vsPre_noRet] at hb
  exact ⟨σ, hp, hb.1⟩

/-- **A run of statements of the body holds** under `S`. -/
theorem VsHoldsB.slice (h : VsHoldsB S rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk True fun rs => rs = [] := by
  have hsplit : vsPre = vsPre.take n ++ (((vsPre.drop n).take blk.length) ++
      (vsPre.drop n).drop blk.length) := by simp
  have hnr := vsPre_noRet
  unfold VsHoldsB at h
  rw [hsplit] at h hnr
  rw [noRetList_append, noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsListB_append, holdsListB_noRet _ hnr.1, holdsListB_append,
    holdsListB_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

/-- One call of the body holds under `S`. -/
theorem VsHoldsB.call (h : VsHoldsB S rd σ) (n : ℕ) (f : String) (args rets : List V)
    (heq : stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) = true) :
    coreProgram.RelB S rd f (args.map σ) (rets.map σ) := by
  have := h.slice n [.call f args rets] heq
  simpa [Stmt.HoldsListB, Stmt.HoldsB] using this

/-- **A run free of `BLAKE2S` holds as deployed.** -/
theorem VsHoldsB.sliceF (h : VsHoldsB S rd σ) (n : ℕ) (blk : List Stmt)
    (heq : (stmtsEqb blk ((vsPre.drop n).take blk.length) && Stmt.freeInList vsFree blk) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun rs => rs = [] := by
  rw [Bool.and_eq_true] at heq
  exact (holdsListB_vsFree heq.2).mp (h.slice n blk heq.1)

/-- One atom of the body other than `BLAKE2S` holds as deployed. -/
theorem VsHoldsB.atomF (h : VsHoldsB S rd σ) (n : ℕ) (a : Atom)
    (heq : (stmtsEqb [.atom a] ((vsPre.drop n).take 1) && Stmt.freeInList vsFree [.atom a]) =
      true) : a.Holds rd σ := by
  have := h.sliceF n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of the body to a function of `vsFree` holds as deployed. -/
theorem VsHoldsB.callF (h : VsHoldsB S rd σ) (n : ℕ) (f : String) (args rets : List V)
    (heq : (stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) &&
      Stmt.freeInList vsFree [.call f args rets]) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  have := h.sliceF n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-! ## Prefixes of the body -/

variable (S) in
/-- The valuation `σ` satisfies the first `N` statements of `verify_sub`'s body, under `S`. -/
def VsHoldsToB (N : ℕ) (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ (vsPre.take N) True fun _ => True

theorem VsHoldsToB.mono {N M : ℕ} (h : VsHoldsToB S N rd σ) (hM : M ≤ N) :
    VsHoldsToB S M rd σ := by
  have hs : vsPre.take N = vsPre.take M ++ (vsPre.take N).drop M := by
    have := List.take_append_drop M (vsPre.take N)
    rw [List.take_take, Nat.min_eq_left hM] at this
    exact this.symm
  unfold VsHoldsToB at h
  rw [hs, holdsListB_append, holdsListB_noRet _ (noRetList_take M _ vsPre_noRet)] at h
  exact h.1

theorem VsHoldsB.to (h : VsHoldsB S rd σ) (N : ℕ) : VsHoldsToB S N rd σ := by
  have hs : vsPre = vsPre.take N ++ vsPre.drop N := (List.take_append_drop _ _).symm
  have hnr := vsPre_noRet
  unfold VsHoldsB at h
  rw [hs, holdsListB_append, holdsListB_noRet _ (noRetList_take N _ hnr)] at h
  exact holdsListB_mono (fun _ _ _ h => h) _ id (fun _ _ => trivial) h.1

/-- **A run of statements of a prefix holds** under `S`. -/
theorem VsHoldsToB.slice {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (blk : List Stmt)
    (hb : n + blk.length ≤ N) (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk True fun _ => True := by
  have h' := h.mono hb
  have hsplit : vsPre.take (n + blk.length) =
      vsPre.take n ++ (vsPre.drop n).take blk.length := by
    rw [List.take_add]
  have hnr := noRetList_take (n + blk.length) _ vsPre_noRet
  unfold VsHoldsToB at h'
  rw [hsplit] at h' hnr
  rw [noRetList_append, Bool.and_eq_true] at hnr
  rw [holdsListB_append, holdsListB_noRet _ hnr.1] at h'
  rw [stmtsEqb_sound heq]
  exact h'.2

/-- `slice` with the bound checked with the statements. -/
theorem VsHoldsToB.slice' {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (blk : List Stmt)
    (heq : (decide (n + blk.length ≤ N) && stmtsEqb blk ((vsPre.drop n).take blk.length)) = true) :
    Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ blk True fun _ => True := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at heq
  exact h.slice n blk heq.1 heq.2

/-- One call of a prefix holds under `S`, the bound checked with the statement. -/
theorem VsHoldsToB.call' {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (f : String)
    (args rets : List V)
    (heq : (decide (n + 1 ≤ N) && stmtsEqb [.call f args rets] ((vsPre.drop n).take 1)) = true) :
    coreProgram.RelB S rd f (args.map σ) (rets.map σ) := by
  have := h.slice' n [.call f args rets] heq
  simpa [Stmt.HoldsListB, Stmt.HoldsB] using this

/-- **A run of a prefix free of `BLAKE2S` holds as deployed**, the bound and the freedom checked
with the statements. -/
theorem VsHoldsToB.sliceF' {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (blk : List Stmt)
    (heq : (decide (n + blk.length ≤ N) && stmtsEqb blk ((vsPre.drop n).take blk.length) &&
      Stmt.freeInList vsFree blk) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun _ => True := by
  rw [Bool.and_eq_true] at heq
  exact (holdsListB_vsFree heq.2).mp (h.slice' n blk heq.1)

/-- One atom of a prefix other than `BLAKE2S` holds as deployed. -/
theorem VsHoldsToB.atomF' {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (a : Atom)
    (heq : (decide (n + 1 ≤ N) && stmtsEqb [.atom a] ((vsPre.drop n).take 1) &&
      Stmt.freeInList vsFree [.atom a]) = true) : a.Holds rd σ := by
  have := h.sliceF' n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of a prefix to a function of `vsFree` holds as deployed. -/
theorem VsHoldsToB.callF' {N : ℕ} (h : VsHoldsToB S N rd σ) (n : ℕ) (f : String)
    (args rets : List V)
    (heq : (decide (n + 1 ≤ N) && stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) &&
      Stmt.freeInList vsFree [.call f args rets]) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  have := h.sliceF' n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-! ## Below a call relation -/

variable (S) in
/-- The valuation `σ` satisfies every statement of `verify_sub` before its `ret`, under `S`,
its calls in `C`. -/
def VsHoldsCB (C : CallRel) (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsListB S C rd σ vsPre True fun rs => rs = []

theorem VsHoldsCB.rel {C : CallRel} (hC : CallRel.Le C (coreProgram.RelB S rd))
    (h : VsHoldsCB S C rd σ) : VsHoldsB S rd σ :=
  holdsListB_mono hC vsPre id (fun _ h => h) h

/-- A run of statements of the body holds under `S`, its calls in `C`. -/
theorem VsHoldsCB.slice {C : CallRel} (h : VsHoldsCB S C rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsListB S C rd σ blk True fun rs => rs = [] := by
  have hsplit : vsPre = vsPre.take n ++ (((vsPre.drop n).take blk.length) ++
      (vsPre.drop n).drop blk.length) := by simp
  have hnr := vsPre_noRet
  unfold VsHoldsCB at h
  rw [hsplit] at h hnr
  rw [noRetList_append, noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsListB_append, holdsListB_noRet _ hnr.1, holdsListB_append,
    holdsListB_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

end
end LeanVM.Guest.B1.VerifySub
