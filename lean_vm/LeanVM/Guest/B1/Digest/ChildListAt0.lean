/-
  LeanVM.Guest.B1.Digest.ChildListAt0

  `child_claim_list_digest`'s path and valuations, and its callees `child_claim_list_last__L{k}`
  and `__loop16` in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCore
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.B1.Digest.LoopAt

/-!
# A child's claim list, the parts

* The path: a branch on `n = 0` between straight runs (`cc_body`), the nonempty arm a straight run,
  the dispatch on `r`, two copies (`cc24Else_split`).
* `ccz_core`, `cc_core`: the empty and the nonempty list's evaluated valuations (as
  `claim_list_digest`'s, `cl_core`).
* `ccl_completeAt`: `child_claim_list_last__L{k}` is `CompleteAtD` (`relAtIn_atoms` on `ccl_core`),
  reading the state's words, the records' marks and cells among the caller's words, its range
  checks below `2^κ`, `L ≤ 2^κ`.
* `l17_completeAt`: `__loop16` is `CompleteAtD` from the first group (`loopA_completeAt` on
  `l17_core`), reading the chain buffer's states and the records.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (relAtIn_atoms)

@[expose] public section

/-! ## The path -/

/-- The nonempty arm before its dispatch. -/
noncomputable def ccP1 : List Stmt := cc24Else.take 51

/-- The nonempty arm after its dispatch. -/
noncomputable def ccPost : List Stmt := cc24Else.drop 52

set_option maxRecDepth 100000 in
theorem cc24Else_split : cc24Else = ccP1 ++
    .dispatch (.n 28) cclNames [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4] [.n 65, .n 66] :: ccPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem ccPost_eq : ccPost = [.atom (.copy (.n 14) (.n 65)), .atom (.copy (.n 15) (.n 66))] :=
  stmtsEqb_sound (by decide +kernel)

theorem cc_body : Fn.body Data.core24 =
    ccHead ++ .ite (.n 7) cc24Zero cc24Else :: (ccTail ++ [.ret [.n 67, .n 68]]) := by
  rw [core24_shape]; rfl

set_option maxRecDepth 100000 in
theorem ccP1_straight : ccP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc24Zero_straight : cc24Zero.all Main.Stmt.straight = true := by decide +kernel

theorem ccHead_straight : ccHead.all Main.Stmt.straight = true := rfl
theorem ccTail_straight : ccTail.all Main.Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem ccP1_allocs : ccP1.filterMap Main.Stmt.allocSz = [(.n 36, .inr (.n 35))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccP1_addrs : ccP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccP1_calls : ccP1.filterMap Main.Stmt.callS =
    [(none, "list_split", [.n 5], [.n 27, .n 28]),
      (some (.n 51), "__loop16", [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccP1_loads : ccP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n 36, c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cc24Zero_parts : cc24Zero.filterMap Main.Stmt.allocSz = [] ∧
    cc24Zero.filterMap Main.Stmt.addrS = [] ∧ cc24Zero.filterMap Main.Stmt.callS = [] ∧
    cc24Zero.filterMap B1.Stmt.loadS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc_loop : coreProgram.loop "child_claim_list_digest" = false := by
  rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel

theorem ccElsePre_eq : ccElsePre = ccP1 ++
    [.dispatch (.n 28) cclNames [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4] [.n 65, .n 66]] := by
  rw [ccElsePre, cc24Else_split, ccPost_eq]; simp

set_option maxRecDepth 100000 in
theorem ccP1_kinds : ccP1.all (fun s => isAtomS s ||
    stmtEqb s (.call "list_split" [.n 5] [.n 27, .n 28]) ||
    stmtEqb s (.callIf (.n 51) "__loop16" [.n 52, .n 27, .n 36, .n 0, .n 1, .n 2, .n 3, .n 4])) =
      true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc24Zero_atoms : cc24Zero.all isAtomS = true := by decide +kernel

theorem cclNames_get {r : ℕ} (hr : r < 17) : cclNames[r]! = cclNames.getD r "" := by
  have h : r < cclNames.length := by simp [cclNames]; omega
  rw [getElem!_pos cclNames r h, List.getD_eq_getElem _ _ h]

/-! ## The valuations -/

/-- The empty list's valuation. -/
noncomputable def cczσ (rd : Reader) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) args ccZEval)

/-- The oracle of the nonempty list's valuation. -/
noncomputable def ccw (m r : ℕ) (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = 27 then gen ^ m else if i = 28 then gen ^ r else if i = 36 then chain
  else if i = 14 ∨ i = 65 then (digestScalars D).1 else if i = 15 ∨ i = 66 then (digestScalars D).2
  else 0

/-- The nonempty list's valuation. -/
noncomputable def ccσ (rd : Reader) (args : List E) (n : ℕ) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (ccw (n / 17) (n % 17) chain D) args ccEEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem ccz_core (entries cover base origin limit : E) :
    let σ := cczσ rd [entries, cover, base, origin, limit, gen ^ 0]
    (∀ a ∈ atomsIn ccZEval, a.Holds rd σ) ∧
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] =
        [entries, cover, base, origin, limit, gen ^ 0] ∧ σ (.n 7) = 0 ∧
      σ (.n 7) = gen ^ 0 + gen ^ 0 ∧
      [σ (.n 67), σ (.n 68)] = digestCells (keccak256 (cellsBytes [])) := by
  intro σ
  have hz1 := ccz_ok
  have hb1 := ccbr_ok
  simp only [ccZOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ccBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz14⟩, hz15⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, b12⟩, b13⟩, b14⟩, b15⟩, -⟩ := hb1
  have c6 : Stmt.atom (.const (.n 6) (word 1 0 0)) ∈ ccHead := by simp [ccHead]
  have a7 : Stmt.atom (.add (.n 7) (.n 5) (.n 6)) ∈ ccHead := by simp [ccHead]
  have t67 : Stmt.atom (.copy (.n 67) (.n 14)) ∈ ccTail := by simp [ccTail]
  have t68 : Stmt.atom (.copy (.n 68) (.n 15)) ∈ ccTail := by simp [ccTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, cover, base, origin, limit, gen ^ 0]
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) ccZEval args hchk
  rw [show args.length = 6 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn ccZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have hns : ∀ a ∈ atomsIn ccZEval, needsSide a = false := by
    intro a ha
    have := List.all_eq_true.mp b15 a ha
    simpa using this
  have hat : ∀ a ∈ atomsIn ccZEval, a.Holds rd σ :=
    atoms_holds hidx b14 hg (A := []) (by simp) fun a ha hn => absurd hn (by simp [hns a ha])
  have mH : ∀ s ∈ ccHead, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mZ : ∀ s ∈ cc24Zero, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mT : ∀ s ∈ ccTail, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cc24Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have v6 : σ (.n 6) = word 1 0 0 := hat _ (cl_mem_atoms (mH _ c6))
  have v7 : σ (.n 7) = σ (.n 5) + σ (.n 6) := hat _ (cl_mem_atoms (mH _ a7))
  have v67 : σ (.n 67) = σ (.n 14) := hat _ (cl_mem_atoms (mT _ t67))
  have v68 : σ (.n 68) = σ (.n 15) := hat _ (cl_mem_atoms (mT _ t68))
  have v7' : σ (.n 7) = gen ^ 0 + gen ^ 0 := by
    rw [v7, v6, par 5 (by omega), word_one, pow_zero]; rfl
  have h70 : σ (.n 7) = 0 := by rw [v7']; exact e_add_eq_zero_iff.mpr rfl
  obtain ⟨hd, -⟩ := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz14, hz15, show List.take (ccZSpec.len / 16) (ccZSpec.vals σ) = [] by simp [ccZSpec],
    List.nil_append] at hd
  refine ⟨hat, ?_, h70, v7', ?_⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega)]
    rfl
  · rw [v67, v68, digestCells, ← hd]

/-- **What the nonempty list's valuation is.** -/
structure CcVals (rd : Reader) (σ : Val) (args : List E) (n : ℕ) (chain : E) (D : Digest) : Prop where
  atoms : ∀ a ∈ atomsIn ccEEval, a.Holds rd σ
  par : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] = args
  v5 : σ (.n 5) = gen ^ n
  v7 : σ (.n 7) = gen ^ n + gen ^ 0
  v14 : σ (.n 14) = (digestScalars D).1
  v15 : σ (.n 15) = (digestScalars D).2
  v27 : σ (.n 27) = gen ^ (n / 17)
  v28 : σ (.n 28) = gen ^ (n % 17)
  v35 : σ (.n 35) = gen ^ (13 * (n / 17 + 1))
  v36 : σ (.n 36) = chain
  v51 : σ (.n 51) = 1 + gen ^ (n / 17)
  v52 : σ (.n 52) = 1
  v58 : σ (.n 58) = chain * gen ^ (13 * (n / 17))
  v64 : σ (.n 64) = σ (.n 2) * gen ^ (17 * (n / 17))
  v65 : σ (.n 65) = (digestScalars D).1
  v66 : σ (.n 66) = (digestScalars D).2
  v67 : σ (.n 67) = (digestScalars D).1
  v68 : σ (.n 68) = (digestScalars D).2

set_option maxRecDepth 100000 in
theorem cc_size_atoms : ∀ a ∈ [Atom.const (.n 29) (word 2 0 0), .mul (.n 30) (.n 27) (.n 29),
    .mul (.n 31) (.n 30) (.n 30), .mul (.n 32) (.n 31) (.n 30), .mul (.n 33) (.n 32) (.n 32),
    .mul (.n 34) (.n 33) (.n 33), .mul (.n 35) (.n 34) (.n 30)], a ∈ atomsIn ccEEval := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **The nonempty list's valuation**: on a memory holding the zero state at the chain buffer. -/
theorem cc_core {entries cover base origin limit chain : E} {n : ℕ} (D : Digest)
    (hz0 : StateAt rd chain 0 zeroState) :
    CcVals rd (ccσ rd [entries, cover, base, origin, limit, gen ^ n] n chain D)
      [entries, cover, base, origin, limit, gen ^ n] n chain D := by
  have he1 := cce_ok
  have hb1 := ccbr_ok
  simp only [ccEOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [ccBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h52⟩, h51⟩, h50⟩, -⟩, hm58⟩, hm64⟩, -⟩, -⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, -⟩, b7⟩, -⟩, b9⟩, b10⟩, b11⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hb1
  have hE := stmtsEqb_sound b1
  have c6 : Stmt.atom (.const (.n 6) (word 1 0 0)) ∈ ccHead := by simp [ccHead]
  have a7 : Stmt.atom (.add (.n 7) (.n 5) (.n 6)) ∈ ccHead := by simp [ccHead]
  have t67 : Stmt.atom (.copy (.n 67) (.n 14)) ∈ ccTail := by simp [ccTail]
  have t68 : Stmt.atom (.copy (.n 68) (.n 15)) ∈ ccTail := by simp [ccTail]
  set m := n / 17 with hmdef
  set r := n % 17 with hrdef
  set w := ccw m r chain D with hw
  have w27 : w 27 = gen ^ m := by rw [hw]; simp [ccw]
  have w28 : w 28 = gen ^ r := by rw [hw]; simp [ccw]
  have w36 : w 36 = chain := by rw [hw]; simp [ccw]
  have w14 : w 14 = (digestScalars D).1 := by rw [hw]; simp [ccw]
  have w65 : w 65 = (digestScalars D).1 := by rw [hw]; simp [ccw]
  have w15 : w 15 = (digestScalars D).2 := by rw [hw]; simp [ccw]
  have w66 : w 66 = (digestScalars D).2 := by rw [hw]; simp [ccw]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
  let args : List E := [entries, cover, base, origin, limit, gen ^ n]
  set σ := ccσ rd args n chain D with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w ccEEval args hchk
  rw [show args.length = 6 from rfl] at hgs
  set SE := storesOf 6 ccEEval with hSE
  have hg : ∀ a ∈ atomsIn ccEEval, Good rd SE w σ a := fun a ha => hgs _ (cl_atom_mem ha)
  have mH : ∀ s ∈ ccHead, s ∈ ccEEval := fun s hs => by unfold ccEEval; simp [hs]
  have mP : ∀ s ∈ ccElsePre, s ∈ ccEEval := fun s hs => by unfold ccEEval; simp [hs]
  have mT : ∀ s ∈ ccTail, s ∈ ccEEval := fun s hs => by unfold ccEEval; simp [hs]
  have mF : ∀ i < 19, Stmt.atom (.hint (.alloc (.n (8 + i)) 0)) ∈ ccEEval := fun i hi => by
    unfold ccEEval
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))
  have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = entries := par 0 (by omega)
  have e2 : σ (.n 2) = base := par 2 (by omega)
  have e5 : σ (.n 5) = gen ^ n := par 5 (by omega)
  have v36 : σ (.n 36) = chain := by
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp b11
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a with
    | hint h =>
      cases h with
      | allocDyn d s =>
        simp only [decide_eq_true_eq] at hp
        subst hp
        have hga' : σ (.n 36) = w 36 := hga
        rw [hga', w36]
      | _ => simp at hp
    | _ => simp at hp
  have v37 : ∀ c < 13, σ (.n (37 + c)) = 0 := by
    intro c hc'
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp b10 c (List.mem_range.mpr hc'))
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hga' : σ (.n (37 + c)) = _ := hga
    rw [hga', eEqb_sound he, word_zero]
  have hat : ∀ a ∈ atomsIn ccEEval, a.Holds rd σ := by
    refine atoms_holds_stores (S := SE) (w := w) hidx b5 hg (A := []) (by simp)
      (fun a ha hnS hns => ?_) (fun _ a ha haS => ?_)
    · have := List.all_eq_true.mp b4 a ha
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
    · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp b3 a haS)
      rw [atomEqb_sound he]
      have hc13 := List.mem_range.mp hc'
      show LoadHolds rd (σ (.n 36)) c (σ (.n (37 + c)))
      rw [v36, v37 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have hdisp : Stmt.dispatch (.n 28) cclNames [.n 58, .n 0, .n 1, .n 64, .n 3, .n 4]
      [.n 65, .n 66] ∈ ccElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b9; rwa [stmtEqb_sound he] at hs
  have hcall : Stmt.call "list_split" [.n 5] [.n 27, .n 28] ∈ ccElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b7; rwa [stmtEqb_sound he] at hs
  have gd : ∀ v ∈ [V.n 65, V.n 66], σ v = w v.idx := hgs _ (mP _ hdisp)
  have gc : ∀ v ∈ [V.n 27, V.n 28], σ v = w v.idx := hgs _ (mP _ hcall)
  have v65 : σ (.n 65) = (digestScalars D).1 := (gd _ (by simp)).trans w65
  have v66 : σ (.n 66) = (digestScalars D).2 := (gd _ (by simp)).trans w66
  have v27 : σ (.n 27) = gen ^ m := (gc _ (by simp)).trans w27
  have v28 : σ (.n 28) = gen ^ r := (gc _ (by simp)).trans w28
  have v14 : σ (.n 14) = (digestScalars D).1 := by
    have : σ (.n 14) = w 14 := hgs _ (mF 6 (by omega))
    rw [this, w14]
  have v15 : σ (.n 15) = (digestScalars D).2 := by
    have : σ (.n 15) = w 15 := hgs _ (mF 7 (by omega))
    rw [this, w15]
  have hatElse : ∀ a ∈ atomsIn cc24Else, a.Holds rd σ := by
    intro a ha
    have hs := cl_atom_mem ha
    rw [hE] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hat a (cl_mem_atoms (mP _ hs))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl
      · show σ (.n 14) = σ (.n 65); rw [v14, v65]
      · show σ (.n 15) = σ (.n 66); rw [v15, v66]
  have v52 : σ (.n 52) = 1 := by rw [const_sound h52 hatElse, word_one]
  have v51 : σ (.n 51) = 1 + gen ^ m := by
    rw [add_sound h51 hatElse, const_sound h50 hatElse, word_one, v27]
  have v58 : σ (.n 58) = chain * gen ^ (13 * m) := by
    rw [monoIs_sound hm58 hatElse, v36, v27, gen_pow_pow]
  have v64 : σ (.n 64) = σ (.n 2) * gen ^ (17 * m) := by
    rw [monoIs_sound hm64 hatElse, v27, gen_pow_pow]
  have v6 : σ (.n 6) = word 1 0 0 := hat _ (cl_mem_atoms (mH _ c6))
  have v7 : σ (.n 7) = σ (.n 5) + σ (.n 6) := hat _ (cl_mem_atoms (mH _ a7))
  have v67 : σ (.n 67) = σ (.n 14) := hat _ (cl_mem_atoms (mT _ t67))
  have v68 : σ (.n 68) = σ (.n 15) := hat _ (cl_mem_atoms (mT _ t68))
  have hs := cc_size_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s29, s30, s31, s32, s33, s34, s35⟩ := hs
  have q29 : σ (.n 29) = word 2 0 0 := hat _ s29
  have q30 : σ (.n 30) = σ (.n 27) * σ (.n 29) := hat _ s30
  have q31 : σ (.n 31) = σ (.n 30) * σ (.n 30) := hat _ s31
  have q32 : σ (.n 32) = σ (.n 31) * σ (.n 30) := hat _ s32
  have q33 : σ (.n 33) = σ (.n 32) * σ (.n 32) := hat _ s33
  have q34 : σ (.n 34) = σ (.n 33) * σ (.n 33) := hat _ s34
  have q35 : σ (.n 35) = σ (.n 34) * σ (.n 30) := hat _ s35
  refine ⟨hat, ?_, e5, by rw [v7, v6, e5, word_one, pow_zero], v14, v15, v27, v28, ?_, v36,
    v51, v52, v58, v64, v65, v66, by rw [v67, v14], by rw [v68, v15]⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega)]
    rfl
  · rw [q35, q34, q33, q32, q31, q30, q29, v27, word_gen]
    ring

/-! ## The callees -/

theorem boundMem_of_low {κ : ℕ} (hl : LowDef κ rd) {L : ℕ} (hL : L ≤ 2 ^ κ) : BoundMem rd L :=
  fun i hi => ⟨_, by rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl (by omega)⟩

/-- **`child_claim_list_last__L{k}` is complete, placed**: the state at `sp = g^sP`, the records'
marks and cells among the caller's words. -/
theorem ccl_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {sp entries cover marks origin limit : E} {sP eP cv og L n : ℕ}
    {pre : List UInt8} {os : ℕ → ℕ} {cells : List E}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hcv : cover = gen ^ cv) (hog : origin = gen ^ og)
    (hL : limit = gen ^ L) (hpre : pre.length = rate * n) (hl : cells.length = 4 * k)
    (hc : AllCanonical cells) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → StateAt rd sp 0 (absorbChunks n zeroState pre) ∧
      RecMem rd cover origin limit entries marks k os cells)
    (hR1 : ∀ o < 13, RegionL Lin (sP + o)) (hR2 : ∀ j < k, RegionL Lin (cv + og + os j))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * os j + c)) :
    CompleteAtD fs cert κ (cclNames.getD k "") Lin [sp, entries, cover, marks, origin, limit]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells)))) := by
  intro fp
  refine ⟨fs (cclNames.getD k ""), [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
    fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hS, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload⟩ := ccl_core hk hsp hen hcv hog hpre hS hl hc hrec hL hL33
    (boundMem_of_low hlow hLκ)
  refine relAtIn_atoms (ccl_name hk) hb (ccl_loop hk) (ccl_na hk) hp hat hr
    (fun q hq => by rw [ccl_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  rcases hload q hq with ⟨o, ho, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, Or.inl (hR1 o ho)⟩
  · exact ⟨_, h, Or.inl (hR2 j hj)⟩
  · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩

set_option maxRecDepth 100000 in
theorem l17_atomsS : (loopPre (coreProgram.getD 338 default)).all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_unplaced :
    (atomsIn (loopPre (coreProgram.getD 338 default))).all atomUnplaced = true := by decide +kernel

/-- **`__loop16` is complete, placed**: the chain buffer's states at `g^chP` and the records'
marks and cells among the caller's words, the groups `j < m`. -/
theorem l17_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lin : Main.Layout}
    {chain entries cover base origin limit : E} {chP eP cv og L m : ℕ} {o : ℕ → ℕ}
    {cells : List E} (hch : chain = gen ^ chP) (hen : entries = gen ^ eP)
    (hcv : cover = gen ^ cv) (hog : origin = gen ^ og) (hL : limit = gen ^ L)
    (hl : 68 * m ≤ cells.length) (hc : AllCanonical cells) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hm : m < 2 ^ 34) (hm0 : 0 < m)
    (hmem : ∀ rd, MemL rd Lin → (∀ q ≤ m, StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q))))) ∧
      RecMem rd cover origin limit entries base (17 * m) o cells)
    (hR1 : ∀ j < m, ∀ c < 26, RegionL Lin (chP + 13 * j + c))
    (hR2 : ∀ j < 17 * m, RegionL Lin (cv + og + o j))
    (hR3 : ∀ j < 17 * m, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtD fs cert κ "__loop16" Lin
      [1, gen ^ m, chain, entries, cover, base, origin, limit] (Returns []) := by
  have h := loopA_completeAt fs cert (find_of_idx l17_idx (by rw [coreProgram_length]; omega))
    l17_shapeF l17_atomsS l17_unplaced (Lin := Lin) (κ := κ) (N := gen ^ m)
    (rest := [chain, entries, cover, base, origin, limit]) (m := m) rfl hm ?_
  · have := h 0 hm0
    rwa [pow_zero] at this
  intro jj hjj rd hlow hLin
  obtain ⟨hS, hrec⟩ := hmem rd hLin
  have hpre : (cellsBytes (cells.take (68 * jj))).length = rate * (8 * jj) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * jj) = 136 * (8 * jj); omega
  have hS0 := hS jj (by omega)
  have hS1 := hS (jj + 1) (by omega)
  rw [show 68 * (jj + 1) = 68 * jj + 68 by ring, List.take_add, cellsBytes_append] at hS1
  have hr := recMem_group hrec (s := 17 * jj) (k := 17) (by omega)
  rw [show 4 * (17 * jj) = 68 * jj by ring, show 4 * 17 = 68 by rfl, mul_comm 17 jj, pow_mul] at hr
  obtain ⟨σ, hp, hat, hload⟩ := l17_core (x := gen ^ jj) (N := gen ^ m) rfl hch hen hcv hog hpre
    (by rw [gen_pow_pow]; exact hS0) (cells := ((cells.drop (68 * jj)).take 68)) (by simp; omega)
    (canon_take (canon_drop hc _) _) hr hL hL33 (boundMem_of_low hlow hLκ) (fun c => by
      have := hS1 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow]
      rw [loadHolds_mul_gen_pow, show 13 * (jj + 1) + (0 + c.val) = 13 * jj + (13 + c.val) by ring,
        show 8 * (jj + 1) = 8 * jj + 8 by ring] at this
      exact this)
  refine ⟨σ, hp, hat, fun q hq => ?_⟩
  rcases hload q hq with ⟨c, hc26, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, hR1 jj hjj c hc26⟩
  · exact ⟨_, h, by have := hR2 (17 * jj + j) (by omega); rwa [mul_comm 17 jj] at this⟩
  · exact ⟨_, h, by have := hR3 (17 * jj + j) (by omega) c hc4; rwa [mul_comm 17 jj] at this⟩

end
end LeanVM.Guest.B1.Digest
