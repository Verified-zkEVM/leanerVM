/-
  LeanVM.Guest.B1.Digest.ClaimListAt

  `claim_list_digest` in the uniform placed form: its chain buffer after its frame, holding the
  sponge states an honest run leaves, its callees after it; it reads the claims among its caller's
  words.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.PlacedLib

/-!
# `claim_list_digest`, placed

The body is a branch on `n = 0` between two straight runs (`cl_body`). The empty list's arm is
atoms (`clz_core`: the evaluated valuation, its atoms holding). The nonempty list's arm
(`cl23Else_split`) calls `list_split`, allocates the chain buffer (`13 (m + 1)` words for
`n = 17 m + r`), stores the zero state, runs `__loop15` over the groups when `m ≠ 0`, and
dispatches on `r` to `claim_list_last__L{r}` (`cl_core`: the evaluated valuation, its atoms holding
on a memory holding the zero state at the buffer). `chainCells`: the buffer's honest words, the
state after each group (`claimChainMem_of_reads`).

`claim_list_digest_completeAt`: for `n < 17 · 2^16` canonical claims' cells at `g^eP` among the
caller's words `Lin`, `claim_list_digest` is `CompleteAtD` returning their digest's cells.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD Returns Kid DisjL Within disj_append kidsFromIn_of_kidsD
  completeAt_of_rel_pureD regionsOk_of within_append bufL bufL_within bufL_disj bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)

@[expose] public section

/-! ## The path -/

/-- The nonempty arm before its dispatch. -/
noncomputable def clP1 : List Stmt := cl23Else.take 53

/-- The nonempty arm after its dispatch. -/
noncomputable def clPost : List Stmt := cl23Else.drop 54

set_option maxRecDepth 100000 in
theorem cl23Else_split :
    cl23Else = clP1 ++ .dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64] :: clPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem clPost_eq : clPost = [.atom (.copy (.n 10) (.n 63)), .atom (.copy (.n 11) (.n 64))] :=
  stmtsEqb_sound (by decide +kernel)

theorem cl_body : Fn.body Data.core23 =
    clHead ++ .ite (.n 3) cl23Zero cl23Else :: (clTail ++ [.ret [.n 65, .n 66]]) := by
  rw [core23_shape]; rfl

set_option maxRecDepth 100000 in
theorem clP1_straight : clP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_straight : cl23Zero.all Main.Stmt.straight = true := by decide +kernel

theorem clHead_straight : clHead.all Main.Stmt.straight = true := rfl
theorem clTail_straight : clTail.all Main.Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem clP1_allocs : clP1.filterMap Main.Stmt.allocSz = [(.n 32, .inr (.n 31))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_addrs : clP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_calls : clP1.filterMap Main.Stmt.callS =
    [(none, "list_split", [.n 1], [.n 23, .n 24]),
      (some (.n 47), "__loop15", [.n 48, .n 23, .n 32, .n 0], [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_loads : clP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n 32, c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_parts : cl23Zero.filterMap Main.Stmt.allocSz = [] ∧
    cl23Zero.filterMap Main.Stmt.addrS = [] ∧ cl23Zero.filterMap Main.Stmt.callS = [] ∧
    cl23Zero.filterMap B1.Stmt.loadS = [] := by decide +kernel

theorem cl_loop : coreProgram.loop "claim_list_digest" = false := by
  rw [Program.loop_of_find? find_claim_list_digest]; decide +kernel

/-! ## The valuations -/

/-- The empty list's valuation. -/
noncomputable def clzσ (rd : Reader) (entries : E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) [entries, gen ^ 0] clZEval)

/-- The oracle of the nonempty list's valuation. -/
noncomputable def clw (m r : ℕ) (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = 23 then gen ^ m else if i = 24 then gen ^ r else if i = 32 then chain
  else if i = 10 ∨ i = 63 then (digestScalars D).1 else if i = 11 ∨ i = 64 then (digestScalars D).2
  else 0

/-- The nonempty list's valuation. -/
noncomputable def clσ (rd : Reader) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (clw (n / 17) (n % 17) chain D) [entries, gen ^ n] clEEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem clz_core (entries : E) :
    (∀ a ∈ atomsIn clZEval, a.Holds rd (clzσ rd entries)) ∧ clzσ rd entries (.n 0) = entries ∧
      clzσ rd entries (.n 1) = gen ^ 0 ∧ clzσ rd entries (.n 3) = 0 ∧
      clzσ rd entries (.n 3) = gen ^ 0 + gen ^ 0 ∧
      [clzσ rd entries (.n 65), clzσ rd entries (.n 66)] =
        digestCells (keccak256 (cellsBytes [])) := by
  have hz1 := cz_ok
  have hb1 := clbr_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, b12⟩, b13⟩, b14⟩, b15⟩, -⟩ := hb1
  have c2 : Stmt.atom (.const (.n 2) (word 1 0 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n 3) (.n 1) (.n 2)) ∈ clHead := by simp [clHead]
  have t65 : Stmt.atom (.copy (.n 65) (.n 10)) ∈ clTail := by simp [clTail]
  have t66 : Stmt.atom (.copy (.n 66) (.n 11)) ∈ clTail := by simp [clTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, gen ^ 0]
  set σ := clzσ rd entries with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) clZEval args hchk
  rw [show args.length = 2 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn clZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have hns : ∀ a ∈ atomsIn clZEval, needsSide a = false := by
    intro a ha
    have := List.all_eq_true.mp b15 a ha
    simpa using this
  have hat : ∀ a ∈ atomsIn clZEval, a.Holds rd σ :=
    atoms_holds hidx b14 hg (A := []) (by simp) fun a ha hn => absurd hn (by simp [hns a ha])
  have mH : ∀ s ∈ clHead, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mZ : ∀ s ∈ cl23Zero, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mT : ∀ s ∈ clTail, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cl23Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have e0 : σ (.n 0) = entries := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have e1 : σ (.n 1) = gen ^ 0 := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have v2 : σ (.n 2) = word 1 0 0 := hat _ (cl_mem_atoms (mH _ c2))
  have v3 : σ (.n 3) = σ (.n 1) + σ (.n 2) := hat _ (cl_mem_atoms (mH _ a3))
  have v65 : σ (.n 65) = σ (.n 10) := hat _ (cl_mem_atoms (mT _ t65))
  have v66 : σ (.n 66) = σ (.n 11) := hat _ (cl_mem_atoms (mT _ t66))
  have h30 : σ (.n 3) = 0 := by
    rw [v3, v2, e1, word_one, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
  obtain ⟨hd, -⟩ := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
    List.nil_append] at hd
  refine ⟨hat, e0, e1, h30, by rw [v3, v2, e1, word_one, pow_zero], ?_⟩
  rw [v65, v66, digestCells, ← hd]

/-- **What the nonempty list's valuation is.** -/
structure ClVals (rd : Reader) (σ : Val) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Prop where
  atoms : ∀ a ∈ atomsIn clEEval, a.Holds rd σ
  v0 : σ (.n 0) = entries
  v1 : σ (.n 1) = gen ^ n
  v3 : σ (.n 3) = gen ^ n + gen ^ 0
  v10 : σ (.n 10) = (digestScalars D).1
  v11 : σ (.n 11) = (digestScalars D).2
  v23 : σ (.n 23) = gen ^ (n / 17)
  v24 : σ (.n 24) = gen ^ (n % 17)
  v31 : σ (.n 31) = gen ^ (13 * (n / 17 + 1))
  v32 : σ (.n 32) = chain
  v47 : σ (.n 47) = 1 + gen ^ (n / 17)
  v48 : σ (.n 48) = 1
  v54 : σ (.n 54) = chain * gen ^ (13 * (n / 17))
  v62 : σ (.n 62) = entries * gen ^ (68 * (n / 17))
  v63 : σ (.n 63) = (digestScalars D).1
  v64 : σ (.n 64) = (digestScalars D).2
  v65 : σ (.n 65) = (digestScalars D).1
  v66 : σ (.n 66) = (digestScalars D).2

set_option maxRecDepth 100000 in
theorem cl_size_atoms : ∀ a ∈ [Atom.const (.n 25) (word 2 0 0), .mul (.n 26) (.n 23) (.n 25),
    .mul (.n 27) (.n 26) (.n 26), .mul (.n 28) (.n 27) (.n 26), .mul (.n 29) (.n 28) (.n 28),
    .mul (.n 30) (.n 29) (.n 29), .mul (.n 31) (.n 30) (.n 26)], a ∈ atomsIn clEEval := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The nonempty list's valuation**: on a memory holding the zero state at the chain buffer. -/
theorem cl_core {entries chain : E} {n : ℕ} (D : Digest) (hz0 : StateAt rd chain 0 zeroState) :
    ClVals rd (clσ rd entries n chain D) entries n chain D := by
  have he1 := ce_ok
  have hb1 := clbr_ok
  simp only [ceOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h48⟩, h47⟩, h46⟩, -⟩, hm54⟩, hm62⟩, -⟩, -⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, -⟩, b7⟩, -⟩, b9⟩, b10⟩, b11⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hb1
  have hE := stmtsEqb_sound b1
  have c2 : Stmt.atom (.const (.n 2) (word 1 0 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n 3) (.n 1) (.n 2)) ∈ clHead := by simp [clHead]
  have t65 : Stmt.atom (.copy (.n 65) (.n 10)) ∈ clTail := by simp [clTail]
  have t66 : Stmt.atom (.copy (.n 66) (.n 11)) ∈ clTail := by simp [clTail]
  set m := n / 17 with hmdef
  set r := n % 17 with hrdef
  set w := clw m r chain D with hw
  have w23 : w 23 = gen ^ m := by rw [hw]; simp [clw]
  have w24 : w 24 = gen ^ r := by rw [hw]; simp [clw]
  have w32 : w 32 = chain := by rw [hw]; simp [clw]
  have w10 : w 10 = (digestScalars D).1 := by rw [hw]; simp [clw]
  have w63 : w 63 = (digestScalars D).1 := by rw [hw]; simp [clw]
  have w11 : w 11 = (digestScalars D).2 := by rw [hw]; simp [clw]
  have w64 : w 64 = (digestScalars D).2 := by rw [hw]; simp [clw]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
  let args : List E := [entries, gen ^ n]
  set σ := clσ rd entries n chain D with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w clEEval args hchk
  rw [show args.length = 2 from rfl] at hgs
  set SE := storesOf 2 clEEval with hSE
  have hg : ∀ a ∈ atomsIn clEEval, Good rd SE w σ a := fun a ha => hgs _ (cl_atom_mem ha)
  have mH : ∀ s ∈ clHead, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mP : ∀ s ∈ clElsePre, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mT : ∀ s ∈ clTail, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mF : ∀ i < 19, Stmt.atom (.hint (.alloc (.n (4 + i)) 0)) ∈ clEEval := fun i hi => by
    unfold clEEval
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))
  have e0 : σ (.n 0) = entries := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have e1 : σ (.n 1) = gen ^ n := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have v32 : σ (.n 32) = chain := by
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp b11
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a with
    | hint h =>
      cases h with
      | allocDyn d s =>
        simp only [decide_eq_true_eq] at hp
        subst hp
        have hga' : σ (.n 32) = w 32 := hga
        rw [hga', w32]
      | _ => simp at hp
    | _ => simp at hp
  have v33 : ∀ c < 13, σ (.n (33 + c)) = 0 := by
    intro c hc'
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp b10 c (List.mem_range.mpr hc'))
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hga' : σ (.n (33 + c)) = _ := hga
    rw [hga', eEqb_sound he, word_zero]
  have hat : ∀ a ∈ atomsIn clEEval, a.Holds rd σ := by
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
      show LoadHolds rd (σ (.n 32)) c (σ (.n (33 + c)))
      rw [v32, v33 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have hdisp : Stmt.dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64] ∈ clElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b9; rwa [stmtEqb_sound he] at hs
  have hcall : Stmt.call "list_split" [.n 1] [.n 23, .n 24] ∈ clElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b7; rwa [stmtEqb_sound he] at hs
  have gd : ∀ v ∈ [V.n 63, V.n 64], σ v = w v.idx := hgs _ (mP _ hdisp)
  have gc : ∀ v ∈ [V.n 23, V.n 24], σ v = w v.idx := hgs _ (mP _ hcall)
  have v63 : σ (.n 63) = (digestScalars D).1 := (gd _ (by simp)).trans w63
  have v64 : σ (.n 64) = (digestScalars D).2 := (gd _ (by simp)).trans w64
  have v23 : σ (.n 23) = gen ^ m := (gc _ (by simp)).trans w23
  have v24 : σ (.n 24) = gen ^ r := (gc _ (by simp)).trans w24
  have v10 : σ (.n 10) = (digestScalars D).1 := by
    have : σ (.n 10) = w 10 := hgs _ (mF 6 (by omega))
    rw [this, w10]
  have v11 : σ (.n 11) = (digestScalars D).2 := by
    have : σ (.n 11) = w 11 := hgs _ (mF 7 (by omega))
    rw [this, w11]
  have hatElse : ∀ a ∈ atomsIn cl23Else, a.Holds rd σ := by
    intro a ha
    have hs := cl_atom_mem ha
    rw [hE] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hat a (cl_mem_atoms (mP _ hs))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl
      · show σ (.n 10) = σ (.n 63); rw [v10, v63]
      · show σ (.n 11) = σ (.n 64); rw [v11, v64]
  have v48 : σ (.n 48) = 1 := by rw [const_sound h48 hatElse, word_one]
  have v47 : σ (.n 47) = 1 + gen ^ m := by
    rw [add_sound h47 hatElse, const_sound h46 hatElse, word_one, v23]
  have v54 : σ (.n 54) = chain * gen ^ (13 * m) := by
    rw [monoIs_sound hm54 hatElse, v32, v23, gen_pow_pow]
  have v62 : σ (.n 62) = entries * gen ^ (68 * m) := by
    rw [monoIs_sound hm62 hatElse, e0, v23, gen_pow_pow]
  have v2 : σ (.n 2) = word 1 0 0 := hat _ (cl_mem_atoms (mH _ c2))
  have v3 : σ (.n 3) = σ (.n 1) + σ (.n 2) := hat _ (cl_mem_atoms (mH _ a3))
  have v65 : σ (.n 65) = σ (.n 10) := hat _ (cl_mem_atoms (mT _ t65))
  have v66 : σ (.n 66) = σ (.n 11) := hat _ (cl_mem_atoms (mT _ t66))
  have hs := cl_size_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s25, s26, s27, s28, s29, s30, s31⟩ := hs
  have q25 : σ (.n 25) = word 2 0 0 := hat _ s25
  have q26 : σ (.n 26) = σ (.n 23) * σ (.n 25) := hat _ s26
  have q27 : σ (.n 27) = σ (.n 26) * σ (.n 26) := hat _ s27
  have q28 : σ (.n 28) = σ (.n 27) * σ (.n 26) := hat _ s28
  have q29 : σ (.n 29) = σ (.n 28) * σ (.n 28) := hat _ s29
  have q30 : σ (.n 30) = σ (.n 29) * σ (.n 29) := hat _ s30
  have q31 : σ (.n 31) = σ (.n 30) * σ (.n 26) := hat _ s31
  refine ⟨hat, e0, e1, by rw [v3, v2, e1, word_one, pow_zero], v10, v11, v23, v24, ?_, v32,
    v47, v48, v54, v62, v63, v64, by rw [v65, v10], by rw [v66, v11]⟩
  rw [q31, q30, q29, q28, q27, q26, q25, v23, word_gen]
  ring

/-! ## The chain buffer -/

/-- A state's thirteen cells. -/
def stCells (S : KState) : List E := List.ofFn (cellsOfState S false)

/-- **The chain buffer's honest words**: the state after each of the first `m + 1` groups. -/
def chainCells (cells : List E) (m : ℕ) : List E :=
  (List.range (m + 1)).flatMap fun q =>
    stCells (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q))))

theorem length_chainCells (cells : List E) (m : ℕ) : (chainCells cells m).length = 13 * (m + 1) := by
  simp only [chainCells, List.length_flatMap, stCells, List.length_ofFn, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem state_of_reads {chain : E} {cells : List E} {m : ℕ} (h : ReadsAt rd chain (chainCells cells m))
    {q : ℕ} (hq : q ≤ m) :
    StateAt rd (chain * gen ^ (13 * q)) 0
      (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q)))) := by
  intro c
  have := Main.readsAt_range_flatMap (w := 13) (fun q _ => by simp [stCells]) h q (by omega) c c.isLt
  rw [loadHolds_mul_gen_pow, Nat.zero_add]
  rw [stCells, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at this
  exact this

/-- **`ClaimChainMem` off the chain buffer's honest words.** -/
theorem claimChainMem_of_reads {entries chain : E} {n : ℕ} {cells : List E}
    (hl : cells.length = 4 * n) (hr : ReadsAt rd entries cells)
    (h : ReadsAt rd chain (chainCells cells (n / 17))) : ClaimChainMem rd chain entries n := by
  intro q hq
  rw [memRun_take hr (by omega)]
  exact state_of_reads h hq

/-! ## Placed -/

theorem clNames_get {r : ℕ} (hr : r < 17) : clNames[r]! = clNames.getD r "" := by
  have h : r < clNames.length := by simp [clNames]; omega
  rw [getElem!_pos clNames r h, List.getD_eq_getElem _ _ h]

set_option maxRecDepth 100000 in
theorem cl_pure_all : ∀ k < 17,
    Stmt.pureList [clNames.getD k ""] (coreProgram.getD (321 + k) default).body = true := by
  decide +kernel

theorem cl_pure {r : ℕ} (hr : r < 17) : coreProgram.PureIn [clNames.getD r ""] :=
  pure_one (find_of_idx (cl_idx r hr) (by rw [coreProgram_length]; omega)) (cl_pure_all r hr)

set_option maxRecDepth 100000 in
theorem l16_pure : coreProgram.PureIn ["__loop15"] :=
  pure_one (find_of_idx l16_idx (by rw [coreProgram_length]; omega)) (by decide +kernel)

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

theorem clElsePre_eq : clElsePre = clP1 ++ [.dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64]] := by
  rw [clElsePre, cl23Else_split, clPost_eq]; simp

set_option maxRecDepth 100000 in
theorem clP1_kinds : clP1.all (fun s => isAtomS s ||
    stmtEqb s (.call "list_split" [.n 1] [.n 23, .n 24]) ||
    stmtEqb s (.callIf (.n 47) "__loop15" [.n 48, .n 23, .n 32, .n 0])) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_atoms : cl23Zero.all isAtomS = true := by decide +kernel

theorem slOk_atomS {rd : Reader} {σ : Val} {s : Stmt} (hs : isAtomS s = true)
    (h : ∀ a, s = .atom a → a.Holds rd σ) : SlOk rd σ s := by
  cases s <;> simp only [isAtomS, Bool.false_eq_true] at hs
  exact h _ rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`claim_list_digest` is complete, placed**: `n < 17 · 2^16` canonical claims' cells at `g^eP`
among the caller's words, its chain buffer after its frame holding the states after each group;
it returns their digest's cells. -/
theorem claim_list_digest_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n)
    (hc : AllCanonical cells) (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) :
    CompleteAtD fs cert 16 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) := by
  intro fp
  simp only [claimGroup, maxKeys] at hn
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP)
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 65, .n 66] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      (cl23Zero.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmZ : ∀ s ∈ clHead ++ cl23Zero ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hat a (cl_mem_atoms ?_)
      unfold clZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      (by
        rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    rw [hal] at h
    simpa using h
  · -- a nonempty list
    set m := n / 17 with hmdef
    set r := n % 17 with hrdef
    have hnm : n = 17 * m + r := (Nat.div_add_mod n 17).symm
    have hm16 : m < 65536 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set b0 := fp + fs "claim_list_digest" with hb0
    set chain : E := gen ^ b0 with hchain
    set Own : Main.Layout := [(b0, chainCells cells m)] with hOwn
    set D := keccak256 (cellsBytes cells) with hD
    have hfit : List.Forall₂ (fun c s => c.length ≤ s) [chainCells cells m] [13 * (m + 1)] := by
      simp [length_chainCells]
    have hWo : Within Own b0 (13 * (m + 1)) := by
      intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
      simp [length_chainCells]
    have hDo : DisjL Own := List.pairwise_singleton _ _
    have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells m) := fun rd hm =>
      reads_of_memL hm List.mem_cons_self
    -- the callees
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ m, gen ^ r]⟩,
        ⟨"__loop15", decide (m ≠ 0), [1, gen ^ m, chain, gen ^ eP], Lin ++ Own, Returns []⟩,
        ⟨clNames[r]!, true, [chain * gen ^ (13 * m), gen ^ eP * gen ^ (68 * m)], Lin ++ Own,
          Returns (digestCells D)⟩]
    have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
      intro k hk ht
      simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · have := list_split_completeAt fs cert (a := m) (b := r) (by simp [maxKeys]; omega)
          (by simp [claimGroup]; omega)
        rwa [show claimGroup * m + r = n by simp [claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine completeAt_of_rel_pureD l16_pure (List.mem_singleton_self _) (fun rd hm => ?_) 16
        have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        exact (guard_complete (find_of_idx l16_idx (by rw [coreProgram_length]; omega)) l16_shapeF
          (cl_blocks hl hr hc hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
      · show CompleteAtD fs cert 16 clNames[r]! (Lin ++ Own) _ _
        rw [clNames_get hr17]
        refine completeAt_of_rel_pureD (cl_pure hr17) (List.mem_singleton_self _) (fun rd hm => ?_) 16
        have hr := hLe rd (memL_append.mp hm).1
        have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl m)
        have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * m) = 136 * (8 * m); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * m)) (by simp; omega)
          (readsAt_drop' hr _) (canon_drop hc _)
        rwa [← cellsBytes_append, List.take_append_drop] at this
    obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
      kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (b0 + 13 * (m + 1))
    have hl0 : outs.length = 3 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain rfl := List.eq_nil_of_length_eq_zero hl3
    obtain ⟨h1, h2, h3, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + 13 * (m + 1) + Nk, Own ++ Lk, _, [], ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · rw [List.nil_append, within_append]
      exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
    simp only [List.nil_append] at hm
    obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
    obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
    have hch := hmOwn rd hmO
    have hz0 : StateAt rd chain 0 zeroState := by
      have := state_of_reads hch (Nat.zero_le m)
      rw [Nat.mul_zero, pow_zero, mul_one] at this
      exact this
    have hV := cl_core (rd := rd) (entries := gen ^ eP) (n := n) D hz0
    set σ := clσ rd (gen ^ eP) n chain D with hσ
    -- the path
    have h3ne : σ (.n 3) ≠ 0 := by
      rw [hV.v3, Ne, e_add_eq_zero_iff, pow_zero, gen_pow_eq_one_iff (by omega)]; omega
    have hx : σ (.n 24) = ofK (gpow r) := by rw [hV.v24, gen_pow_eq_ofK]
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 54, .n 62] [.n 63, .n 64] ::
          clPost.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]
      rw [cl23Else_split]
      exact walk_dispatch_fall σ clP1 clPost clP1_straight (by rw [clPost_eq]; rfl) (.n 24) clNames
        [.n 54, .n 62] [.n 63, .n 64] (i := r) (by simp [clNames]; omega) (by simp [clNames]) hx
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 65, .n 66] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      ((clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 54, .n 62] [.n 63, .n 64] ::
        clPost.flatMap (Main.slEvs σ)) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmE : ∀ s ∈ clHead ++ clP1 ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hV.atoms a (cl_mem_atoms ?_)
      unfold clEEval
      rw [clElsePre_eq]
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs <;> simp [hs]
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmE s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [hV.v3]; exact gen_pow_add_isInK n 0
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · refine slEvs_holds (fun s hs => ?_) e he
          have hk := List.all_eq_true.mp clP1_kinds s hs
          simp only [Bool.or_eq_true] at hk
          rcases hk with (hk | hk) | hk
          · exact slOk_atomS hk (hmE s (by simp [hs]))
          · rw [stmtEqb_sound hk]; trivial
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 47)); rw [hV.v47, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        rcases List.mem_cons.mp he with rfl | he
        · trivial
        · refine slEvs_holds (fun s hs => ?_) e he
          rw [clPost_eq] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n 10) = σ (.n 63); rw [hV.v10, hV.v63]
          · show σ (.n 11) = σ (.n 64); rw [hV.v11, hV.v64]
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmE s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ clP1_straight
    obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl)
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    have hpostA : clPost.filterMap Main.Stmt.allocSz = [] ∧ clPost.filterMap Main.Stmt.addrS = [] ∧
        clPost.filterMap Main.Stmt.callS = [] ∧ clPost.filterMap B1.Stmt.loadS = [] := by
      rw [clPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hal : allocs σ es = [13 * (m + 1)] := by
      rw [hes, es5_allocs, hha, hpa, hqa, hta, clP1_allocs, hpostA.1]
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, Main.Stmt.allocSz,
        List.map_cons, List.map_nil, Sum.elim_inr, hV.v31,
        logG_gen_pow (show 13 * (n / 17 + 1) < 2 ^ 64 - 1 by omega), List.nil_append, List.append_nil]
      rfl
    have h47 : decide (σ (.n 47) ≠ 0) = decide (m ≠ 0) := by
      rw [hV.v47]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have hcalls : calls es = [⟨"list_split", [.n 1], [.n 23, .n 24], true⟩,
        ⟨"__loop15", [.n 48, .n 23, .n 32, .n 0], [], decide (m ≠ 0)⟩,
        ⟨clNames[r]!, [.n 54, .n 62], [.n 63, .n 64], true⟩] := by
      rw [hes, es5_calls, hhc, hpc, hqc, htc, clP1_calls, hpostA.2.2.1]
      simp only [List.map_cons, List.map_nil, Main.mkCall, h47, clHead, clTail, List.filterMap_cons,
        List.filterMap_nil, Main.Stmt.callS, List.nil_append, List.cons_append, List.append_nil]
    have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (m + 1) →
        ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" [13 * (m + 1)] es i :=
      fun i h1 h2 => Or.inl ⟨(13 * (m + 1), b0), List.Mem.head _, h1, h2⟩
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, hV.v0, hV.v1]) hw
      (by show [σ (.n 65), σ (.n 66)] = _; rw [hV.v65, hV.v66]; rfl) hev
      (by
        rw [hal, hes, es5_allocDsts, hhd, hpd, hqd, htd, clP1_allocs, hpostA.1]
        simp only [List.map_cons, List.map_nil, clHead, clTail, List.filterMap_cons,
          List.filterMap_nil, Main.Stmt.allocSz, List.nil_append, List.append_nil, bases, hV.v32]
        rw [hchain, gen_pow_eq_ofK])
      (fun q hq => by
        rw [hes, es5_addrs, hhad, hpad, hqad, htad, clP1_addrs, hpostA.2.1] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · rw [hal] at h
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h
      exact h
    · rw [hcalls, hal]
      rw [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
          fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n 1)] = _; rw [hV.v1]
        · rw [(h1 rfl).1]; show [σ (.n 23), σ (.n 24)] = _; rw [hV.v23, hV.v24]
        · show [σ (.n 48), σ (.n 23), σ (.n 32), σ (.n 0)] = _
          rw [hV.v48, hV.v23, hV.v32, hV.v0]
        · rename_i ht; rw [(h2 ht).1]; rfl
        · show [σ (.n 54), σ (.n 62)] = _; rw [hV.v54, hV.v62]
        · rw [(h3 rfl).1]; show [σ (.n 63), σ (.n 64)] = _; rw [hV.v63, hV.v64]; rfl
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append, List.mem_append] at hq
        rcases hq with (hq | hq) | (hq | hq)
        · exact hLin' q hq
        · exact hmO q hq
        · exact hLin' q hq
        · exact hmO q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        all_goals
          obtain ⟨q, hq, h1', h2'⟩ := hi
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
          · simp only [hOwn, List.mem_singleton] at hq
            subst hq
            simp only [length_chainCells] at h2'
            exact Or.inl (Or.inr (hown i h1' h2'))
    · intro A hA
      rw [hes, es5_loads, B1.loadAddrs_straight σ _ clHead_straight,
        B1.loadAddrs_straight σ _ clP1_straight,
        B1.loadAddrs_straight σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl),
        B1.loadAddrs_straight σ _ clTail_straight, clP1_loads, hpostA.2.2.2] at hA
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS,
        List.map_nil, List.nil_append, List.append_nil, List.map_map, List.mem_map,
        List.mem_range, Function.comp] at hA
      obtain ⟨c, hc13, rfl⟩ := hA
      refine ⟨b0 + c, by rw [hV.v32, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]
      exact hown _ (by omega) (by omega)

end
end LeanVM.Guest.B1.Digest
