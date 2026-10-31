/-
  LeanVM.Guest.B1.Digest.ClaimListComplete

  `claim_list_digest`, completely: its meaning's claims, and the memory an honest run leaves at
  its chain buffer, give its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCLast
public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# `claim_list_digest`, completely

`ClaimChainMem rd chain entries n`: the memory an honest run leaves at its chain buffer `chain`,
the sponge state after each group of `17` claims (`68` cells) at `chain · g^(13q)`.
`claim_list_digest_complete`: on a memory image, `n < 17 · 2^16` claims at `entries`
(`ClaimListOut`) and that memory give the relation. Each branch is evaluated on its own
(`Fwd.ev` of `clZEval`, `clEEval`): the empty list hashes the empty string; the nonempty one splits
`n = 17a + b` (`list_split_complete`), runs the groups (`guard_complete`, `l16_block`) and the last
`b` claims (`claimLast_complete`), the oracle naming the split, the buffer and the digest.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- **The memory an honest run of `claim_list_digest` leaves** at its chain buffer `chain`: after
`q ≤ n / 17` groups, the sponge state after the first `68q` cells at `entries`, at
`chain · g^(13q)`. -/
def ClaimChainMem (rd : Reader) (chain entries : E) (n : ℕ) : Prop :=
  ∀ q ≤ n / 17, StateAt rd (chain * gen ^ (13 * q)) 0
    (absorbChunks (8 * q) zeroState (cellsBytes (memRun rd entries (68 * q))))

theorem readsAt_take' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd p (cells.take k) := fun i hi => by
  rw [List.getElem_take]; exact hr i (by simp at hi; omega)

theorem readsAt_drop' {p : E} {cells : List E} (hr : ReadsAt rd p cells) (k : ℕ) :
    ReadsAt rd (p * gen ^ k) (cells.drop k) := fun i hi => by
  rw [loadHolds_mul_gen_pow, List.getElem_drop]; exact hr _ (by simp at hi; omega)

theorem memRun_take {p : E} {cells : List E} (hr : ReadsAt rd p cells) {k : ℕ}
    (hk : k ≤ cells.length) : memRun rd p k = cells.take k := by
  rw [readsAt_memRun (readsAt_take' hr k), List.length_take, Nat.min_eq_left hk]

theorem canon_take {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.take k) :=
  fun c h => hc c (List.mem_of_mem_take h)

theorem canon_drop {cells : List E} (hc : AllCanonical cells) (k : ℕ) : AllCanonical (cells.drop k) :=
  fun c h => hc c (List.mem_of_mem_drop h)

theorem l16_shapeF : loopShapeF (coreProgram.getD 320 default) "__loop15" = true := by
  have h := l16c_ok
  simp only [l16cOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1

/-- The groups of claims: `__loop15`'s block at every group below `a`. -/
theorem cl_blocks {chain entries : E} {n : ℕ} {cells : List E} (hl : cells.length = 4 * n)
    (hr : ReadsAt rd entries cells) (hc : AllCanonical cells) (hmem : ClaimChainMem rd chain entries n) :
    ∀ j < n / 17, LoopBlock rd (coreProgram.getD 320 default) (gen ^ j) (gen ^ (n / 17))
      [chain, entries] := by
  intro j hj
  have h68 : 68 * j + 68 ≤ cells.length := by omega
  have hS := hmem j (by omega)
  have hS1 := hmem (j + 1) (by omega)
  rw [memRun_take hr (by omega)] at hS
  rw [memRun_take hr (by omega), show 68 * (j + 1) = 68 * j + 68 by ring, List.take_add,
    cellsBytes_append] at hS1
  have hpre : (cellsBytes (cells.take (68 * j))).length = rate * (8 * j) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * j) = 136 * (8 * j); omega
  refine l16_block hpre (by rw [gen_pow_pow]; exact hS) (cells := ((cells.drop (68 * j)).take 68))
    (by simp; omega) ?_ (canon_take (canon_drop hc _) _) fun c => ?_
  · rw [gen_pow_pow]; exact readsAt_take' (readsAt_drop' hr _) _
  · have := hS1 c
    rw [gen_pow_pow, loadHolds_mul_gen_pow]
    rw [loadHolds_mul_gen_pow, show 13 * (j + 1) + (0 + c.val) = 13 * j + (13 + c.val) by ring,
      show 8 * (j + 1) = 8 * j + 8 by ring] at this
    exact this

theorem cl_clNames {j : ℕ} (hj : j < clNames.length) : clNames[j] = clNames.getD j "" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

theorem cl_param (σ : Val) : (Fn.params Data.core23).map σ = [σ (.n 0), σ (.n 1)] := rfl

set_option maxRecDepth 20000 in
/-- **`claim_list_digest` is complete**: on a memory image, the `n < 17 · 2^16` claims at `entries`
and the memory an honest run leaves at a chain buffer `chain` give its relation returning their
digest. -/
theorem claim_list_digest_complete (hm : MemOk rd) {entries chain : E} {n : ℕ} {rets : List E}
    (hn : n < claimGroup * maxKeys) (hout : ClaimListOut rd entries n rets)
    (hmem : 0 < n → ClaimChainMem rd chain entries n) :
    coreProgram.Rel rd "claim_list_digest" [entries, gen ^ n] rets := by
  obtain ⟨cells, hl, hr, hc, rfl⟩ := hout
  have hz1 := cz_ok
  have he1 := ce_ok
  have hb1 := clbr_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ceOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨hzf, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hef, -⟩, -⟩, -⟩, h48⟩, h47⟩, h46⟩, -⟩, hm54⟩, hm62⟩, -⟩, -⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩,
    b15⟩, b16⟩ := hb1
  have hE := stmtsEqb_sound b1
  have c2 : Stmt.atom (.const (.n 2) (word 1 0 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n 3) (.n 1) (.n 2)) ∈ clHead := by simp [clHead]
  have t65 : Stmt.atom (.copy (.n 65) (.n 10)) ∈ clTail := by simp [clTail]
  have t66 : Stmt.atom (.copy (.n 66) (.n 11)) ∈ clTail := by simp [clTail]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
    let args : List E := [entries, gen ^ 0]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args clZEval) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) clZEval args hchk
    rw [show args.length = 2 from rfl, List.isEmpty_iff.mp b13, ← hσ] at hgs
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
    have v3' : σ (.n 3) = gen ^ 0 + gen ^ 0 := by rw [v3, v2, e1, word_one, pow_zero]
    have h30 : σ (.n 3) = 0 := by rw [v3']; exact e_add_eq_zero_iff.mpr rfl
    obtain ⟨hd, -⟩ := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
      List.nil_append] at hd
    refine (rel_iff_sem find_claim_list_digest _ _).mpr ⟨σ, by rw [cl_param, e0, e1], ?_⟩
    rw [core23_shape]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨v2, v3, by rw [v3']; exact gen_pow_add_isInK 0 0, fun _ => ?_, fun h => absurd h30 h⟩
    refine holdsList_flat_of _ hzf _ _ (fun s hs => ?_) ⟨v65, v66, ?_⟩
    · have := List.all_eq_true.mp b16 s hs
      cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
      rename_i a
      exact ⟨hat a (cl_mem_atoms (mZ _ hs)), trivial⟩
    · rw [v65, v66, digestCells, ← hd]
  · -- a nonempty list
    have hmem := hmem hn0
    simp only [claimGroup, maxKeys] at hn
    have hl16 := cl_blocks hl hr hc hmem
    set m := n / 17 with hmdef
    set r := n % 17 with hrdef
    have hnm : n = 17 * m + r := (Nat.div_add_mod n 17).symm
    have hm16 : m < 65536 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set D := keccak256 (cellsBytes cells) with hD
    obtain ⟨w, hw⟩ : ∃ w : ℕ → E, w = fun i => if i = 23 then gen ^ m else if i = 24 then gen ^ r
        else if i = 32 then chain else if i = 10 ∨ i = 63 then (digestScalars D).1
        else if i = 11 ∨ i = 64 then (digestScalars D).2 else 0 := ⟨_, rfl⟩
    have w23 : w 23 = gen ^ m := by rw [hw]; simp
    have w24 : w 24 = gen ^ r := by rw [hw]; simp
    have w32 : w 32 = chain := by rw [hw]; simp
    have w10 : w 10 = (digestScalars D).1 := by rw [hw]; simp
    have w63 : w 63 = (digestScalars D).1 := by rw [hw]; simp
    have w11 : w 11 = (digestScalars D).2 := by rw [hw]; simp
    have w64 : w 64 = (digestScalars D).2 := by rw [hw]; simp
    obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
    let args : List E := [entries, gen ^ n]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w args clEEval) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd w clEEval args hchk
    rw [show args.length = 2 from rfl, ← hσ] at hgs
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
    -- the oracle's values
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
    have hz0 : StateAt rd chain 0 zeroState := by
      have := hmem 0 (Nat.zero_le _)
      rw [Nat.mul_zero, pow_zero, mul_one] at this
      exact this
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
    have v3' : σ (.n 3) = gen ^ n + gen ^ 0 := by rw [v3, v2, e1, word_one, pow_zero]
    have h30 : σ (.n 3) ≠ 0 := by
      rw [v3']
      intro h
      have := gen_pow_inj (a := n) (b := 0) (by omega) (by omega) (e_add_eq_zero_iff.mp h)
      omega
    -- the last claims
    have hlast : coreProgram.Rel rd (clNames.getD r "") [σ (.n 54), σ (.n 62)]
        [σ (.n 63), σ (.n 64)] := by
      have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * m) = 136 * (8 * m); omega
      have hS := hmem m le_rfl
      rw [memRun_take hr (by omega)] at hS
      have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * m)) (by simp; omega)
        (readsAt_drop' hr _) (canon_drop hc _)
      rw [← cellsBytes_append, List.take_append_drop] at this
      rw [v54, v62, v63, v64]
      exact this
    -- the groups
    have hf16 := find_of_idx l16_idx (by rw [coreProgram_length]; omega)
    have hguard := guard_complete hf16 l16_shapeF hl16
    have hms : MeaningListSplit [gen ^ n] [gen ^ m, gen ^ r] := by
      simp only [MeaningListSplit]
      exact ⟨m, hm16, r, hr17, by rw [hnm], rfl⟩
    refine (rel_iff_sem find_claim_list_digest _ _).mpr ⟨σ, by rw [cl_param, e0, e1], ?_⟩
    rw [core23_shape]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨v2, v3, by rw [v3']; exact gen_pow_add_isInK n 0, fun h => absurd h h30, fun _ => ?_⟩
    rw [hE]
    refine holdsList_flat_of _ (by rw [← hE]; exact List.all_eq_true.mpr hef) _ _
      (fun s hs => ?_) ⟨v65, v66, ?_⟩
    · rcases List.mem_append.mp hs with hs | hs
      · have := List.all_eq_true.mp b6 s hs
        simp only [Bool.or_eq_true] at this
        rcases this with ((h | h) | h) | h
        · cases s <;> simp only [isAtomS, Bool.false_eq_true] at h
          rename_i a _
          exact ⟨hat a (cl_mem_atoms (mP _ hs)), trivial⟩
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          rw [e1, v23, v24]
          exact ⟨list_split_complete rd hm _ _ hms, trivial⟩
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          refine ⟨by rw [v47]; exact hguard.1, fun hne => ?_, trivial⟩
          rw [v48, v23, v32, e0]
          exact hguard.2 (by rwa [v47] at hne)
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          refine ⟨⟨r, by simp [clNames]; omega, by rw [v24, gen_pow_eq_ofK], ?_⟩, trivial⟩
          rw [cl_clNames]
          exact hlast
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨show σ (.n 10) = σ (.n 63) by rw [v10, v63], trivial⟩
        · exact ⟨show σ (.n 11) = σ (.n 64) by rw [v11, v64], trivial⟩
    · rw [v65, v66, v10, v11]
      rfl

end
end LeanVM.Guest.B1.Digest
