/-
  LeanVM.Guest.B1.Digest.ChildListComplete

  `child_claim_list_digest`, completely: a child's claim list rebuilt at honest slots, and the
  memory an honest run leaves at its chain buffer, give its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCLast
public import LeanVM.Guest.B1.Digest.ClaimListComplete

/-!
# `child_claim_list_digest`, completely

`ChildChainMem rd chain cells n`: the memory an honest run leaves at its chain buffer, the sponge
state after each group of `17` rebuilt claims at `chain · g^(13q)`.
`child_claim_list_digest_complete`: on a memory image, `n < 17 · 2^16` honest records
(`RecMem`, `ChildListOut`'s data: slots below the bound `g^L`, marks, canonical cells), the words
the range checks read (`BoundMem`) and that memory give the relation returning the cells' digest.
As `claim_list_digest_complete`: each branch evaluated on its own, the groups by `l17_block`
(`recMem_group`), the last claims by `ccLast_complete`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- **The memory an honest run of `child_claim_list_digest` leaves** at its chain buffer `chain`:
after `q ≤ n / 17` groups, the sponge state after the first `68q` rebuilt cells, at
`chain · g^(13q)`. -/
def ChildChainMem (rd : Reader) (chain : E) (cells : List E) (n : ℕ) : Prop :=
  ∀ q ≤ n / 17, StateAt rd (chain * gen ^ (13 * q)) 0
    (absorbChunks (8 * q) zeroState (cellsBytes (cells.take (68 * q))))

/-- `ChildListOut`'s data: the slots, the cells, their records. -/
theorem recMem_of_childListOut {entries cover base origin limit : E} {n : ℕ} {rets : List E}
    (h : ChildListOut rd entries cover base origin limit n rets) :
    ∃ (o : ℕ → ℕ) (cells : List E), cells.length = 4 * n ∧ AllCanonical cells ∧
      RecMem rd cover origin limit entries base n o cells ∧
      rets = digestCells (keccak256 (cellsBytes cells)) := h

/-- The records of the claims `s, …, s + k - 1`. -/
theorem recMem_group {cover origin limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd cover origin limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd cover origin limit entries (base * gen ^ s) k (fun j => o (s + j))
      ((cells.drop (4 * s)).take (4 * k)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : ((cells.drop (4 * s)).take (4 * k)).getD (4 * j + c) 0 = cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_pos' (by omega), show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

theorem l17_shapeF : loopShapeF (coreProgram.getD 338 default) "__loop16" = true := by
  have h := l17c_ok
  simp only [l17cOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1

/-- The groups of child claims: `__loop16`'s block at every group below `n / 17`. -/
theorem cc_blocks {entries cover base origin limit chain : E} {n L : ℕ} {o : ℕ → ℕ}
    {cells : List E} (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hrec : RecMem rd cover origin limit entries base n o cells) (hL : limit = gen ^ L)
    (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L) (hmem : ChildChainMem rd chain cells n) :
    ∀ j < n / 17, LoopBlock rd (coreProgram.getD 338 default) (gen ^ j) (gen ^ (n / 17))
      [chain, entries, cover, base, origin, limit] := by
  intro j hj
  have hS := hmem j (by omega)
  have hS1 := hmem (j + 1) (by omega)
  rw [show 68 * (j + 1) = 68 * j + 68 by ring, List.take_add, cellsBytes_append] at hS1
  have hpre : (cellsBytes (cells.take (68 * j))).length = rate * (8 * j) := by
    rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
    show 16 * (68 * j) = 136 * (8 * j); omega
  have hr := recMem_group hrec (s := 17 * j) (k := 17) (by omega)
  rw [show 4 * (17 * j) = 68 * j by ring, show 4 * 17 = 68 by rfl, mul_comm 17 j, pow_mul] at hr
  refine l17_block hpre (by rw [gen_pow_pow]; exact hS) (cells := ((cells.drop (68 * j)).take 68))
    (by simp; omega) (canon_take (canon_drop hc _) _) hr hL hL33 hdef fun c => ?_
  have := hS1 c
  rw [gen_pow_pow, loadHolds_mul_gen_pow]
  rw [loadHolds_mul_gen_pow, show 13 * (j + 1) + (0 + c.val) = 13 * j + (13 + c.val) by ring,
    show 8 * (j + 1) = 8 * j + 8 by ring] at this
  exact this

theorem cc_param (σ : Val) : (Fn.params Data.core24).map σ =
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] := rfl

theorem cc_cclNames {j : ℕ} (hj : j < cclNames.length) : cclNames[j] = cclNames.getD j "" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **`child_claim_list_digest` is complete**: on a memory image, `n < 17 · 2^16` honest records
at slots below the bound `g^L` (whose range checks read defined words) and the memory an honest
run leaves at a chain buffer `chain` give its relation returning the cells' digest. -/
theorem child_claim_list_digest_complete (hm : MemOk rd)
    {entries cover base origin limit chain : E} {n L : ℕ} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimGroup * maxKeys) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hrec : RecMem rd cover origin limit entries base n o cells)
    (hL : limit = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L)
    (hmem : 0 < n → ChildChainMem rd chain cells n) :
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, gen ^ n]
      (digestCells (keccak256 (cellsBytes cells))) := by
  have hz1 := ccz_ok
  have he1 := cce_ok
  have hb1 := ccbr_ok
  simp only [ccZOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ccEOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [ccBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨hzf, hzc⟩, hz14⟩, hz15⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hef, -⟩, -⟩, -⟩, h52⟩, h51⟩, h50⟩, -⟩, hm58⟩, hm64⟩, -⟩, -⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, b12⟩, b13⟩, b14⟩,
    b15⟩, b16⟩ := hb1
  have hE := stmtsEqb_sound b1
  have c6 : Stmt.atom (.const (.n 6) (word 1 0 0)) ∈ ccHead := by simp [ccHead]
  have a7 : Stmt.atom (.add (.n 7) (.n 5) (.n 6)) ∈ ccHead := by simp [ccHead]
  have t67 : Stmt.atom (.copy (.n 67) (.n 14)) ∈ ccTail := by simp [ccTail]
  have t68 : Stmt.atom (.copy (.n 68) (.n 15)) ∈ ccTail := by simp [ccTail]
  let args : List E := [entries, cover, base, origin, limit, gen ^ n]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args ccZEval) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) ccZEval args hchk
    rw [show args.length = 6 from rfl, List.isEmpty_iff.mp b13, ← hσ] at hgs
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
    have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi => by
      rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
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
    refine (rel_iff_sem find_child_claim_list_digest _ _).mpr ⟨σ, ?_, ?_⟩
    · rw [cc_param, par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega),
        par 4 (by omega), par 5 (by omega)]
      rfl
    rw [core24_shape]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨v6, v7, by rw [v7']; exact gen_pow_add_isInK 0 0, fun _ => ?_, fun h => absurd h70 h⟩
    refine holdsList_flat_of _ hzf _ _ (fun s hs => ?_) ⟨v67, v68, ?_⟩
    · have := List.all_eq_true.mp b16 s hs
      cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
      rename_i a
      exact ⟨hat a (cl_mem_atoms (mZ _ hs)), trivial⟩
    · rw [v67, v68, digestCells, ← hd]
  · -- a nonempty list
    have hmem := hmem hn0
    simp only [claimGroup, maxKeys] at hn
    have hl17 := cc_blocks hl hc hrec hL hL33 hdef hmem
    set m := n / 17 with hmdef
    set r := n % 17 with hrdef
    have hnm : n = 17 * m + r := (Nat.div_add_mod n 17).symm
    have hm16 : m < 65536 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set D := keccak256 (cellsBytes cells) with hD
    obtain ⟨w, hw⟩ : ∃ w : ℕ → E, w = fun i => if i = 27 then gen ^ m else if i = 28 then gen ^ r
        else if i = 36 then chain else if i = 14 ∨ i = 65 then (digestScalars D).1
        else if i = 15 ∨ i = 66 then (digestScalars D).2 else 0 := ⟨_, rfl⟩
    have w27 : w 27 = gen ^ m := by rw [hw]; simp
    have w28 : w 28 = gen ^ r := by rw [hw]; simp
    have w36 : w 36 = chain := by rw [hw]; simp
    have w14 : w 14 = (digestScalars D).1 := by rw [hw]; simp
    have w65 : w 65 = (digestScalars D).1 := by rw [hw]; simp
    have w15 : w 15 = (digestScalars D).2 := by rw [hw]; simp
    have w66 : w 66 = (digestScalars D).2 := by rw [hw]; simp
    obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w args ccEEval) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd w ccEEval args hchk
    rw [show args.length = 6 from rfl, ← hσ] at hgs
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
    have e1 : σ (.n 1) = cover := par 1 (by omega)
    have e2 : σ (.n 2) = base := par 2 (by omega)
    have e3 : σ (.n 3) = origin := par 3 (by omega)
    have e4 : σ (.n 4) = limit := par 4 (by omega)
    have e5 : σ (.n 5) = gen ^ n := par 5 (by omega)
    -- the oracle's values
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
    have hz0 : StateAt rd chain 0 zeroState := by
      have := hmem 0 (Nat.zero_le _)
      rw [Nat.mul_zero, pow_zero, mul_one] at this
      exact this
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
    have v64 : σ (.n 64) = base * gen ^ (17 * m) := by
      rw [monoIs_sound hm64 hatElse, e2, v27, gen_pow_pow]
    have v6 : σ (.n 6) = word 1 0 0 := hat _ (cl_mem_atoms (mH _ c6))
    have v7 : σ (.n 7) = σ (.n 5) + σ (.n 6) := hat _ (cl_mem_atoms (mH _ a7))
    have v67 : σ (.n 67) = σ (.n 14) := hat _ (cl_mem_atoms (mT _ t67))
    have v68 : σ (.n 68) = σ (.n 15) := hat _ (cl_mem_atoms (mT _ t68))
    have v7' : σ (.n 7) = gen ^ n + gen ^ 0 := by rw [v7, v6, e5, word_one, pow_zero]
    have h70 : σ (.n 7) ≠ 0 := by
      rw [v7']
      intro h
      have := gen_pow_inj (a := n) (b := 0) (by omega) (by omega) (e_add_eq_zero_iff.mp h)
      omega
    -- the last claims
    have hlast : coreProgram.Rel rd (cclNames.getD r "")
        [σ (.n 58), σ (.n 0), σ (.n 1), σ (.n 64), σ (.n 3), σ (.n 4)] [σ (.n 65), σ (.n 66)] := by
      have hpre : (cellsBytes (cells.take (68 * m))).length = rate * (8 * m) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * m) = 136 * (8 * m); omega
      have hS := hmem m le_rfl
      have hr := recMem_group hrec (s := 17 * m) (k := r) (by omega)
      rw [show 4 * (17 * m) = 68 * m by ring, List.take_of_length_le (by simp; omega),
        mul_comm 17 m] at hr
      have := ccLast_complete hr17 hpre hS (cells := cells.drop (68 * m)) (by simp; omega)
        (canon_drop hc _) hr hL hL33 hdef
      rw [← cellsBytes_append, List.take_append_drop] at this
      rw [v58, e0, e1, v64, e3, e4, v65, v66, mul_comm 17 m]
      exact this
    -- the groups
    have hf17 := find_of_idx l17_idx (by rw [coreProgram_length]; omega)
    have hguard := guard_complete hf17 l17_shapeF hl17
    have hms : MeaningListSplit [gen ^ n] [gen ^ m, gen ^ r] := by
      simp only [MeaningListSplit]
      exact ⟨m, hm16, r, hr17, by rw [hnm], rfl⟩
    refine (rel_iff_sem find_child_claim_list_digest _ _).mpr ⟨σ, ?_, ?_⟩
    · rw [cc_param, e0, e1, e2, e3, e4, e5]
    rw [core24_shape]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨v6, v7, by rw [v7']; exact gen_pow_add_isInK n 0, fun h => absurd h h70, fun _ => ?_⟩
    rw [hE]
    refine holdsList_flat_of _ (by rw [← hE]; exact List.all_eq_true.mpr hef) _ _
      (fun s hs => ?_) ⟨v67, v68, ?_⟩
    · rcases List.mem_append.mp hs with hs | hs
      · have := List.all_eq_true.mp b6 s hs
        simp only [Bool.or_eq_true] at this
        rcases this with ((h | h) | h) | h
        · cases s <;> simp only [isAtomS, Bool.false_eq_true] at h
          rename_i a _
          exact ⟨hat a (cl_mem_atoms (mP _ hs)), trivial⟩
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          rw [e5, v27, v28]
          exact ⟨list_split_complete rd hm _ _ hms, trivial⟩
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          refine ⟨by rw [v51]; exact hguard.1, fun hne => ?_, trivial⟩
          rw [v52, v27, v36, e0, e1, e2, e3, e4]
          exact hguard.2 (by rwa [v51] at hne)
        · rw [stmtEqb_sound h]
          simp only [Stmt.Holds, List.map_cons, List.map_nil]
          refine ⟨⟨r, by simp [cclNames]; omega, by rw [v28, gen_pow_eq_ofK], ?_⟩, trivial⟩
          rw [cc_cclNames]
          exact hlast
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ⟨show σ (.n 14) = σ (.n 65) by rw [v14, v65], trivial⟩
        · exact ⟨show σ (.n 15) = σ (.n 66) by rw [v15, v66], trivial⟩
    · rw [v67, v68, v14, v15]
      rfl

end
end LeanVM.Guest.B1.Digest
