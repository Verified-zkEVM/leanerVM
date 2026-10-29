/-
  LeanVM.Guest.B1.Main.AggSqueeze

  `aggregate_claims`' squeezing loop (`__loop25`: the lambdas and the batched claim) and its
  weighing loop (`__loop26`: the batched equality weight).
-/

module

public import LeanVM.Guest.B1.Main.AggAbsorb

/-!
# `__loop25` and `__loop26`

* `l26_step` (`__loop25`, core function `395`): iteration `x = g^c` permutes the sponge its row of
  fourteen words carries (`sqT·x^14`), squeezes `λ_fresh` and `λ_carried` (stored at
  `lam·x^2`), writes the row after them (an empty queue), and its running claim (word `13`) plus
  `λ_fresh · fresh[23] + λ_carried · carried[23]` of the child's claims (through the pointer
  tables `lf`, `lc`) into word `13` of the next row (`L26Step`).
* `l27_step` (`__loop26`, core function `397`): iteration `x = g^c` adds
  `λ_fresh · eq(fresh, r) + λ_carried · eq(carried, r)` to the running weight `w[c]` into
  `w[c + 1]`, `r` the `23` coordinates at `pt` (`L27Step`); the equality polynomials are products
  `Π (1 + p_j + r_j)` checked by evaluation (`eqChainOk`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## Templates as atoms -/

/-- Every atom of `as` is in the list. -/
def allIn (atoms as : List Atom) : Bool := as.all fun a => atoms.any (atomEqb a)

theorem allIn_holds {as : List Atom} (h : allIn atoms as = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    (C : CallRel) (kret : List E → Prop) : Stmt.HoldsList C rd σ (as.map Stmt.atom) True kret := by
  have hall : ∀ a ∈ as, a.Holds rd σ := by
    intro a ha
    simp only [allIn, List.all_eq_true] at h
    obtain ⟨a', ha', he⟩ := List.any_eq_true.mp (h a ha)
    rw [atomEqb_sound he]
    exact hat a' ha'
  have hA : AllAtoms (as.map Stmt.atom) := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
    exact ⟨a, rfl⟩
  exact (holdsList_atoms hA True kret).mpr ⟨fun a ha => hall a (by
    obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
    cases he
    exact ha'), trivial⟩

/-- `challengeT`'s atoms. -/
def challA (s0 s1 : V) (b : ℕ) : List Atom :=
  [.hint (.limbs s1 [.n b]), .add (.n (b + 1)) s1 (.n b), .const (.n (b + 2)) (word 1 0 1),
    .mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2)), .assertInK (.n b) (.n (b + 3)),
    .const (.n (b + 4)) (word 0 0 1), .mul (.n (b + 5)) (.n (b + 4)) (.n b),
    .add (.n (b + 6)) s0 (.n (b + 5))]

theorem chal_sound {s0 s1 : V} {b : ℕ} (h : allIn atoms (challA s0 s1 b) = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ChallengeOk σ s0 s1 b :=
  ((holds_challengeT (C := fun _ _ _ => True) s0 s1 b True (fun _ => True)).mp
    (allIn_holds h hat _ _)).1

/-! ## `__loop25`: the lambdas -/

/-- The first permutation's inputs: the row's rate cells (four copied), then its capacity. -/
def k1i : List V := [.n 17, .n 18, .n 19, .n 20, .n 25, .n 26, .n 27, .n 28, .n 12, .n 13, .n 14,
  .n 15, .n 16]

/-- The first permutation's outputs. -/
def k1o : List V := (List.range 13).map fun i => .n (29 + i)

/-- The second permutation's inputs: a zero rate, the first's capacity. -/
def k2i : List V := [.n 50, .n 50, .n 50, .n 50, .n 50, .n 51, .n 52, .n 53, .n 37, .n 38, .n 39,
  .n 40, .n 41]

/-- The second permutation's outputs. -/
def k2o : List V := (List.range 13).map fun i => .n (54 + i)

/-- **`__loop25`'s body, checked.** -/
def l26Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop25" && decide (fn.params.length = 6) &&
  monoIs A (.n 11) (.n 2) (.n 0) 14 &&
  A.any (isKeccakAt k1i k1o false false) && rowInOk A (.n 11) k1i &&
  allIn A (challA (.n 29) (.n 30) 42) &&
  (List.range 4).all (fun i => A.any (isConstAt (.n (50 + i)) 0 0)) &&
  A.any (isKeccakAt k2i k2o false false) &&
  allIn A (challA (.n 54) (.n 55) 67) &&
  isMul A (.n 74) (.n 0) (.n 0) && isMul A (.n 75) (.n 3) (.n 74) &&
  A.any (isLoadAt (.n 48) (.n 75) 0) && isMul A (.n 76) (.n 3) (.n 74) &&
  A.any (isLoadAt (.n 73) (.n 76) 1) &&
  isMul A (.n 77) (.n 4) (.n 0) && A.any (isLoadAt (.n 78) (.n 77) 0) &&
  isMul A (.n 79) (.n 5) (.n 0) && A.any (isLoadAt (.n 80) (.n 79) 0) &&
  storesOk A (.n 11) 14 5 (fun i => .n (62 + i)) &&
  (List.range 8).all (fun c => A.any (isLoadAt (.n (81 + c)) (.n 11) (14 + (5 + c)))) &&
  (List.range 8).all (fun c => A.any (isConstAt (.n (81 + c)) 0 0)) &&
  A.any (isLoadAt (.n 89) (.n 11) 13) && A.any (isLoadAt (.n 90) (.n 78) 23) &&
  isMul A (.n 91) (.n 48) (.n 90) && A.any (isAddAt (.n 92) (.n 89) (.n 91)) &&
  A.any (isLoadAt (.n 93) (.n 80) 23) && isMul A (.n 94) (.n 73) (.n 93) &&
  A.any (isAddAt (.n 95) (.n 92) (.n 94)) && A.any (isLoadAt (.n 95) (.n 11) 27)

set_option maxRecDepth 100000 in
theorem l26_ok : l26Ok (coreProgram.getD 375 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26_idx : coreProgram.indexOf? "__loop25" = some 375 := by decide +kernel

/-- **Child `x`'s lambdas**: from the sponge its row (`sqT·x^14`) carries, the two squeezes
stored at `lam·x^2`, the row after them, and the running claim on. -/
def L26Step (rd : Reader) (sqT lamT lfT lcT x : E) : Prop :=
  ∀ st : Fs, RowRel rd (sqT * x ^ 14) st →
    LoadHolds rd (lamT * x ^ 2) 0 st.squeeze.1 ∧
    LoadHolds rd (lamT * x ^ 2) 1 st.squeeze.2.squeeze.1 ∧
    RowRel rd (sqT * x ^ 14 * gen ^ 14) st.squeeze.2.squeeze.2 ∧
    LoadHolds rd (sqT * x ^ 14) 27 (memAt rd (sqT * x ^ 14) 13 +
      st.squeeze.1 * memAt rd (memAt rd (lfT * x) 0) 23 +
      st.squeeze.2.squeeze.1 * memAt rd (memAt rd (lcT * x) 0) 23)

theorem getD_k1o {c : ℕ} (hc : c < 13) : k1o.getD c default = .n (29 + c) := by
  simp [k1o, List.getD_eq_getElem?_getD, hc]

theorem getD_k2o {c : ℕ} (hc : c < 13) : k2o.getD c default = .n (54 + c) := by
  simp [k2o, List.getD_eq_getElem?_getD, hc]

theorem rateOf_nil : rateOf [] = List.replicate 8 0 := by
  rw [rateOf_eq_cells [] (by simp)]; rfl

theorem l26_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop25" (x :: ps) []) :
    (∀ N sqT lamT lfT lcT, ps = [N, sqT, lamT, lfT, lcT] → L26Step rd sqT lamT lfT lcT x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop25" (x * gen :: ps) []) := by
  have hf := find_of_idx l26_idx (by rw [coreProgram_length]; omega)
  have hok := l26_ok
  simp only [l26Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm11⟩, hk1⟩, hrin⟩, hc1⟩, hz⟩, hk2⟩,
    hc2⟩, hm74⟩, hm75⟩, hl48⟩, hm76⟩, hl73⟩, hm77⟩, hl78⟩, hm79⟩, hl80⟩, hcst⟩, hzst⟩, hzc⟩,
    hl89⟩, hl90⟩, hm91⟩, ha92⟩, hl93⟩, hm94⟩, ha95⟩, hl95⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N sqT lamT lfT lcT hN st hrow => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 375 default).params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5⟩ := hps
  have p11 : σ (.n 11) = sqT * x ^ 14 := by rw [monoIs_sound hm11 hat, h2, hx]
  -- the first squeeze
  have hin := rowIn_sound hrin hat
  rw [p11] at hin
  obtain ⟨hcan1, hout1⟩ := DupSpec.keccak_facts (keccak_sound hk1 hat)
  rw [hin] at hcan1 hout1
  have hperm := rowRel_perm hrow (fun c hc => hcan1 c (List.mem_append_left _ hc))
  rw [← hperm] at hout1
  have o1 : ∀ c (hc : c < 13), σ (.n (29 + c)) = cellsOfState st.perm false ⟨c, hc⟩ :=
    fun c hc => by rw [← getD_k1o hc]; exact hout1 c hc
  have lf : σ (.n 48) = st.squeeze.1 :=
    challengeT_value (chal_sound hc1 hat) (o1 0 (by omega)) (o1 1 (by omega))
  -- the second
  obtain ⟨-, hout2⟩ := DupSpec.keccak_facts (keccak_sound hk2 hat)
  simp only [List.all_eq_true, List.mem_range] at hz hzc
  have z : ∀ i < 4, σ (.n (50 + i)) = 0 := fun i hi => by
    rw [const_sound (hz i hi) hat, word_zero]
  have hin2 : k2i.map σ = rateOf [] ++ capOf st.perm := by
    rw [rateOf_nil]
    simp only [k2i, List.map_cons, List.map_nil, capOf]
    rw [z 0 (by omega), z 1 (by omega), z 2 (by omega), z 3 (by omega), o1 8 (by omega),
      o1 9 (by omega), o1 10 (by omega), o1 11 (by omega), o1 12 (by omega)]
    rfl
  have hp2 : permOf (k2i.map σ) = st.squeeze.2.perm := by rw [hin2]; rfl
  rw [hp2] at hout2
  have o2 : ∀ c (hc : c < 13), σ (.n (54 + c)) = cellsOfState st.squeeze.2.perm false ⟨c, hc⟩ :=
    fun c hc => by rw [← getD_k2o hc]; exact hout2 c hc
  have lc : σ (.n 73) = st.squeeze.2.squeeze.1 :=
    challengeT_value (chal_sound hc2 hat) (o2 0 (by omega)) (o2 1 (by omega))
  have p74 : σ (.n 74) = x ^ 2 := by rw [isMul_sound hm74 hat, hx, sq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := load_sound hl48 hat
    rwa [isMul_sound hm75 hat, h3, p74, lf] at this
  · have := load_sound hl73 hat
    rwa [isMul_sound hm76 hat, h3, p74, lc] at this
  · -- the row after
    have hcap : capOf st.squeeze.2.perm = rowCap rd (sqT * x ^ 14 * gen ^ 14) := by
      have e := stores_sound hcst hat
      rw [p11] at e
      simp only [rowCap, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
        List.map_nil, List.cons_append, capOf]
      rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
        o2 8 (by omega), o2 9 (by omega), o2 10 (by omega), o2 11 (by omega), o2 12 (by omega)]
      rfl
    show RowRel rd (sqT * x ^ 14 * gen ^ 14) ⟨capOf st.squeeze.2.perm, []⟩
    rw [hcap]
    refine rowRel_empty fun c hc => ?_
    simp only [List.all_eq_true, List.mem_range] at hzst
    have e := store_at (hzst c hc) hat
    rw [p11] at e
    rw [e, const_sound (hzc c hc) hat, word_zero]
  · -- the running claim
    have e27 := load_sound hl95 hat
    have e13 := memAt_of_load (load_sound hl89 hat)
    have e90 := memAt_of_load (load_sound hl90 hat)
    have e93 := memAt_of_load (load_sound hl93 hat)
    have e78 := memAt_of_load (load_sound hl78 hat)
    have e80 := memAt_of_load (load_sound hl80 hat)
    rw [isMul_sound hm77 hat, h4, hx] at e78
    rw [isMul_sound hm79 hat, h5, hx] at e80
    rw [p11] at e27 e13
    rw [add_sound ha95 hat, add_sound ha92 hat, isMul_sound hm91 hat, isMul_sound hm94 hat, lf,
      lc, ← e13, ← e90, ← e93, ← e78, ← e80] at e27
    exact e27

/-! ## Equality weights -/

/-- `t = 1 + p[j] + r[j]`, through two `ADD`s, the constant `1`, and loads through `pP`, `pR`. -/
def eqTermOk (A : List Atom) (t pP pR : V) (j : ℕ) : Bool :=
  match addOf A t with
  | some (a, r) => A.any (isLoadAt r pR j) && (match addOf A a with
      | some (o, pv) => A.any (isConstAt o 1 0) && A.any (isLoadAt pv pP j)
      | none => false)
  | none => false

theorem eqTerm_sound {t pP pR : V} {j : ℕ} (h : eqTermOk atoms t pP pR j = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ t = 1 + memAt rd (σ pP) j + memAt rd (σ pR) j := by
  unfold eqTermOk at h
  split at h
  · rename_i a r har
    simp only [Bool.and_eq_true] at h
    obtain ⟨hr, h⟩ := h
    split at h
    · rename_i o pv hop
      simp only [Bool.and_eq_true] at h
      rw [addOf_sound har hat, addOf_sound hop hat, const_sound h.1 hat, word_one,
        memAt_of_load (load_sound h.2 hat), memAt_of_load (load_sound hr hat)]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- `out` is `Π_{j < n} (1 + p[j] + r[j])`, its factors through `MUL`s from the last. -/
def eqChainOk (A : List Atom) (pP pR : V) : ℕ → V → Bool
  | 0, _ => false
  | 1, t => eqTermOk A t pP pR 0
  | n + 2, out => match mulOf A out with
    | some (prev, t) => eqTermOk A t pP pR (n + 1) && eqChainOk A pP pR (n + 1) prev
    | none => false

theorem memRun_succ (rd : Reader) (p : E) (n : ℕ) :
    memRun rd p (n + 1) = memRun rd p n ++ [memAt rd p n] := by
  simp [memRun, List.range_succ]

theorem eqEval_snoc (l r : List E) (a b : E) (h : l.length = r.length) :
    eqEval (l ++ [a]) (r ++ [b]) = eqEval l r * (1 + a + b) := by
  rw [eqEval, eqEval, List.zipWith_append h, List.foldl_append]
  rfl

theorem eqChain_sound {pP pR : V} : ∀ {n : ℕ} {out : V}, eqChainOk atoms pP pR n out = true →
    (∀ a ∈ atoms, a.Holds rd σ) →
    σ out = eqEval (memRun rd (σ pP) n) (memRun rd (σ pR) n)
  | 0, _, h, _ => absurd h (by simp [eqChainOk])
  | 1, t, h, hat => by
    rw [eqTerm_sound h hat]
    simp [memRun, eqEval]
  | n + 2, out, h, hat => by
    unfold eqChainOk at h
    split at h
    · rename_i prev t hm
      simp only [Bool.and_eq_true] at h
      rw [mulOf_sound hm hat, eqChain_sound h.2 hat, eqTerm_sound h.1 hat,
        memRun_succ rd _ (n + 1), memRun_succ rd _ (n + 1), eqEval_snoc _ _ _ _ (by simp)]
    · exact absurd h (by simp)

/-! ## `__loop26`: the weights -/

/-- **`__loop26`'s body, checked.** -/
def l27Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop26" && decide (fn.params.length = 7) &&
  isMul A (.n 7) (.n 2) (.n 0) && A.any (isLoadAt (.n 8) (.n 7) 0) &&
  isMul A (.n 9) (.n 3) (.n 0) && A.any (isLoadAt (.n 10) (.n 9) 0) &&
  eqChainOk A (.n 8) (.n 4) 23 (.n 256) && eqChainOk A (.n 10) (.n 4) 23 (.n 261) &&
  isMul A (.n 262) (.n 0) (.n 0) &&
  isMul A (.n 263) (.n 5) (.n 0) && A.any (isLoadAt (.n 264) (.n 263) 0) &&
  isMul A (.n 265) (.n 6) (.n 262) && A.any (isLoadAt (.n 266) (.n 265) 0) &&
  isMul A (.n 267) (.n 266) (.n 256) && A.any (isAddAt (.n 268) (.n 264) (.n 267)) &&
  isMul A (.n 269) (.n 6) (.n 262) && A.any (isLoadAt (.n 270) (.n 269) 1) &&
  isMul A (.n 271) (.n 270) (.n 261) && A.any (isAddAt (.n 272) (.n 268) (.n 271)) &&
  isMul A (.n 273) (.n 5) (.n 0) && A.any (isLoadAt (.n 272) (.n 273) 1)

set_option maxRecDepth 100000 in
theorem l27_ok : l27Ok (coreProgram.getD 377 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27_idx : coreProgram.indexOf? "__loop26" = some 377 := by decide +kernel

/-- **Child `x`'s weight**: `w[x·g] = w[x] + λ_fresh · eq(fresh, r) + λ_carried · eq(carried, r)`,
the lambdas at `lam·x^2`, the claims' points through the pointer tables, `r` at `pt`. -/
def L27Step (rd : Reader) (lfT lcT pt wT lamT x : E) : Prop :=
  LoadHolds rd (wT * x) 1 (memAt rd (wT * x) 0 +
    memAt rd (lamT * x ^ 2) 0 * eqEval (memRun rd (memAt rd (lfT * x) 0) 23) (memRun rd pt 23) +
    memAt rd (lamT * x ^ 2) 1 * eqEval (memRun rd (memAt rd (lcT * x) 0) 23) (memRun rd pt 23))

theorem l27_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop26" (x :: ps) []) :
    (∀ N lfT lcT pt wT lamT, ps = [N, lfT, lcT, pt, wT, lamT] → L27Step rd lfT lcT pt wT lamT x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop26" (x * gen :: ps) []) := by
  have hf := find_of_idx l27_idx (by rw [coreProgram_length]; omega)
  have hok := l27_ok
  simp only [l27Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm7⟩, hl8⟩, hm9⟩, hl10⟩, he1⟩, he2⟩, hm262⟩, hm263⟩,
    hl264⟩, hm265⟩, hl266⟩, hm267⟩, ha268⟩, hm269⟩, hl270⟩, hm271⟩, ha272⟩, hm273⟩, hl272⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lfT lcT pt wT lamT hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 377 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have p262 : σ (.n 262) = x ^ 2 := by rw [isMul_sound hm262 hat, hx, sq]
  have e8 := memAt_of_load (load_sound hl8 hat)
  have e10 := memAt_of_load (load_sound hl10 hat)
  rw [isMul_sound hm7 hat, h2, hx] at e8
  rw [isMul_sound hm9 hat, h3, hx] at e10
  have ef := eqChain_sound he1 hat
  have ec := eqChain_sound he2 hat
  rw [← e8, h4] at ef
  rw [← e10, h4] at ec
  have e264 := memAt_of_load (load_sound hl264 hat)
  have e266 := memAt_of_load (load_sound hl266 hat)
  have e270 := memAt_of_load (load_sound hl270 hat)
  have e272 := load_sound hl272 hat
  rw [isMul_sound hm263 hat, h5, hx] at e264
  rw [isMul_sound hm273 hat, h5, hx] at e272
  rw [isMul_sound hm265 hat, h6, p262] at e266
  rw [isMul_sound hm269 hat, h6, p262] at e270
  unfold L27Step
  rw [add_sound ha272 hat, add_sound ha268 hat, isMul_sound hm267 hat, isMul_sound hm271 hat,
    ← e264, ← e266, ← e270, ef, ec] at e272
  exact e272

end
end LeanVM.Guest.B1.Main
