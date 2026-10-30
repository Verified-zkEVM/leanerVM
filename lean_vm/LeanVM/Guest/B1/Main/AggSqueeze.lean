/-
  LeanVM.Guest.B1.Main.AggSqueeze

  `aggregate_claims`' squeezing loop (`__loop25`: the lambdas and the batched claim) and its
  weighing loop (`__loop26`: the batched equality weight).
-/

module

public import LeanVM.Guest.B1.Main.AggAbsorb

/-!
# `__loop25` and `__loop26`

* `l26_step` (`__loop25`, core function `375`): iteration `x = g^c` reads record `c` of
  `bc_chain` (`chain·x^2`, two words: `λ`'s power `λ^(2c)` and the running claim), writes the
  power times `λ²` into word `2` (record `c + 1`'s power) and the running claim plus the power
  times `fresh[23] + λ · carried[23]` of the child's claims (through the pointer tables `lf`,
  `lc`) into word `3` (record `c + 1`'s claim) (`L26Step`).
* `l27_step` (`__loop26`, core function `377`): iteration `x = g^c` adds
  `p · (eq(fresh, r) + λ · eq(carried, r))` to the running weight `w[c]` into `w[c + 1]`, `p`
  record `c`'s power, `r` the `23` coordinates at `pt` (`L27Step`); the equality polynomials are
  products `Π (1 + p_j + r_j)` checked by evaluation (`eqChainOk`).
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

/-! ## `__loop25`: the powers of `λ` and the running claim -/

/-- **`__loop25`'s body, checked.** -/
def l26Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop25" && decide (fn.params.length = 7) &&
  isMul A (.n 7) (.n 0) (.n 0) && isMul A (.n 8) (.n 2) (.n 7) &&
  A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul A (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  isMul A (.n 12) (.n 4) (.n 0) && A.any (isLoadAt (.n 13) (.n 12) 0) &&
  isMul A (.n 14) (.n 9) (.n 5) && A.any (isLoadAt (.n 14) (.n 8) 2) &&
  A.any (isLoadAt (.n 15) (.n 8) 1) && A.any (isLoadAt (.n 16) (.n 11) 23) &&
  A.any (isLoadAt (.n 17) (.n 13) 23) && isMul A (.n 18) (.n 6) (.n 17) &&
  A.any (isAddAt (.n 19) (.n 16) (.n 18)) && isMul A (.n 20) (.n 9) (.n 19) &&
  A.any (isAddAt (.n 21) (.n 15) (.n 20)) && A.any (isLoadAt (.n 21) (.n 8) 3)

set_option maxRecDepth 100000 in
theorem l26_ok : l26Ok (coreProgram.getD 375 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26_idx : coreProgram.indexOf? "__loop25" = some 375 := by decide +kernel

/-- **Child `x`'s record**: the record at `chain·x^2` holds `λ`'s power and the running claim;
the next record holds the power times `λ²` and the running claim plus the power times
`fresh[23] + λ · carried[23]` of the child's claims (through the pointer tables `lf`, `lc`). -/
def L26Step (rd : Reader) (chainT lfT lcT lamSq lam x : E) : Prop :=
  LoadHolds rd (chainT * x ^ 2) 2 (memAt rd (chainT * x ^ 2) 0 * lamSq) ∧
  LoadHolds rd (chainT * x ^ 2) 3 (memAt rd (chainT * x ^ 2) 1 +
    memAt rd (chainT * x ^ 2) 0 * (memAt rd (memAt rd (lfT * x) 0) 23 +
      lam * memAt rd (memAt rd (lcT * x) 0) 23))

theorem l26_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop25" (x :: ps) []) :
    (∀ N chainT lfT lcT lamSq lam, ps = [N, chainT, lfT, lcT, lamSq, lam] →
      L26Step rd chainT lfT lcT lamSq lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop25" (x * gen :: ps) []) := by
  have hf := find_of_idx l26_idx (by rw [coreProgram_length]; omega)
  have hok := l26_ok
  simp only [l26Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm7⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩, hm12⟩, hl13⟩, hm14⟩,
    hl14⟩, hl15⟩, hl16⟩, hl17⟩, hm18⟩, ha19⟩, hm20⟩, ha21⟩, hl21⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N chainT lfT lcT lamSq lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 375 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have p8 : σ (.n 8) = chainT * x ^ 2 := by
    rw [isMul_sound hm8 hat, isMul_sound hm7 hat, h2, hx, sq]
  have e9 := memAt_of_load (load_sound hl9 hat)
  have e11 := memAt_of_load (load_sound hl11 hat)
  have e13 := memAt_of_load (load_sound hl13 hat)
  have e15 := memAt_of_load (load_sound hl15 hat)
  have e16 := memAt_of_load (load_sound hl16 hat)
  have e17 := memAt_of_load (load_sound hl17 hat)
  rw [p8] at e9 e15
  rw [isMul_sound hm10 hat, h3, hx] at e11
  rw [isMul_sound hm12 hat, h4, hx] at e13
  refine ⟨?_, ?_⟩
  · have := load_sound hl14 hat
    rwa [p8, isMul_sound hm14 hat, h5, ← e9] at this
  · have := load_sound hl21 hat
    rwa [p8, add_sound ha21 hat, isMul_sound hm20 hat, add_sound ha19 hat, isMul_sound hm18 hat,
      h6, ← e9, ← e15, ← e16, ← e17, ← e11, ← e13] at this

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
  loopShapeF fn "__loop26" && decide (fn.params.length = 8) &&
  isMul A (.n 8) (.n 2) (.n 0) && A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul A (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  eqChainOk A (.n 9) (.n 4) 23 (.n 257) && eqChainOk A (.n 11) (.n 4) 23 (.n 262) &&
  isMul A (.n 263) (.n 0) (.n 0) && isMul A (.n 264) (.n 5) (.n 263) &&
  isMul A (.n 265) (.n 6) (.n 0) && A.any (isLoadAt (.n 266) (.n 265) 0) &&
  A.any (isLoadAt (.n 267) (.n 264) 0) && isMul A (.n 268) (.n 7) (.n 262) &&
  A.any (isAddAt (.n 269) (.n 257) (.n 268)) && isMul A (.n 270) (.n 267) (.n 269) &&
  A.any (isAddAt (.n 271) (.n 266) (.n 270)) && isMul A (.n 272) (.n 6) (.n 0) &&
  A.any (isLoadAt (.n 271) (.n 272) 1)

set_option maxRecDepth 100000 in
theorem l27_ok : l27Ok (coreProgram.getD 377 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27_idx : coreProgram.indexOf? "__loop26" = some 377 := by decide +kernel

/-- **Child `x`'s weight**: `w[x·g] = w[x] + p · (eq(fresh, r) + λ · eq(carried, r))`, `p` the
power of `λ` at `chain·x^2`, the claims' points through the pointer tables, `r` at `pt`. -/
def L27Step (rd : Reader) (lfT lcT pt chainT wT lam x : E) : Prop :=
  LoadHolds rd (wT * x) 1 (memAt rd (wT * x) 0 + memAt rd (chainT * x ^ 2) 0 *
    (eqEval (memRun rd (memAt rd (lfT * x) 0) 23) (memRun rd pt 23) +
      lam * eqEval (memRun rd (memAt rd (lcT * x) 0) 23) (memRun rd pt 23)))

theorem l27_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop26" (x :: ps) []) :
    (∀ N lfT lcT pt chainT wT lam, ps = [N, lfT, lcT, pt, chainT, wT, lam] →
      L27Step rd lfT lcT pt chainT wT lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop26" (x * gen :: ps) []) := by
  have hf := find_of_idx l27_idx (by rw [coreProgram_length]; omega)
  have hok := l27_ok
  simp only [l27Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩, he1⟩, he2⟩, hm263⟩, hm264⟩,
    hm265⟩, hl266⟩, hl267⟩, hm268⟩, ha269⟩, hm270⟩, ha271⟩, hm272⟩, hl271⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lfT lcT pt chainT wT lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 377 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hps
  have e9 := memAt_of_load (load_sound hl9 hat)
  have e11 := memAt_of_load (load_sound hl11 hat)
  rw [isMul_sound hm8 hat, h2, hx] at e9
  rw [isMul_sound hm10 hat, h3, hx] at e11
  have ef := eqChain_sound he1 hat
  have ec := eqChain_sound he2 hat
  rw [← e9, h4] at ef
  rw [← e11, h4] at ec
  have e266 := memAt_of_load (load_sound hl266 hat)
  have e267 := memAt_of_load (load_sound hl267 hat)
  have e271 := load_sound hl271 hat
  rw [isMul_sound hm265 hat, h6, hx] at e266
  rw [isMul_sound hm264 hat, isMul_sound hm263 hat, h5, hx, ← sq] at e267
  rw [isMul_sound hm272 hat, h6, hx] at e271
  unfold L27Step
  rw [add_sound ha271 hat, isMul_sound hm270 hat, add_sound ha269 hat, isMul_sound hm268 hat, h7,
    ← e266, ← e267, ef, ec] at e271
  exact e271

end
end LeanVM.Guest.B1.Main
