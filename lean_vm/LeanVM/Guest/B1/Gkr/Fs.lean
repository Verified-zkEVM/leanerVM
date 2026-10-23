/-
  LeanVM.Guest.B1.Gkr.Fs

  The guest's Fiat-Shamir sponge as it carries it, the Spec's programs run on it, and the
  templates of the inline Fiat-Shamir helpers: a copy of B1-a's `B1/Common/Sponge`,
  `B1/Common/Run` and `B1/Fs/Templates` (branch `mumbai-keccak-b1a`), prefixed `tbx`, local to
  these families until they import B1-a's.
-/

module

public import LeanVM.Guest.B1.Tables.Basic

/-!
# The carried sponge (local copy)

`TbxFs` (five capacity cells and the waiting scalars), `TbxFs.Carries`, `TbxRunsTo` (a Spec
program run on any sponge the guest carries as `s`), the run combinators (`TbxRunsTo.bind`,
`tbx_runsTo_readE`, `tbx_runsTo_sampleE`, …), and the templates `tbxFsNextT`, `tbxChallengeT`,
`tbxKeccakA` with their meanings. Copied from B1-a (credit there); to be replaced by imports of
`B1/Common` and `B1/Fs` when the families merge.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem tbx_word_y : word 0 1 0 = y := by rw [y_eq]; rfl

theorem tbx_word_yy : word 0 0 1 = y * y := by
  rw [y_eq, mul_limbs]
  simp only [word, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> rfl

theorem tbx_word_y_inv : word 1 0 1 = y⁻¹ := by rw [y_inv]; rfl

/-- `y · E(t)`, the data's `word 0 t 0`. -/
theorem tbx_word_y_mul (t : ℕ) : word 0 t 0 = y * eOfNat t := by
  rw [eOfNat_eq_ofLimbs, y_eq, mul_limbs]
  simp only [word, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf <;> rfl





/-! ## Cells of the sponge -/

/-- The five capacity cells of a state: cells `8..12` of its even layout, lanes `16..24`
(`fs0 .. fs4`, `sp[8] .. sp[12]`). -/
def tbxCapOf (S : KState) : List E :=
  [cellsOfState S false 8, cellsOfState S false 9, cellsOfState S false 10,
    cellsOfState S false 11, cellsOfState S false 12]

/-- The eight rate cells of the waiting scalars: scalar `k`'s two cells at `2k`, `2k + 1`
(`fs_pack`), zero past them. -/
def tbxRateOf (pend : List (E × ℕ)) : List E := (List.range 8).map (Keccak.rateCell pend)

/-- The state one `KECCAK` in the even layouts writes from the thirteen cells it reads. -/
def tbxPermOf (cells : List E) : KState := keccakF (stateOfCells (cells13 cells) false)

/-- Every cell canonical (`IsCanonical128`), as a `KECCAK` requires of the cells it reads. -/
def TbxAllCanonical (cs : List E) : Prop := ∀ c ∈ cs, IsCanonical128 c

/-! ## The carried sponge -/

/-- The guest's sponge: the five capacity cells it carries, and the scalars waiting with their
tags. -/
structure TbxFs where
  /-- The capacity cells. -/
  cap : List E
  /-- The waiting scalars and their tags. -/
  pend : List (E × ℕ)

namespace TbxFs

/-- The state the next permutation writes: the waiting scalars over the rate, the capacity
kept. -/
def perm (s : TbxFs) : KState := tbxPermOf (tbxRateOf s.pend ++ s.cap)

/-- Absorb a scalar with a tag: a full queue is permuted first (`absorb`). -/
def absorb (s : TbxFs) (x : E) (t : ℕ) : TbxFs :=
  if s.pend.length = rateScalars then ⟨tbxCapOf s.perm, [(x, t)]⟩ else ⟨s.cap, s.pend ++ [(x, t)]⟩

/-- Absorb scalars in order, each with the tag `t`. -/
def absorbAll (s : TbxFs) (xs : List E) (t : ℕ) : TbxFs := xs.foldl (fun s x ↦ s.absorb x t) s

/-- Squeeze a challenge: a permutation, its state's challenge (`squeeze`, `challengeOf`). -/
def squeeze (s : TbxFs) : E × TbxFs := (challengeOf s.perm, ⟨tbxCapOf s.perm, []⟩)

/-- `n` challenges in order, and the sponge after them. -/
def squeezeN : ℕ → TbxFs → List E × TbxFs
  | 0, s => ([], s)
  | n + 1, s => ((s.squeeze.1 :: (squeezeN n s.squeeze.2).1), (squeezeN n s.squeeze.2).2)

/-- The cells a `KECCAK` can read: five canonical capacity cells, at most four waiting. -/
def Ok (s : TbxFs) : Prop := s.cap.length = 5 ∧ TbxAllCanonical s.cap ∧ s.pend.length ≤ rateScalars

/-- The Spec's sponge `sp` is the one the guest carries as `s`. -/
def Carries (s : TbxFs) (sp : Sponge) : Prop := tbxCapOf sp.state = s.cap ∧ sp.pending = s.pend

end TbxFs

/-! ## Runs of the Spec's programs -/

/-- The deployed reading of a Spec program: `Compile.run` at Keccak-256 and Keccak-f. -/
abbrev tbxRunId {α : Type} (p : Prog α) (st : St) : Option (α × St) :=
  Compile.run (m := Id) keccak256 keccakF p st

/-- From any Spec sponge the guest carries as `s`, the program `p` reads exactly the stream words
`xs` and returns `a`, leaving a sponge the guest carries as `s'`, on any rest of the stream, any
openings and any roots. -/
def TbxRunsTo {α : Type} (p : Prog α) (s : TbxFs) (xs : List E) (a : α) (s' : TbxFs) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)), ∃ sp' : Sponge, s'.Carries sp' ∧
      tbxRunId p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)



/-! ## The operations -/

/-- The cells of the permutation input: the rate cells of the waiting scalars, then the
capacity's. -/
theorem tbx_stateOfCells_carried (S : KState) (pend : List (E × ℕ)) :
    stateOfCells (cells13 (tbxRateOf pend ++ tbxCapOf S)) false = duplexInput ⟨S, pend⟩ := by
  apply Keccak.stateOfCells_duplex
  · intro c hc
    simp only [cells13, tbxRateOf]
    rw [List.getD_append _ _ _ _ (by simpa using hc), List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hc]
    rfl
  · intro c hc
    fin_cases c <;> simp_all [cells13, tbxRateOf, tbxCapOf]

/-- **The carried sponge permutes as the Spec's.** -/
theorem tbx_perm_eq {s : TbxFs} {sp : Sponge} (h : s.Carries sp) : keccakF (duplexInput sp) = s.perm := by
  obtain ⟨h1, h2⟩ := h
  rw [TbxFs.perm, tbxPermOf, ← h1, tbx_stateOfCells_carried, ← h2]

/-- **`TbxFs.absorb` is `absorb`.** -/
theorem tbx_carries_absorb {s : TbxFs} {sp : Sponge} (h : s.Carries sp) (x : E) (t : ℕ) :
    (s.absorb x t).Carries (Id.run (Compile.absorb (m := Id) keccakF sp x t)) := by
  have hp := tbx_perm_eq h
  obtain ⟨h1, h2⟩ := h
  unfold TbxFs.absorb
  split_ifs with hl
  · rw [Keccak.absorb_id_full sp x t (by rw [h2]; exact hl), hp]
    exact ⟨rfl, rfl⟩
  · have : Compile.absorb (m := Id) keccakF sp x t =
        { sp with pending := sp.pending ++ [(x, t)] } := by
      simp [Compile.absorb, h2, hl]
      rfl
    rw [this]
    exact ⟨h1, by rw [← h2]; rfl⟩

/-- **`TbxFs.squeeze` is `squeeze`.** -/
theorem tbx_carries_squeeze {s : TbxFs} {sp : Sponge} (h : s.Carries sp) :
    (Id.run (Compile.squeeze (m := Id) keccakF sp)).1 = s.squeeze.1 ∧
      s.squeeze.2.Carries (Id.run (Compile.squeeze (m := Id) keccakF sp)).2 := by
  have hp := tbx_perm_eq h
  rw [Keccak.squeeze_id, hp]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Composing runs -/

theorem tbx_prog_bind_eq {α β : Type} (p : Prog α) (f : α → Prog β) : p >>= f = p.bind f := rfl

theorem tbx_prog_pure_eq {α : Type} (a : α) : (pure a : Prog α) = Prog.ret a := rfl

theorem tbx_run_bind {α β : Type} (p : Prog α) (f : α → Prog β) (st : St) :
    tbxRunId (p.bind f) st = (tbxRunId p st).bind (fun r => tbxRunId (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [tbxRunId, Prog.bind, Compile.run]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [tbxRunId, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [tbxRunId, Prog.bind, Compile.run]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [tbxRunId, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind]
      split
      · exact ih _ _
      · rfl

theorem tbx_runsTo_ret {α : Type} (a : α) (s : TbxFs) : TbxRunsTo (pure a : Prog α) s [] a s :=
  fun sp h _ _ _ => ⟨sp, h, rfl⟩

theorem TbxRunsTo.bind {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 s2 : TbxFs} {xs ys : List E}
    {a : α} {b : β} (h1 : TbxRunsTo p s xs a s1) (h2 : TbxRunsTo (f a) s1 ys b s2) :
    TbxRunsTo (p >>= f) s (xs ++ ys) b s2 := by
  intro sp hs rest os roots
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) os roots
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest os roots
  refine ⟨sp2, hs2, ?_⟩
  rw [tbx_prog_bind_eq, tbx_run_bind, List.append_assoc, e1]
  exact e2

theorem TbxRunsTo.of_eq {α : Type} {p : Prog α} {s s' t t' : TbxFs} {xs xs' : List E} {a a' : α}
    (h : TbxRunsTo p s xs a t) (hs : s = s') (hx : xs = xs') (ha : a = a') (ht : t = t') :
    TbxRunsTo p s' xs' a' t' := by
  subst hs hx ha ht; exact h

/-! ## The steps -/

/-- **A read** absorbs the stream word with `dsObserve`. -/
theorem tbx_runsTo_readE (s : TbxFs) (x : E) : TbxRunsTo Prog.readE s [x] x (s.absorb x dsObserve) := by
  intro sp hs rest os roots
  exact ⟨_, tbx_carries_absorb hs x dsObserve, rfl⟩

/-- **A sample** squeezes. -/
theorem tbx_runsTo_sampleE (s : TbxFs) : TbxRunsTo Prog.sampleE s [] s.squeeze.1 s.squeeze.2 := by
  intro sp hs rest os roots
  obtain ⟨e1, e2⟩ := tbx_carries_squeeze hs
  refine ⟨_, e2, ?_⟩
  simp only [tbxRunId, Prog.sampleE, Compile.run, List.nil_append]
  rw [← e1]
  rfl

theorem tbx_runsTo_readN (s : TbxFs) (xs : List E) :
    TbxRunsTo (Prog.readN xs.length) s xs xs (s.absorbAll xs dsObserve) := by
  induction xs generalizing s with
  | nil => exact tbx_runsTo_ret _ _
  | cons x xs ih =>
    have h := (tbx_runsTo_readE s x).bind (f := fun x => do let xs ← Prog.readN xs.length; return x :: xs)
      ((ih (s.absorb x dsObserve)).bind (f := fun xs => (pure (x :: xs) : Prog (List E)))
        (tbx_runsTo_ret (x :: xs) _))
    simpa [Prog.readN, TbxFs.absorbAll, List.foldl] using h

theorem tbx_runsTo_sampleN (n : ℕ) (s : TbxFs) :
    TbxRunsTo (Prog.sampleN n) s [] (s.squeezeN n).1 (s.squeezeN n).2 := by
  induction n generalizing s with
  | zero => exact tbx_runsTo_ret _ _
  | succ n ih =>
    have h := (tbx_runsTo_sampleE s).bind (f := fun x => do let xs ← Prog.sampleN n; return x :: xs)
      ((ih s.squeeze.2).bind (f := fun xs => (pure (s.squeeze.1 :: xs) : Prog (List E)))
        (tbx_runsTo_ret _ _))
    simpa [Prog.sampleN, TbxFs.squeezeN] using h

/-- **A proof of work**: the nonce absorbed with `dsPowNonce`, a squeeze, and `powOk` of its
challenge. -/
theorem tbx_runsTo_grindP (bits : ℕ) (s : TbxFs) (n : E)
    (hok : powOk bits n (s.absorb n dsPowNonce).squeeze.1 = true) :
    TbxRunsTo (Prog.grindP bits) s [n] () (s.absorb n dsPowNonce).squeeze.2 := by
  intro sp hs rest os roots
  have ha := tbx_carries_absorb hs n dsPowNonce
  obtain ⟨e1, e2⟩ := tbx_carries_squeeze ha
  refine ⟨_, e2, ?_⟩
  have key : tbxRunId (Prog.grindP bits) ⟨sp, [n] ++ rest, os, roots⟩ =
      (if powOk bits n (Id.run (Compile.squeeze (m := Id) keccakF
          (Id.run (Compile.absorb (m := Id) keccakF sp n dsPowNonce)))).1 = true then
        some ((), ⟨(Id.run (Compile.squeeze (m := Id) keccakF
          (Id.run (Compile.absorb (m := Id) keccakF sp n dsPowNonce)))).2, rest, os, roots⟩)
      else none) := rfl
  rw [key, e1]
  simp only [hok, ↓reduceIte]

/-! ## Cells of waiting scalars and permutations -/

/-- The rate cells of the waiting scalars, scalar by scalar (`Keccak.scalarCells`). -/
def tbxPendCells (pend : List (E × ℕ)) : List E :=
  pend.flatMap fun p => [(Keccak.scalarCells p.1 p.2).1, (Keccak.scalarCells p.1 p.2).2]

/-- The rate cells of up to four waiting scalars: their cells, then zeros. -/
theorem tbx_rateOf_eq_cells (pend : List (E × ℕ)) (h : pend.length ≤ 4) :
    tbxRateOf pend = tbxPendCells pend ++ List.replicate (8 - 2 * pend.length) 0 := by
  match pend, h with
  | [], _ => simp [tbxRateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, tbxPendCells,
      zero_eq_ofLimbs]
  | [a], _ => simp [tbxRateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, tbxPendCells,
      Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b], _ => simp [tbxRateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes, tbxPendCells,
      Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b, c], _ => simp [tbxRateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      tbxPendCells, Keccak.scalarCells, zero_eq_ofLimbs]
  | [a, b, c, d], _ => simp [tbxRateOf, List.range_succ, Keccak.rateCell, Compile.pendingLanes,
      tbxPendCells, Keccak.scalarCells]

/-- A sponge's next permutation, its cells written out. -/
theorem tbx_perm_eq_cells (s : TbxFs) (h : s.pend.length ≤ 4) :
    s.perm = tbxPermOf (tbxPendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap) := by
  rw [TbxFs.perm, tbx_rateOf_eq_cells _ h]

/-- Absorbing below a full queue appends. -/
theorem tbx_absorbAll_short (s : TbxFs) (xs : List E) (t : ℕ) (h : s.pend.length + xs.length ≤ 4) :
    s.absorbAll xs t = ⟨s.cap, s.pend ++ xs.map (·, t)⟩ := by
  induction xs generalizing s with
  | nil => simp [TbxFs.absorbAll]
  | cons x xs ih =>
    simp only [List.length_cons] at h
    have hl : s.pend.length ≠ rateScalars := by unfold rateScalars; omega
    simp only [TbxFs.absorbAll, List.foldl_cons] at ih ⊢
    rw [show s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ by simp [TbxFs.absorb, hl],
      ih _ (by simp; omega)]
    simp

/-- The cells of a `KECCAK` atom's outputs, one by one. -/
theorem tbx_outs_eq {σ : Val} {outs : List V} {f : Fin 13 → E}
    (h : cells13 (outs.map σ) = f) (k : Fin 13) (hk : k.val < outs.length) :
    σ outs[k.val] = f k := by
  rw [← h]
  simp [cells13, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]



variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## `fs_pack` -/

/-- `fs_pack(rate, k, x, tag)`'s atoms from the value `b`: the hinted limbs `b .. b + 2`, the tag
`b + 3`, `y²` at `b + 4`, `y²·x₂` at `b + 5`, the cells `b + 6`, `b + 8` (`y·tag` at `b + 7`). -/
def tbxFsPackT (x : V) (b t : ℕ) : List Stmt :=
  [.atom (.hint (.limbs x [.n b, .n (b + 1), .n (b + 2)])),
    .atom (.const (.n (b + 3)) (word t 0 0)),
    .atom (.assertInK (.n (b + 2)) (.n (b + 3))),
    .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n (b + 2))),
    .atom (.add (.n (b + 6)) x (.n (b + 5))),
    .atom (.const (.n (b + 7)) (word 0 t 0)),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7)))]

/-- What `tbxFsPackT` asks of a valuation. -/
def TbxFsPackOk (σ : Val) (x : V) (b t : ℕ) : Prop :=
  σ (.n (b + 3)) = word t 0 0 ∧ IsInK (σ (.n (b + 2))) ∧ IsInK (σ (.n (b + 3))) ∧
    σ (.n (b + 4)) = word 0 0 1 ∧ σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 2)) ∧
    σ (.n (b + 6)) = σ x + σ (.n (b + 5)) ∧ σ (.n (b + 7)) = word 0 t 0 ∧
    σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7))

theorem tbx_holds_fsPackT (x : V) (b t : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (tbxFsPackT x b t) next kret ↔ TbxFsPackOk σ x b t ∧ next := by
  simp only [tbxFsPackT, TbxFsPackOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_assoc]

/-- **`fs_pack`'s cells** (G:551-559): once its first cell is canonical, the two cells are the
scalar's rate cells `Keccak.scalarCells x t`. -/
theorem tbx_fsPackT_cells {x : V} {b t : ℕ} (h : TbxFsPackOk σ x b t)
    (hcan : IsCanonical128 (σ (.n (b + 6)))) :
    (σ (.n (b + 6)), σ (.n (b + 8))) = Keccak.scalarCells (σ x) t := by
  obtain ⟨-, h2, -, h4, h5, h6, h7, h8⟩ := h
  have e6 : σ (.n (b + 6)) = σ x + y * y * σ (.n (b + 2)) := by rw [h6, h5, h4, tbx_word_yy]
  have e8 : σ (.n (b + 8)) = σ (.n (b + 2)) + y * eOfNat t := by rw [h8, h7, tbx_word_y_mul]
  rw [e6] at hcan ⊢
  rw [e8]
  exact (Keccak.fsPack_cells (σ x) (σ (.n (b + 2))) t h2 hcan).2

/-- The honest values of `tbxFsPackT` on the word `x`: its three limbs, then the constants and
cells. -/
def tbxFsPackVals (x : E) (t : ℕ) : ℕ → E
  | 0 => ofK (x.limb 0)
  | 1 => ofK (x.limb 1)
  | 2 => ofK (x.limb 2)
  | 3 => word t 0 0
  | 4 => word 0 0 1
  | 5 => word 0 0 1 * ofK (x.limb 2)
  | 6 => x + word 0 0 1 * ofK (x.limb 2)
  | 7 => word 0 t 0
  | _ => ofK (x.limb 2) + word 0 t 0

theorem tbx_fsPackOk_of_vals {x : V} {b t : ℕ} (h : ∀ i < 9, σ (.n (b + i)) = tbxFsPackVals (σ x) t i) :
    TbxFsPackOk σ x b t := by
  have e : ∀ i, i < 9 → σ (.n (b + i)) = tbxFsPackVals (σ x) t i := h
  refine ⟨e 3 (by omega), ?_, ?_, e 4 (by omega), ?_, ?_, e 7 (by omega), ?_⟩
  · rw [e 2 (by omega)]; exact ofK_isInK _
  · rw [e 3 (by omega)]; show IsInK (word t 0 0); rw [tb_word_eOfNat]; exact eOfNat_isInK _
  · rw [e 5 (by omega), e 4 (by omega), e 2 (by omega)]; rfl
  · rw [e 6 (by omega), e 5 (by omega)]; rfl
  · rw [e 8 (by omega), e 2 (by omega), e 7 (by omega)]; rfl

/-- The honest cells are the scalar's rate cells. -/
theorem tbx_fsPackVals_cells (x : E) (t : ℕ) :
    (tbxFsPackVals x t 6, tbxFsPackVals x t 8) = Keccak.scalarCells x t := by
  have hc : IsCanonical128 (x + y * y * ofK (x.limb 2)) := by
    rw [top_pin_eq]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have := (Keccak.fsPack_cells x (ofK (x.limb 2)) t (ofK_isInK _) hc).2
  simp only [tbxFsPackVals, tbx_word_yy, tbx_word_y_mul]
  exact this

/-- The scalar's rate cells are canonical. -/
theorem tbx_scalarCells_canonical (x : E) (t : ℕ) :
    IsCanonical128 (Keccak.scalarCells x t).1 ∧ IsCanonical128 (Keccak.scalarCells x t).2 :=
  ⟨(isCanonical128_ofLimbs_iff _ _ _).mpr rfl, (isCanonical128_ofLimbs_iff _ _ _).mpr rfl⟩

/-- The honest cells are canonical. -/
theorem tbx_fsPackVals_canonical (x : E) (t : ℕ) :
    IsCanonical128 (tbxFsPackVals x t 6) ∧ IsCanonical128 (tbxFsPackVals x t 8) := by
  have h := tbx_fsPackVals_cells x t
  simp only [Prod.ext_iff] at h
  rw [h.1, h.2]
  exact tbx_scalarCells_canonical x t

/-! ## `fs_next` -/

/-- `fs_next(rate, k, cursor)`'s atoms from the value `b`: the word at `cur·g^off` into `b`, then
`fs_pack` of it with the tag `DS_OBSERVE = 1`, its cells `b + 7`, `b + 9`. -/
def tbxFsNextT (cur : V) (off b : ℕ) : List Stmt :=
  .atom (.load (.n b) cur off) :: tbxFsPackT (.n b) (b + 1) dsObserve

theorem tbx_holds_fsNextT (cur : V) (off b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (tbxFsNextT cur off b) next kret ↔
      (LoadHolds rd (σ cur) off (σ (.n b)) ∧ TbxFsPackOk σ (.n b) (b + 1) dsObserve) ∧ next := by
  rw [tbxFsNextT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, tbx_holds_fsPackT, and_assoc]

/-! ## `challenge_from_state` -/

/-- `challenge_from_state(state)`'s atoms from the value `b`, on the state's cells `s0`, `s1`:
the hinted low limb `b`, the derived high limb `b + 3`, the challenge `b + 6`. -/
def tbxChallengeT (s0 s1 : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs s1 [.n b])),
    .atom (.add (.n (b + 1)) s1 (.n b)),
    .atom (.const (.n (b + 2)) (word 1 0 1)),
    .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3))),
    .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n b)),
    .atom (.add (.n (b + 6)) s0 (.n (b + 5)))]

/-- What `tbxChallengeT` asks of a valuation. -/
def TbxChallengeOk (σ : Val) (s0 s1 : V) (b : ℕ) : Prop :=
  σ (.n (b + 1)) = σ s1 + σ (.n b) ∧ σ (.n (b + 2)) = word 1 0 1 ∧
    σ (.n (b + 3)) = σ (.n (b + 1)) * σ (.n (b + 2)) ∧ IsInK (σ (.n b)) ∧
    IsInK (σ (.n (b + 3))) ∧ σ (.n (b + 4)) = word 0 0 1 ∧
    σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n b) ∧ σ (.n (b + 6)) = σ s0 + σ (.n (b + 5))

theorem tbx_holds_challengeT (s0 s1 : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (tbxChallengeT s0 s1 b) next kret ↔ TbxChallengeOk σ s0 s1 b ∧ next := by
  simp only [tbxChallengeT, TbxChallengeOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_assoc]

/-- **`challenge_from_state`** (G:528-538): on the cells `0`, `1` of a state, the template's
challenge is `challengeOf` of the state. -/
theorem tbx_challengeT_value {s0 s1 : V} {b : ℕ} {S : KState} (h : TbxChallengeOk σ s0 s1 b)
    (h0 : σ s0 = cellsOfState S false 0) (h1 : σ s1 = cellsOfState S false 1) :
    σ (.n (b + 6)) = challengeOf S := by
  obtain ⟨e1, e2, e3, hk, hk3, e4, e5, e6⟩ := h
  have hsplit := (split_iff (σ s1) (σ (.n b))).mp ⟨hk, by rw [← tbx_word_y_inv, ← e2, ← e1, ← e3]; exact hk3⟩
  rw [e6, e5, e4, tbx_word_yy, hsplit.2, h0, h1, Keccak.challengeOf_cells]

/-- The honest values of `tbxChallengeT` on the cell `s1` (`s0 + …` the challenge). -/
def tbxChallengeVals (s0 s1 : E) : ℕ → E
  | 0 => ofK (s1.limb 0)
  | 1 => s1 + ofK (s1.limb 0)
  | 2 => word 1 0 1
  | 3 => (s1 + ofK (s1.limb 0)) * word 1 0 1
  | 4 => word 0 0 1
  | 5 => word 0 0 1 * ofK (s1.limb 0)
  | _ => s0 + word 0 0 1 * ofK (s1.limb 0)

theorem tbx_challengeOk_of_vals {s0 s1 : V} {b : ℕ} (hc : IsCanonical128 (σ s1))
    (h : ∀ i < 7, σ (.n (b + i)) = tbxChallengeVals (σ s0) (σ s1) i) : TbxChallengeOk σ s0 s1 b := by
  have e : ∀ i, i < 7 → σ (.n (b + i)) = tbxChallengeVals (σ s0) (σ s1) i := h
  have e0 : σ (.n b) = ofK ((σ s1).limb 0) := e 0 (by omega)
  have hhi := (split_iff (σ s1) (σ (.n b))).mpr ⟨hc, e0⟩
  refine ⟨?_, e 2 (by omega), ?_, hhi.1, ?_, e 4 (by omega), ?_, ?_⟩
  · rw [e 1 (by omega), e0]; rfl
  · rw [e 3 (by omega), e 1 (by omega), e 2 (by omega)]; rfl
  · rw [e 3 (by omega)]; show IsInK ((σ s1 + ofK ((σ s1).limb 0)) * word 1 0 1)
    rw [tbx_word_y_inv, ← e0]; exact hhi.2
  · rw [e 5 (by omega), e 4 (by omega), e0]; rfl
  · rw [e 6 (by omega), e 5 (by omega)]; rfl

/-- A state's cells are canonical. -/
theorem tbx_cellsOfState_canonical (S : KState) (odd : Bool) (c : Fin 13) :
    IsCanonical128 (cellsOfState S odd c) := (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- The honest challenge is the state's. -/
theorem tbx_challengeVals_six (S : KState) :
    tbxChallengeVals (cellsOfState S false 0) (cellsOfState S false 1) 6 = challengeOf S := by
  rw [Keccak.challengeOf_cells]
  simp [tbxChallengeVals, tbx_word_yy]

/-! ## One permutation -/

/-- One `KECCAK` atom in the even layouts. -/
def tbxKeccakA (ins outs : List V) : Stmt := .atom (.keccak ins outs false false)

/-- **A permutation** (`fs_perm`, `fs_perm4`, `fs_perm_pending`, G:563-605): a `KECCAK` atom in
the even layouts reads canonical cells and writes the cells of `tbxPermOf` of them. -/
theorem tbx_keccakA_perm {ins outs : List V} (h : (Atom.keccak ins outs false false).Holds rd σ) :
    ins.length = 13 ∧ outs.length = 13 ∧ TbxAllCanonical (ins.map σ) ∧
      cells13 (outs.map σ) = cellsOfState (tbxPermOf (ins.map σ)) false := by
  obtain ⟨hi, ho, hK⟩ := h
  refine ⟨hi, ho, fun c hc => ?_, funext hK.2⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  have := hK.1 ⟨k, by simpa [hi] using hk⟩
  simpa [cells13, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this


end
end LeanVM.Guest.B1.Tables
