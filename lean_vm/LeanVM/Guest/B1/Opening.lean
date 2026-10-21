/-
  LeanVM.Guest.B1.Opening

  B1 for the stacked WHIR opening's stream gadgets: `opening_final_message` at each of its
  specializations, one generic argument over the message length.
-/

module

public import LeanVM.Guest.B1.FiatShamir

/-!
# `opening_final_message` (TRIAGE #33)

`opening_final_message(fs0, fs1, cursor, out, n)` (G:944-949) reads `n` stream words, absorbing
each (`fs_next`), and stores them at `out`: `readN n` (V:432). Its expansion is `n` blocks of
`fs_next` and a store, `ofmBlock i` at value `4 + 15·i` (the state of block `i` is
`.n (4 + 15·i)`, `.n (5 + 15·i)`, its word `.n (6 + 15·i)`), then `ofmTail n`: `ofmBody n`,
equal by `rfl` to each compiled specialization (`__L4`, `__L8`, `__L16`, `__L32`).
`opening_final_message_iff` is proved once, for every `0 < n < 64`; under a hash model,
`opening_final_message_model` (the words absorbed in order, every hash answered, `RunsToM`), from
which the deployed iff's forward direction follows.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Repeated blocks -/

/-- Blocks without a return, one per index below `n`, hold exactly when each does. -/
theorem holdsList_range_flatten (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsList C rd σ (blk i) True kret) ∧ next := by
  rw [holdsList_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- `holdsList_range_flatten` under any semantics. -/
theorem holdsListB_flatten_range {S : BlakeSem} (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsListB S C rd σ (blk i) True kret) ∧ next := by
  rw [holdsListB_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- Absorbing `xs ++ ys` over a hash model is absorbing `xs`, then `ys`. -/
theorem obsAllM_append_eq {M : HashModel} (cv : Digest) (xs ys : List E) :
    obsAllM M cv (xs ++ ys) = (obsAllM M cv xs).bind fun c ↦ obsAllM M c ys := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, obsAllM, Option.bind_assoc]
    congr 1
    funext c
    exact ih c

/-! ## The template -/

/-- Block `i`: read the word at offset `i`, absorb it, store it at `out`. -/
def ofmBlock (i : ℕ) : List Stmt :=
  fsNextT (.n (4 + 15 * i)) (.n (5 + 15 * i)) (.n 2) i (6 + 15 * i) ++
    [.atom (.load (.n (6 + 15 * i)) (.n 3) i)]

/-- The returns: the state, and the cursor `n` words on. -/
def ofmTail (n : ℕ) : List Stmt :=
  [.atom (.copy (.n (6 + 15 * n)) (.n (4 + 15 * n))), .atom (.copy (.n (7 + 15 * n)) (.n (5 + 15 * n))),
    .atom (.const (.n (8 + 15 * n)) (word (2 ^ n) 0 0)),
    .atom (.mul (.n (9 + 15 * n)) (.n 2) (.n (8 + 15 * n))),
    .atom (.copy (.n (10 + 15 * n)) (.n (9 + 15 * n))),
    .ret [.n (6 + 15 * n), .n (7 + 15 * n), .n (10 + 15 * n)]]

/-- The expansion of `opening_final_message` at `n`. -/
def ofmBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 4) (.n 0)), .atom (.copy (.n 5) (.n 1))] ++
    ((List.range n).map ofmBlock).flatten ++ ofmTail n

/-- What block `i` asks of a valuation. -/
def OfmOk (rd : Reader) (σ : Val) (i : ℕ) : Prop :=
  LoadHolds rd (σ (.n 2)) i (σ (.n (6 + 15 * i))) ∧
    (∃ cv, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n (6 + 15 * i + 1 + k)) = fsVals (σ (.n (6 + 15 * i))) cv 1 k) ∧
    LoadHolds rd (σ (.n 3)) i (σ (.n (6 + 15 * i)))

theorem holds_ofmBlock (i : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmBlock i) True kret ↔ OfmOk rd σ i := by
  rw [ofmBlock, holdsList_append, holds_fsNextT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, OfmOk]
  tauto

/-- What block `i` gives under a hash model: `OfmOk` with the absorption's hash answered. -/
def OfmOkB (M : HashModel) (rd : Reader) (σ : Val) (i : ℕ) : Prop :=
  LoadHolds rd (σ (.n 2)) i (σ (.n (6 + 15 * i))) ∧
    (∃ cv d, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) = digestScalars cv ∧
      obsCvM M cv (σ (.n (6 + 15 * i))) = some d ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n (6 + 15 * i + 1 + k)) = fsValsD (σ (.n (6 + 15 * i))) d 1 k) ∧
    LoadHolds rd (σ (.n 3)) i (σ (.n (6 + 15 * i)))

theorem holdsB_ofmBlock {M : HashModel} (i : ℕ) (kret : List E → Prop)
    (h : Stmt.HoldsListB M.sem C rd σ (ofmBlock i) True kret) : OfmOkB M rd σ i := by
  rw [ofmBlock] at h
  rw [holdsListB_append] at h
  obtain ⟨⟨hl, hcv⟩, h⟩ := holdsB_fsNextT _ _ _ _ _ h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  exact ⟨hl, hcv, h⟩

/-! ## The meaning -/

/-- **`opening_final_message(n)`** (G:944-949; TRIAGE #33): from the state of `cv`, the `n` words
`xs` at the cursor are read (`readN n`, V:432, to the state `cv'`) and stored at `out`; the
function returns `cv'`'s cells and the cursor `n` words on. -/
def MeaningOpeningFinalMessage (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, out], rets =>
      ∃ cv xs cv', (s0, s1) = digestScalars cv ∧ xs.length = n ∧ ReadsAt rd cur xs ∧
        ReadsAt rd out xs ∧ RunsTo (Prog.readN n) cv xs xs cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ n]
  | _, _ => False

/-- The states of the chain after each prefix of `xs`. -/
def cvAt (cv : Digest) (xs : List E) : ℕ → Digest
  | 0 => cv
  | i + 1 => absorbCv (cvAt cv xs i) (xs.getD i 0) 1

theorem cvAt_eq (cv : Digest) (xs : List E) (i : ℕ) (hi : i ≤ xs.length) :
    cvAt cv xs i = obsAll cv (xs.take i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [cvAt, ih (by omega), List.take_add_one]
    simp only [obsAll, List.foldl_append, List.getElem?_eq_getElem (show i < xs.length by omega),
      Option.toList_some, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD,
      Option.getD_some]
    rfl

/-- The honest valuation, block by block. -/
def ofmSig (base : Val) (cv : Digest) (xs : List E) : ℕ → Val
  | 0 => setl base 4 [(digestScalars cv).1, (digestScalars cv).2]
  | i + 1 => setv (setl (ofmSig base cv xs i) (6 + 15 * i) [xs.getD i 0]) (7 + 15 * i) 14
      (fsVals (xs.getD i 0) (cvAt cv xs i) 1)

theorem ofmSig_lt (base : Val) (cv : Digest) (xs : List E) :
    ∀ (m i k : ℕ), i ≤ m → k < 6 + 15 * i → ofmSig base cv xs m (.n k) = ofmSig base cv xs i (.n k)
  | 0, i, k, h, _ => by rw [show i = 0 by omega]
  | m + 1, i, k, h, hk => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [ofmSig, set_n_lt (by omega), setl, set_n_lt (by omega)]
      exact ofmSig_lt base cv xs m i k (by omega) hk
    · rw [show i = m + 1 by omega]

theorem ofmSig_base (base : Val) (cv : Digest) (xs : List E) (m k : ℕ) (hk : k < 4) :
    ofmSig base cv xs m (.n k) = base (.n k) := by
  rw [ofmSig_lt base cv xs m 0 k (by omega) (by omega), ofmSig, setl, set_n_lt hk]

/-- The state cells of block `i ≤ m`. -/
theorem ofmSig_state (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i ≤ m) :
    ofmSig base cv xs m (.n (4 + 15 * i)) = (digestScalars (cvAt cv xs i)).1 ∧
      ofmSig base cv xs m (.n (5 + 15 * i)) = (digestScalars (cvAt cv xs i)).2 := by
  rw [ofmSig_lt base cv xs m i _ hi (by omega), ofmSig_lt base cv xs m i _ hi (by omega)]
  cases i with
  | zero =>
    simp only [ofmSig, setl, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  | succ i =>
    rw [ofmSig, set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show 4 + 15 * (i + 1) - (7 + 15 * i) = 12 by omega,
      show 5 + 15 * (i + 1) - (7 + 15 * i) = 13 by omega]
    exact ⟨rfl, rfl⟩

/-- Block `i < m`'s word and own values. -/
theorem ofmSig_block (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i < m) :
    ofmSig base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 ∧
      ∀ k, 2 ≤ k → k < 14 → ofmSig base cv xs m (.n (6 + 15 * i + 1 + k)) =
        fsVals (xs.getD i 0) (cvAt cv xs i) 1 k := by
  have hw : ofmSig base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 := by
    rw [ofmSig_lt base cv xs m (i + 1) _ hi (by omega), ofmSig, set_n_lt (by omega), setl,
      set_n_in (by omega) (by simp), Nat.sub_self]
    rfl
  refine ⟨hw, fun k hk1 hk2 => ?_⟩
  rw [ofmSig_lt base cv xs m (i + 1) _ hi (by omega), ofmSig, set_n_in (by omega) (by omega),
    show 6 + 15 * i + 1 + k - (7 + 15 * i) = k by omega]

/-! ## The theorem -/

theorem obsAll_eq_cvAt (cv : Digest) (xs : List E) : obsAll cv xs = cvAt cv xs xs.length := by
  rw [cvAt_eq cv xs _ le_rfl, List.take_length]

theorem word_pow_two {n : ℕ} (h : n < 64) : word (2 ^ n) 0 0 = gen ^ n := word_two_pow h

/-- **`opening_final_message(n)` under a hash model** (the meaning of
`MeaningOpeningFinalMessage`, every hash answered). -/
def MeaningOpeningFinalMessageWith (M : HashModel) (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, out], rets =>
      ∃ cv xs cv', (s0, s1) = digestScalars cv ∧ xs.length = n ∧ ReadsAt rd cur xs ∧
        ReadsAt rd out xs ∧ RunsToM M (Prog.readN n) cv xs xs cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ n]
  | _, _ => False

/-- At the deployed model it is `MeaningOpeningFinalMessage`. -/
theorem meaningOpeningFinalMessageWith_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningOpeningFinalMessageWith HashModel.deployed n rd args rets ↔
      MeaningOpeningFinalMessage n rd args rets := by
  unfold MeaningOpeningFinalMessageWith MeaningOpeningFinalMessage
  split <;> try simp only [runsToM_deployed]

/-- **`opening_final_message` is sound under a hash model**, at every `0 < n < 64`, for a
compiled function whose body is `ofmBody n`: the words read are absorbed in order, every hash
answered. -/
theorem opening_final_message_model {M : HashModel} {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hn64 : n < 64) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = ofmBody n) (rd : Reader)
    (args rets : List E) (h : coreProgram.RelB M.sem rd name args rets) :
    MeaningOpeningFinalMessageWith M n rd args rets := by
  rw [relB_iff_sem hfind, hbody, hparams, ofmBody] at h
  simp only [holdsListB_append, holdsListB_flatten_range n ofmBlock (fun _ => rfl), ofmTail,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h4, h5, ⟨hblk, t1, t2, t3, t4, t5, hret⟩⟩ := h
  subst hp
  have hblk : ∀ i < n, OfmOkB M rd σ i := fun i hi ↦ holdsB_ofmBlock i _ (hblk i hi)
  set xs := (List.range n).map fun i => σ (.n (6 + 15 * i))
  have hlen : xs.length = n := by simp [xs]
  have hxs : ∀ i < n, xs.take (i + 1) = xs.take i ++ [σ (.n (6 + 15 * i))] := fun i hi => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp [xs]
  obtain ⟨cv, -, hcv, -⟩ := (hblk 0 hn).2.1
  simp only [Nat.mul_zero, Nat.add_zero] at hcv
  have hst : ∀ i ≤ n, ∃ d, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) = digestScalars d ∧
      obsAllM M cv (xs.take i) = some d := by
    intro i hi
    induction i with
    | zero => exact ⟨cv, hcv, rfl⟩
    | succ i ih =>
      obtain ⟨d, hd, hrun⟩ := ih (by omega)
      obtain ⟨-, ⟨cvi, di, hcvi, hdi, e⟩, -⟩ := hblk i (by omega)
      obtain rfl : cvi = d := digestScalars_injective (hcvi.symm.trans hd)
      have e12 : σ (.n (4 + 15 * (i + 1))) = (digestScalars di).1 := by
        rw [show 4 + 15 * (i + 1) = 6 + 15 * i + 1 + 12 by ring]; exact e 12 (by omega) (by omega)
      have e13 : σ (.n (5 + 15 * (i + 1))) = (digestScalars di).2 := by
        rw [show 5 + 15 * (i + 1) = 6 + 15 * i + 1 + 13 by ring]; exact e 13 (by omega) (by omega)
      refine ⟨di, by rw [e12, e13], ?_⟩
      rw [hxs i (by omega), obsAllM_append_eq, hrun]
      simp [obsAllM, hdi]
  obtain ⟨d, hd, hrun⟩ := hst n le_rfl
  rw [← hlen, List.take_length] at hrun
  rw [h4, h5] at hcv
  have hr : RunsToM M (Prog.readN n) cv xs xs d := by
    have := runsToM_readN hrun; rwa [hlen] at this
  refine ⟨cv, xs, d, hcv, hlen, fun k hk => ?_, fun k hk => ?_, hr, ?_⟩
  · have hk' : k < n := hlen ▸ hk
    have := (hblk k hk').1
    simpa [xs] using this
  · have hk' : k < n := hlen ▸ hk
    have := (hblk k hk').2.2
    simpa [xs] using this
  · rw [← hret, t1, t2, t5, t4, t3, word_pow_two hn64, ← hd]

/-- **`opening_final_message` at every `0 < n < 64`**, for a compiled function whose body is
`ofmBody n`. -/
theorem opening_final_message_iff {name : String} {f : Fn} (n : ℕ) (hn : 0 < n) (hn64 : n < 64)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1, .n 2, .n 3])
    (hbody : f.body = ofmBody n) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningOpeningFinalMessage n rd args rets := by
  constructor
  · intro h
    rw [← relB_deployed] at h
    exact (meaningOpeningFinalMessageWith_deployed n rd args rets).mp
      (opening_final_message_model (M := HashModel.deployed) n hn hn64 hfind hparams hbody rd
        args rets h)
  rw [rel_iff_sem hfind, hbody, hparams, ofmBody]
  simp only [holdsList_append, holdsList_range_flatten n ofmBlock (fun _ => rfl), holds_ofmBlock, ofmTail, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil]
  · intro hm
    obtain ⟨s0, s1, cur, out, rfl⟩ : ∃ s0 s1 cur out, args = [s0, s1, cur, out] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨cv, xs, cv', hcv, hlen, hcur, hout, hrun, hret⟩ := hm
    obtain ⟨-, rfl⟩ := (runsTo_readN cv xs).iff.mp (hlen ▸ hrun)
    subst hret
    set base := Val.ofArgs [s0, s1, cur, out]
    set τ := setl (ofmSig base cv xs n) (6 + 15 * n)
      [(digestScalars (cvAt cv xs n)).1, (digestScalars (cvAt cv xs n)).2, word (2 ^ n) 0 0,
        cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0]
    have hτ : ∀ k < 6 + 15 * n, τ (.n k) = ofmSig base cv xs n (.n k) := fun k hk => by
      simp only [τ, setl]; rw [set_n_lt hk]
    have hbase : ∀ k < 4, τ (.n k) = base (.n k) := fun k hk => by
      rw [hτ k (by omega), ofmSig_base _ _ _ _ _ hk]
    obtain ⟨hs0, hs1⟩ := ofmSig_state base cv xs n n le_rfl
    refine ⟨τ, ?_, ?_, ?_, ?blk, ?tail⟩
    · simp only [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega)]
      rfl
    · rw [hτ 4 (by omega), hbase 0 (by omega)]
      have := (ofmSig_state base cv xs n 0 (by omega)).1
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      exact (congrArg Prod.fst hcv).symm
    · rw [hτ 5 (by omega), hbase 1 (by omega)]
      have := (ofmSig_state base cv xs n 0 (by omega)).2
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this]
      exact (congrArg Prod.snd hcv).symm
    case blk =>
      intro i hi
      obtain ⟨hw, hv⟩ := ofmSig_block base cv xs n i hi
      obtain ⟨hst0, hst1⟩ := ofmSig_state base cv xs n i (by omega)
      have hi' : i < xs.length := hlen ▸ hi
      have hx : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD, hi']
      refine ⟨?_, ⟨cvAt cv xs i, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
      · rw [hbase 2 (by omega), hτ _ (by omega), hw, hx]; exact hcur i hi'
      · rw [hτ _ (by omega), hτ _ (by omega), hst0, hst1]
      · rw [hτ _ (by omega), hτ _ (by omega), hw, hv k hk1 hk2]
      · rw [hbase 3 (by omega), hτ _ (by omega), hw, hx]; exact hout i hi'
    case tail =>
      have hlk : ∀ j, j < 5 → τ (.n (6 + 15 * n + j)) =
          [(digestScalars (cvAt cv xs n)).1, (digestScalars (cvAt cv xs n)).2, word (2 ^ n) 0 0,
            cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0].getD j 0 := fun j hj => by
        simp only [τ, setl]
        rw [set_n_in (by omega) (by simp only [List.length_cons, List.length_nil]; omega),
          Nat.add_sub_cancel_left]
      have l6 := hlk 0 (by omega)
      have l7 := hlk 1 (by omega)
      have l8 := hlk 2 (by omega)
      have l9 := hlk 3 (by omega)
      have l10 := hlk 4 (by omega)
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
        show 6 + 15 * n + 1 = 7 + 15 * n by omega, show 6 + 15 * n + 2 = 8 + 15 * n by omega,
        show 6 + 15 * n + 3 = 9 + 15 * n by omega, show 6 + 15 * n + 4 = 10 + 15 * n by omega]
        at l6 l7 l8 l9 l10
      have l4 : τ (.n (4 + 15 * n)) = (digestScalars (cvAt cv xs n)).1 := by
        rw [hτ _ (by omega)]; exact hs0
      have l5 : τ (.n (5 + 15 * n)) = (digestScalars (cvAt cv xs n)).2 := by
        rw [hτ _ (by omega)]; exact hs1
      have l2 : τ (.n 2) = cur := hbase 2 (by omega)
      refine ⟨by rw [l6, l4], by rw [l7, l5], l8, by rw [l9, l2, l8], by rw [l10, l9], ?_⟩
      rw [l6, l7, l10, word_pow_two hn64, obsAll_eq_cvAt, hlen]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem opening_final_message_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L4" args rets ↔
      MeaningOpeningFinalMessage 4 rd args rets :=
  opening_final_message_iff 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L8" args rets ↔
      MeaningOpeningFinalMessage 8 rd args rets :=
  opening_final_message_iff 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L16" args rets ↔
      MeaningOpeningFinalMessage 16 rd args rets :=
  opening_final_message_iff 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
theorem opening_final_message_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L32" args rets ↔
      MeaningOpeningFinalMessage 32 rd args rets :=
  opening_final_message_iff 32 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl rfl rd args rets

set_option maxRecDepth 100000 in
/-- `opening_final_message__L4` under a hash model. -/
theorem opening_final_message_L4_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "opening_final_message__L4" args rets) :
    MeaningOpeningFinalMessageWith M 4 rd args rets :=
  opening_final_message_model 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl) rfl rfl rd args rets h

set_option maxRecDepth 100000 in
/-- `opening_final_message__L8` under a hash model. -/
theorem opening_final_message_L8_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "opening_final_message__L8" args rets) :
    MeaningOpeningFinalMessageWith M 8 rd args rets :=
  opening_final_message_model 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl) rfl rfl rd args rets h

set_option maxRecDepth 100000 in
/-- `opening_final_message__L16` under a hash model. -/
theorem opening_final_message_L16_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "opening_final_message__L16" args rets) :
    MeaningOpeningFinalMessageWith M 16 rd args rets :=
  opening_final_message_model 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl) rfl rfl rd args rets h

set_option maxRecDepth 100000 in
/-- `opening_final_message__L32` under a hash model. -/
theorem opening_final_message_L32_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "opening_final_message__L32" args rets) :
    MeaningOpeningFinalMessageWith M 32 rd args rets :=
  opening_final_message_model 32 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl rfl rd args rets h

end
end LeanVM.Guest.B1
