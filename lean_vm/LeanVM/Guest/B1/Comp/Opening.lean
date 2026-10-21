/-
  LeanVM.Guest.B1.Comp.Opening

  `opening_final_message(n)` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.Opening

/-!
# `opening_final_message` over a completeness model

The backward half of `opening_final_message_iff` over a `CompModel`: from the meaning over the
model's answers (`MeaningOpeningFinalMessageComp CM n`: the `n` words read, every absorb
answered), the run is taken apart into its answered absorbs (`obsAllM_obsAt`), whose states
(`obsAt`) are the honest values in place of the deployed `cvAt`, each block's row the model's
(`holdsB_fsNextT_comp`). `opening_final_message_comp` and its four specializations
(`opening_final_message_L{4,8,16,32}_comp`); at `CompModel.deployed` the deployed backward
direction (`opening_final_message_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Blocks without a return, one per index below `n`, hold under `S` exactly when each does
(`holdsList_range_flatten`). -/
theorem range_flatten_holdsListB {S : BlakeSem} (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsListB S C rd σ (blk i) True kret) ∧ next := by
  rw [holdsListB_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- A forward branch whose blocks have no `ret` holds under `S`, then its continuation
(`holds_ite_noRet`). -/
theorem ite_holdsB_noRet {S : BlakeSem} (c : V) (z n : List Stmt) (hz : Stmt.noRetList z = true)
    (hn : Stmt.noRetList n = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsListB S C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsListB S C rd σ n True kret)) ∧ next := by
  rw [holdsB_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

/-- **`readN` in an answered run, whole**: the run reads its words, every absorb answered. -/
theorem RunsToM.readN_obsAll {M : HashModel} {n : ℕ} {cv cv' : Digest} {xs ys : List E}
    (hn : xs.length = n) (h : RunsToM M (Prog.readN n) cv xs ys cv') :
    ys = xs ∧ obsAllM M cv xs = some cv' := by
  rw [← Prog.bind_ret (Prog.readN n)] at h
  obtain ⟨c, hc, h⟩ := RunsToM.readN_inv' (zs := []) hn (by simpa using h)
  obtain ⟨-, rfl, rfl⟩ := h.ret_inv
  exact ⟨rfl, hc⟩

/-- Block `i` of `opening_final_message` under a completeness model, backward (`holds_ofmBlock`). -/
theorem holdsB_ofmBlock_comp {CM : CompModel} (i : ℕ) (kret : List E → Prop)
    (h : LoadHolds rd (σ (.n 2)) i (σ (.n (6 + 15 * i))) ∧
      (∃ cv d, (σ (.n (4 + 15 * i)), σ (.n (5 + 15 * i))) = digestScalars cv ∧
        obsCvM CM.hm cv (σ (.n (6 + 15 * i))) = some d ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (6 + 15 * i + 1 + k)) = fsValsD (σ (.n (6 + 15 * i))) d 1 k) ∧
      LoadHolds rd (σ (.n 3)) i (σ (.n (6 + 15 * i)))) :
    Stmt.HoldsListB CM.sem C rd σ (ofmBlock i) True kret := by
  obtain ⟨hl, ⟨cv, d, hcv, hd, e⟩, hl'⟩ := h
  rw [ofmBlock, holdsListB_append]
  exact holdsB_fsNextT_comp _ _ _ _ _ ⟨⟨hl, cv, d, hcv, hd, e⟩, hl', trivial⟩

/-- **`opening_final_message(n)` over a completeness model** (`MeaningOpeningFinalMessage`, the
absorbs answered by the model). -/
def MeaningOpeningFinalMessageComp (CM : CompModel) (n : ℕ) (rd : Reader) :
    List E → List E → Prop
  | [s0, s1, cur, out], rets =>
      ∃ cv xs cv', (s0, s1) = digestScalars cv ∧ xs.length = n ∧ ReadsAt rd cur xs ∧
        ReadsAt rd out xs ∧ RunsToM CM.hm (Prog.readN n) cv xs xs cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ n]
  | _, _ => False

theorem meaningOpeningFinalMessageComp_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningOpeningFinalMessageComp CompModel.deployed n rd args rets ↔
      MeaningOpeningFinalMessage n rd args rets := by
  unfold MeaningOpeningFinalMessageComp MeaningOpeningFinalMessage
  split <;> try simp only [runsToM_hm_deployed]

/-- The honest valuation over a model, block by block (`ofmSig` with the answered states). -/
noncomputable def ofmSigC (M : HashModel) (base : Val) (cv : Digest) (xs : List E) : ℕ → Val
  | 0 => setl base 4 [(digestScalars cv).1, (digestScalars cv).2]
  | i + 1 => setv (setl (ofmSigC M base cv xs i) (6 + 15 * i) [xs.getD i 0]) (7 + 15 * i) 14
      (fsValsD (xs.getD i 0) (obsAt M cv xs (i + 1)) 1)

section
variable (M : HashModel)

theorem ofmSigC_lt (base : Val) (cv : Digest) (xs : List E) :
    ∀ (m i k : ℕ), i ≤ m → k < 6 + 15 * i →
      ofmSigC M base cv xs m (.n k) = ofmSigC M base cv xs i (.n k)
  | 0, i, k, h, _ => by rw [show i = 0 by omega]
  | m + 1, i, k, h, hk => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [ofmSigC, set_n_lt (by omega), setl, set_n_lt (by omega)]
      exact ofmSigC_lt base cv xs m i k (by omega) hk
    · rw [show i = m + 1 by omega]

theorem ofmSigC_base (base : Val) (cv : Digest) (xs : List E) (m k : ℕ) (hk : k < 4) :
    ofmSigC M base cv xs m (.n k) = base (.n k) := by
  rw [ofmSigC_lt M base cv xs m 0 k (by omega) (by omega), ofmSigC, setl, set_n_lt hk]

theorem ofmSigC_state (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i ≤ m) :
    ofmSigC M base cv xs m (.n (4 + 15 * i)) = (digestScalars (obsAt M cv xs i)).1 ∧
      ofmSigC M base cv xs m (.n (5 + 15 * i)) = (digestScalars (obsAt M cv xs i)).2 := by
  rw [ofmSigC_lt M base cv xs m i _ hi (by omega), ofmSigC_lt M base cv xs m i _ hi (by omega)]
  cases i with
  | zero =>
    simp only [ofmSigC, setl, List.length_cons, List.length_nil]
    rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  | succ i =>
    rw [ofmSigC, set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show 4 + 15 * (i + 1) - (7 + 15 * i) = 12 by omega,
      show 5 + 15 * (i + 1) - (7 + 15 * i) = 13 by omega]
    exact ⟨rfl, rfl⟩

theorem ofmSigC_block (base : Val) (cv : Digest) (xs : List E) (m i : ℕ) (hi : i < m) :
    ofmSigC M base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 ∧
      ∀ k, 2 ≤ k → k < 14 → ofmSigC M base cv xs m (.n (6 + 15 * i + 1 + k)) =
        fsValsD (xs.getD i 0) (obsAt M cv xs (i + 1)) 1 k := by
  have hw : ofmSigC M base cv xs m (.n (6 + 15 * i)) = xs.getD i 0 := by
    rw [ofmSigC_lt M base cv xs m (i + 1) _ hi (by omega), ofmSigC, set_n_lt (by omega), setl,
      set_n_in (by omega) (by simp), Nat.sub_self]
    rfl
  refine ⟨hw, fun k hk1 hk2 => ?_⟩
  rw [ofmSigC_lt M base cv xs m (i + 1) _ hi (by omega), ofmSigC, set_n_in (by omega) (by omega),
    show 6 + 15 * i + 1 + k - (7 + 15 * i) = k by omega]

end

/-- **`opening_final_message` at every `0 < n < 64` is complete over a completeness model**, for a
compiled function whose body is `ofmBody n`. -/
theorem opening_final_message_comp {CM : CompModel} {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hn64 : n < 64) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = ofmBody n) (rd : Reader)
    (args rets : List E) (hm : MeaningOpeningFinalMessageComp CM n rd args rets) :
    coreProgram.RelB CM.sem rd name args rets := by
  obtain ⟨s0, s1, cur, out, rfl⟩ : ∃ s0 s1 cur out, args = [s0, s1, cur, out] := by
    match args, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨cv, xs, cv', hcv, hlen, hcur, hout, hrun, hret⟩ := hm
  obtain ⟨-, hall⟩ := hrun.readN_obsAll hlen
  obtain ⟨hsteps, rfl⟩ := obsAllM_obsAt hall
  subst hret
  rw [relB_iff_sem hfind, hbody, hparams, ofmBody]
  simp only [holdsListB_append, range_flatten_holdsListB n ofmBlock (fun _ => rfl), ofmTail,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil]
  set M := CM.hm
  set base := Val.ofArgs [s0, s1, cur, out]
  set τ := setl (ofmSigC M base cv xs n) (6 + 15 * n)
    [(digestScalars (obsAt M cv xs n)).1, (digestScalars (obsAt M cv xs n)).2, word (2 ^ n) 0 0,
      cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0]
  have hτ : ∀ k < 6 + 15 * n, τ (.n k) = ofmSigC M base cv xs n (.n k) := fun k hk => by
    simp only [τ, setl]; rw [set_n_lt hk]
  have hbase : ∀ k < 4, τ (.n k) = base (.n k) := fun k hk => by
    rw [hτ k (by omega), ofmSigC_base _ _ _ _ _ _ hk]
  obtain ⟨hs0, hs1⟩ := ofmSigC_state M base cv xs n n le_rfl
  refine ⟨τ, ?_, ?_, ?_, ?blk, ?tail⟩
  · simp only [hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega), hbase 3 (by omega)]
    rfl
  · rw [hτ 4 (by omega), hbase 0 (by omega)]
    have := (ofmSigC_state M base cv xs n 0 (by omega)).1
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [this]
    exact (congrArg Prod.fst hcv).symm
  · rw [hτ 5 (by omega), hbase 1 (by omega)]
    have := (ofmSigC_state M base cv xs n 0 (by omega)).2
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [this]
    exact (congrArg Prod.snd hcv).symm
  case blk =>
    intro i hi
    obtain ⟨hw, hv⟩ := ofmSigC_block M base cv xs n i hi
    obtain ⟨hst0, hst1⟩ := ofmSigC_state M base cv xs n i (by omega)
    have hi' : i < xs.length := hlen ▸ hi
    have hx : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD, hi']
    refine holdsB_ofmBlock_comp i _ ⟨?_, ⟨obsAt M cv xs i, obsAt M cv xs (i + 1), ?_, ?_,
      fun k hk1 hk2 => ?_⟩, ?_⟩
    · rw [hbase 2 (by omega), hτ _ (by omega), hw, hx]; exact hcur i hi'
    · rw [hτ _ (by omega), hτ _ (by omega), hst0, hst1]
    · rw [hτ _ (by omega), hw]; exact hsteps i hi'
    · rw [hτ _ (by omega), hτ _ (by omega), hw, hv k hk1 hk2]
    · rw [hbase 3 (by omega), hτ _ (by omega), hw, hx]; exact hout i hi'
  case tail =>
    have hlk : ∀ j, j < 5 → τ (.n (6 + 15 * n + j)) =
        [(digestScalars (obsAt M cv xs n)).1, (digestScalars (obsAt M cv xs n)).2,
          word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0, cur * word (2 ^ n) 0 0].getD j 0 :=
      fun j hj => by
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
    have l4 : τ (.n (4 + 15 * n)) = (digestScalars (obsAt M cv xs n)).1 := by
      rw [hτ _ (by omega)]; exact hs0
    have l5 : τ (.n (5 + 15 * n)) = (digestScalars (obsAt M cv xs n)).2 := by
      rw [hτ _ (by omega)]; exact hs1
    have l2 : τ (.n 2) = cur := hbase 2 (by omega)
    refine ⟨by rw [l6, l4], by rw [l7, l5], l8, by rw [l9, l2, l8], by rw [l10, l9], ?_⟩
    rw [l6, l7, l10, word_pow_two hn64, hlen]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem opening_final_message_L4_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningFinalMessageComp CM 4 rd args rets) :
    coreProgram.RelB CM.sem rd "opening_final_message__L4" args rets :=
  opening_final_message_comp 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 616) (by decide +kernel) rfl) rfl rfl rd args rets hm

set_option maxRecDepth 100000 in
theorem opening_final_message_L8_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningFinalMessageComp CM 8 rd args rets) :
    coreProgram.RelB CM.sem rd "opening_final_message__L8" args rets :=
  opening_final_message_comp 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 631) (by decide +kernel) rfl) rfl rfl rd args rets hm

set_option maxRecDepth 100000 in
theorem opening_final_message_L16_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningFinalMessageComp CM 16 rd args rets) :
    coreProgram.RelB CM.sem rd "opening_final_message__L16" args rets :=
  opening_final_message_comp 16 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 588) (by decide +kernel) rfl) rfl rfl rd args rets hm

set_option maxRecDepth 100000 in
theorem opening_final_message_L32_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : MeaningOpeningFinalMessageComp CM 32 rd args rets) :
    coreProgram.RelB CM.sem rd "opening_final_message__L32" args rets :=
  opening_final_message_comp 32 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl rfl rd args rets hm

/-! ## At the deployed model -/

/-- The deployed backward direction of `opening_final_message_iff`, from the generic one. -/
theorem opening_final_message_of_comp {name : String} {f : Fn} (n : ℕ) (hn : 0 < n)
    (hn64 : n < 64) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = ofmBody n) (rd : Reader)
    (args rets : List E) (h : MeaningOpeningFinalMessage n rd args rets) :
    coreProgram.Rel rd name args rets := by
  rw [← relB_deployed]
  exact opening_final_message_comp (CM := CompModel.deployed) n hn hn64 hfind hparams hbody rd
    args rets ((meaningOpeningFinalMessageComp_deployed n rd args rets).mpr h)

end
end LeanVM.Guest.B1
