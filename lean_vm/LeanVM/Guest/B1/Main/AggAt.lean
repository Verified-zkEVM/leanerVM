/-
  LeanVM.Guest.B1.Main.AggAt

  `aggregate_claims` in the uniform placed form: its eight buffers after its frame, holding the
  words an honest run leaves, its callees after them; it reads the children's words and writes the
  batching's claim among its caller's words.
-/

module

public import LeanVM.Guest.B1.Main.AggComplete
public import LeanVM.Guest.B1.Da.AtBase

/-!
# `aggregate_claims`, placed

At `fp`, `aggregate_claims` allocates from `b0 = fp + fs "aggregate_claims"` the rounds' words
(`46`), the tables of the children's fresh and carried claims (`m` each), the absorbing rows
(`13(m+1)`), the lambdas (`2m`), the squeezing rows (`14(m+1)`), the sumcheck's point (`23`) and
the weights (`m+1`) (`aggSizes`), holding `aggConts` (`aggOwn`); its callees follow in call order:
`__loop24`, `__loop25`, `batch_sumcheck__L23`, `__loop26`, which place nothing (`aggPure`). Its
valuation is `agg_core`'s at the allocator's buffers (`aggPtrsAt`).
`aggregate_claims_completeAt`: `aggregate_claims` is `CompleteAtD`, reading the children's words
and the batching's claim at `g^ds` among the caller's words `Lin`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL Within
  disj_append disj_nil kidsFromIn_of_kidsD completeAt_of_rel_pureD regionsOk_of within_append
  bufL bufL_within bufL_disj bufL_region)

@[expose] public section

/-! ## The buffers -/

/-- `aggregate_claims`' `HeapBuf` sizes, in allocation order. -/
def aggSizes (m : ℕ) : List ℕ := [46, m, m, 13 * (m + 1), 2 * m, 14 * (m + 1), 23, m + 1]

/-- The buffers' first words. -/
def axLf (b0 : ℕ) : ℕ := b0 + 46
def axLc (m b0 : ℕ) : ℕ := axLf b0 + m
def axAbs (m b0 : ℕ) : ℕ := axLc m b0 + m
def axLam (m b0 : ℕ) : ℕ := axAbs m b0 + 13 * (m + 1)
def axSq (m b0 : ℕ) : ℕ := axLam m b0 + 2 * m
def axPt (m b0 : ℕ) : ℕ := axSq m b0 + 14 * (m + 1)
def axW (m b0 : ℕ) : ℕ := axPt m b0 + 23

/-- `aggregate_claims`' pointers at its buffers. -/
def aggPtrsAt (m b0 : ℕ) : AggPtrs :=
  ⟨gen ^ b0, gen ^ axLf b0, gen ^ axLc m b0, gen ^ axAbs m b0, gen ^ axLam m b0, gen ^ axSq m b0,
    gen ^ axPt m b0, gen ^ axW m b0⟩

/-- **The words an honest run leaves in `aggregate_claims`' buffers.** -/
def aggConts (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchHints) :
    List (List E) :=
  [h.bytecodeRounds.flatMap (fun g => [g.1, g.2]),
    (List.range m).map (fun c => cfresh * (gen ^ c) ^ 24),
    (List.range m).map (fun c => ccarried * (gen ^ c) ^ 24),
    (List.range (m + 1)).flatMap (fun c => rowW (absSt m cs c)),
    (List.range m).flatMap (fun c => [(lamOf (aggAbs cs) c).1, (lamOf (aggAbs cs) c).2]),
    (List.range (m + 1)).flatMap (fun c => rowW (sq2F c (aggAbs cs)).2 ++ [claimAt cs c]),
    (aggRun cs h).1.1,
    (List.range (m + 1)).map (weightAt cs h)]

/-- **`aggregate_claims`' own buffers' layout.** -/
def aggOwn (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchHints) (b0 : ℕ) :
    Main.Layout :=
  bufL b0 (aggSizes m) (aggConts m cfresh ccarried cs h)

theorem aggOwn_eq (m : ℕ) (cfresh ccarried : E) (cs : List ChildClaims) (h : BatchHints) (b0 : ℕ) :
    aggOwn m cfresh ccarried cs h b0 =
      [(b0, h.bytecodeRounds.flatMap (fun g => [g.1, g.2])),
        (axLf b0, (List.range m).map (fun c => cfresh * (gen ^ c) ^ 24)),
        (axLc m b0, (List.range m).map (fun c => ccarried * (gen ^ c) ^ 24)),
        (axAbs m b0, (List.range (m + 1)).flatMap (fun c => rowW (absSt m cs c))),
        (axLam m b0, (List.range m).flatMap
          (fun c => [(lamOf (aggAbs cs) c).1, (lamOf (aggAbs cs) c).2])),
        (axSq m b0, (List.range (m + 1)).flatMap
          (fun c => rowW (sq2F c (aggAbs cs)).2 ++ [claimAt cs c])),
        (axPt m b0, (aggRun cs h).1.1),
        (axW m b0, (List.range (m + 1)).map (weightAt cs h))] := rfl

theorem agg_zip (m b0 : ℕ) : (aggSizes m).zip (bases b0 (aggSizes m)) =
    [(46, b0), (m, axLf b0), (m, axLc m b0), (13 * (m + 1), axAbs m b0), (2 * m, axLam m b0),
      (14 * (m + 1), axSq m b0), (23, axPt m b0), (m + 1, axW m b0)] := rfl

theorem len_frange {α : Type} (f : ℕ → List α) (w n : ℕ) (hf : ∀ j, (f j).length = w) :
    ((List.range n).flatMap f).length = n * w := by
  simp [List.length_flatMap, hf]

theorem rowW_abs_len (m : ℕ) (cs : List ChildClaims) (c : ℕ) : (rowW (absSt m cs c)).length = 13 :=
  rowW_length (absSt_ok m cs c)

theorem rowW_sq_len (cs : List ChildClaims) (c : ℕ) :
    (rowW (sq2F c (aggAbs cs)).2 ++ [claimAt cs c]).length = 14 := by
  simp [rowW_length (sqSt_ok cs c)]

/-- The buffers' words fit their sizes. -/
theorem aggConts_fit {m : ℕ} {cfresh ccarried : E} {cs : List ChildClaims} {h : BatchHints}
    (hrl : h.bytecodeRounds.length = 23) :
    List.Forall₂ (fun c s => c.length ≤ s) (aggConts m cfresh ccarried cs h) (aggSizes m) := by
  simp only [aggConts, aggSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, by simp, by simp, ?_, ?_, ?_, ?_, by simp⟩
  · simp [hrl]
  · rw [len_frange _ 13 _ (rowW_abs_len m cs)]; omega
  · rw [len_frange _ 2 _ (fun _ => rfl)]; omega
  · rw [len_frange _ 14 _ (rowW_sq_len cs)]; omega
  · rw [aggRun, bsRun_len, hrl]

theorem readsAt_rows {rd : Reader} {p : E} {n w : ℕ} {f : ℕ → List E}
    (hw : ∀ c, (f c).length = w) (h : ReadsAt rd p ((List.range n).flatMap f)) :
    ∀ c < n, ReadsAt rd (p * (gen ^ c) ^ w) (f c) := by
  intro c hc
  have := Main.readsAt_flatMap_of (List.range n) (fun c _ => hw c) h c (by simpa using hc)
  simp only [List.getElem_range] at this
  rwa [← pow_mul, Nat.mul_comm c]

theorem loadAt_map {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ReadsAt rd p ((List.range n).map f)) : ∀ c < n, LoadHolds rd (p * gen ^ c) 0 (f c) := by
  intro c hc
  have := h c (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range] at this
  rw [loadHolds_mul_gen_pow, Nat.add_zero]
  exact this

/-- **`AggMem` off a memory holding `aggregate_claims`' buffers and the claim at `dst`.** -/
theorem aggMem_of_memL {rd : Reader} {cfresh ccarried dst : E} {cs : List ChildClaims}
    {h : BatchHints} {b0 : ℕ} (hm : MemL rd (aggOwn cs.length cfresh ccarried cs h b0))
    (hdst : ReadsAt rd dst (aggOut cs h).cells) :
    AggMem rd cfresh ccarried dst cs h (aggPtrsAt cs.length b0) := by
  have M : ∀ {b : ℕ} {xs : List E}, (b, xs) ∈ aggOwn cs.length cfresh ccarried cs h b0 →
      ReadsAt rd (gen ^ b) xs := fun hq => reads_of_memL hm hq
  rw [aggOwn_eq] at M
  refine ⟨fun c hc => readsAt_rows (rowW_abs_len _ cs) (M (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) c (by omega),
    loadAt_map (M (List.mem_cons_of_mem _ List.mem_cons_self)),
    loadAt_map (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    fun c hc => readsAt_rows (rowW_sq_len cs) (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))) c (by omega),
    fun c hc => readsAt_rows (f := fun c => [(lamOf (aggAbs cs) c).1, (lamOf (aggAbs cs) c).2])
      (fun _ => rfl) (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))) c hc,
    M List.mem_cons_self,
    M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))))),
    fun c hc => loadAt_map (M (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) c (by omega),
    hdst⟩

/-! ## The callees -/

/-- `aggregate_claims`' callees, which place nothing. -/
def aggPureSet : List String := ["__loop24", "__loop25", "__loop26", "batch_sumcheck__L23"]

/-- Every member's body places nothing and calls members only. -/
noncomputable def aggPureOk : Bool :=
  aggPureSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList aggPureSet fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem aggPure_ok : aggPureOk = true := by decide +kernel

theorem aggPure : coreProgram.PureIn aggPureSet := by
  intro g hg fn hf
  have h := List.all_eq_true.mp aggPure_ok g hg
  rw [hf] at h
  exact h

/-! ## The path -/

set_option maxRecDepth 100000 in
theorem aggP_straight : aggP.all Main.Stmt.straight = true := by decide +kernel

/-- `aggregate_claims`' statements: atoms, the sumcheck's call and its guarded loops. -/
def aggKind : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf c _ _ => decide (c ∈ [V.n 62, .n 95, .n 121])
  | _ => false

set_option maxRecDepth 100000 in
theorem aggP_kinds : aggP.all aggKind = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_allocs : aggP.filterMap Main.Stmt.allocSz = [(.n 5, .inl 46), (.n 7, .inr (.n 0)),
    (.n 8, .inr (.n 0)), (.n 60, .inr (.n 59)), (.n 71, .inr (.n 70)), (.n 79, .inr (.n 78)),
    (.n 104, .inl 23), (.n 118, .inr (.n 117))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_addrs : aggP.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem aggP_calls : aggP.filterMap Main.Stmt.callS =
    [(some (.n 62), "__loop24", [.n 63, .n 0, .n 60, .n 2, .n 7, .n 3, .n 8, .n 1], []),
      (some (.n 95), "__loop25", [.n 96, .n 0, .n 79, .n 71, .n 7, .n 8], []),
      (none, "batch_sumcheck__L23", [.n 105, .n 106, .n 107, .n 108, .n 109, .n 5, .n 103, .n 104],
        [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115]),
      (some (.n 121), "__loop26", [.n 122, .n 0, .n 7, .n 8, .n 104, .n 118, .n 71], [])] := by
  decide +kernel

/-- The loads `aggregate_claims` may make: its first rows, last rows, weights, point, and the
claim at `defer_stmt`. -/
def aggLoadSet : List (V × ℕ) :=
  (List.range 13).map (fun i => (.n 60, i)) ++ (List.range 14).map (fun k => (.n 79, k)) ++
    [(.n 118, 0)] ++ (List.range 24).map (fun k => (.n 4, k)) ++
    (List.range 13).map (fun k => (.n 69, k)) ++ (List.range 14).map (fun k => (.n 102, k)) ++
    [(.n 123, 0)] ++ (List.range 23).map (fun k => (.n 104, k))

set_option maxRecDepth 100000 in
theorem aggP_loads : (aggP.filterMap B1.Stmt.loadS).all (fun q => decide (q ∈ aggLoadSet)) = true := by
  decide +kernel

/-- The buffers' sizes' words. -/
noncomputable def aggSizeOk : Bool :=
  let A := atomsIn aggP
  A.any (isConstAt (.n 53) 2 0) && isMul A (.n 54) (.n 0) (.n 53) && isMul A (.n 55) (.n 54) (.n 54) &&
  isMul A (.n 56) (.n 55) (.n 54) && isMul A (.n 57) (.n 56) (.n 56) &&
  isMul A (.n 58) (.n 57) (.n 57) && isMul A (.n 59) (.n 58) (.n 54) &&
  isMul A (.n 70) (.n 0) (.n 0) &&
  A.any (isConstAt (.n 72) 2 0) && isMul A (.n 73) (.n 0) (.n 72) &&
  isMul A (.n 74) (.n 73) (.n 73) && isMul A (.n 75) (.n 74) (.n 73) &&
  isMul A (.n 76) (.n 75) (.n 75) && isMul A (.n 77) (.n 76) (.n 73) &&
  isMul A (.n 78) (.n 77) (.n 77) &&
  A.any (isConstAt (.n 116) 2 0) && isMul A (.n 117) (.n 0) (.n 116)

set_option maxRecDepth 100000 in
theorem aggSize_ok : aggSizeOk = true := by decide +kernel

theorem agg_loop : coreProgram.loop "aggregate_claims" = false := by
  rw [Program.loop_of_find? find_aggregate_claims]; decide +kernel

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

/-- The buffers' sizes, as the valuation computes them. -/
theorem agg_sizes {rd : Reader} {σ : Val} {m : ℕ} (hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ)
    (e0 : σ (.n 0) = gen ^ m) :
    σ (.n 59) = gen ^ (13 * (m + 1)) ∧ σ (.n 70) = gen ^ (2 * m) ∧
      σ (.n 78) = gen ^ (14 * (m + 1)) ∧ σ (.n 117) = gen ^ (m + 1) := by
  have hok := aggSize_ok
  simp only [aggSizeOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c53, m54⟩, m55⟩, m56⟩, m57⟩, m58⟩, m59⟩, m70⟩, c72⟩, m73⟩, m74⟩, m75⟩,
    m76⟩, m77⟩, m78⟩, c116⟩, m117⟩ := hok
  have g53 : σ (.n 53) = gen := by rw [const_sound c53 hat, word_gen]
  have g72 : σ (.n 72) = gen := by rw [const_sound c72 hat, word_gen]
  have g116 : σ (.n 116) = gen := by rw [const_sound c116 hat, word_gen]
  have s54 : σ (.n 54) = gen ^ (m + 1) := by rw [isMul_sound m54 hat, e0, g53, pow_succ]
  have s55 : σ (.n 55) = gen ^ (2 * (m + 1)) := by
    rw [isMul_sound m55 hat, s54, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  have s56 : σ (.n 56) = gen ^ (3 * (m + 1)) := by
    rw [isMul_sound m56 hat, s55, s54, ← pow_add, show 2 * (m + 1) + (m + 1) = 3 * (m + 1) by ring]
  have s57 : σ (.n 57) = gen ^ (6 * (m + 1)) := by
    rw [isMul_sound m57 hat, s56, ← pow_add,
      show 3 * (m + 1) + 3 * (m + 1) = 6 * (m + 1) by ring]
  have s58 : σ (.n 58) = gen ^ (12 * (m + 1)) := by
    rw [isMul_sound m58 hat, s57, ← pow_add,
      show 6 * (m + 1) + 6 * (m + 1) = 12 * (m + 1) by ring]
  have s73 : σ (.n 73) = gen ^ (m + 1) := by rw [isMul_sound m73 hat, e0, g72, pow_succ]
  have s74 : σ (.n 74) = gen ^ (2 * (m + 1)) := by
    rw [isMul_sound m74 hat, s73, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring]
  have s75 : σ (.n 75) = gen ^ (3 * (m + 1)) := by
    rw [isMul_sound m75 hat, s74, s73, ← pow_add, show 2 * (m + 1) + (m + 1) = 3 * (m + 1) by ring]
  have s76 : σ (.n 76) = gen ^ (6 * (m + 1)) := by
    rw [isMul_sound m76 hat, s75, ← pow_add,
      show 3 * (m + 1) + 3 * (m + 1) = 6 * (m + 1) by ring]
  have s77 : σ (.n 77) = gen ^ (7 * (m + 1)) := by
    rw [isMul_sound m77 hat, s76, s73, ← pow_add,
      show 6 * (m + 1) + (m + 1) = 7 * (m + 1) by ring]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isMul_sound m59 hat, s58, s54, ← pow_add,
      show 12 * (m + 1) + (m + 1) = 13 * (m + 1) by ring]
  · rw [isMul_sound m70 hat, e0, ← pow_add, show m + m = 2 * m by ring]
  · rw [isMul_sound m78 hat, s77, ← pow_add,
      show 7 * (m + 1) + 7 * (m + 1) = 14 * (m + 1) by ring]
  · rw [isMul_sound m117 hat, e0, g116, pow_succ]

/-! ## `aggregate_claims` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`aggregate_claims` is complete, placed**: on `m ≤ 16` children whose words the caller's
words `Lin` hold, the hints of an accepting batching, writing the batching's claim, which `Lin`
holds at `g^ds`. -/
theorem aggregate_claims_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm16 : m ≤ 16) {cs : List ChildClaims} (hcl : cs.length = m) {h : BatchHints}
    {out : DeferredClaim} (hrl : h.bytecodeRounds.length = 23) (hb : batch cs h = some out)
    {cpi cfresh ccarried : E} {ds : ℕ} {Lin : Main.Layout}
    (hcw : ∀ rd, Main.MemL rd Lin → ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hdst : (ds, out.cells) ∈ Lin) :
    CompleteAtD fs cert 16 "aggregate_claims" Lin [gen ^ m, cpi, cfresh, ccarried, gen ^ ds]
      (Returns []) := by
  subst hcl
  obtain ⟨hout, -⟩ := batch_out hb
  subst hout
  intro fp
  set m := cs.length with hmd
  set b0 := fp + fs "aggregate_claims" with hb0
  set P := aggPtrsAt m b0 with hP
  set Own := aggOwn m cfresh ccarried cs h b0 with hOwn
  have hfit := aggConts_fit (m := m) (cfresh := cfresh) (ccarried := ccarried) (cs := cs) hrl
  have hbm : ∀ rd, Main.MemL rd (Own ++ Lin) → AggMem rd cfresh ccarried (gen ^ ds) cs h P :=
    fun rd hm => by
      obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
      exact aggMem_of_memL h1 (reads_of_memL h2 hdst)
  have hcw' : ∀ rd, Main.MemL rd (Own ++ Lin) → ∀ c (hc : c < cs.length),
      ChildWordsAt rd cpi cfresh ccarried c cs[c] :=
    fun rd hm => hcw rd (Main.memL_append.mp hm).2
  have hne : (1 : E) + gen ^ m ≠ 0 := (one_add_gen_ne (by omega)).mpr (by omega)
  -- the callees
  let ks : List Kid :=
    [⟨"__loop24", true, [1, gen ^ m, P.absorb, cfresh, P.lf, ccarried, P.lc, cpi], Own ++ Lin,
        Returns []⟩,
      ⟨"__loop25", true, [1, gen ^ m, P.sq, P.lam, P.lf, P.lc], Own ++ Lin, Returns []⟩,
      ⟨"batch_sumcheck__L23", true, (sq2F m (aggAbs cs)).2.cap ++ [P.msgs, claimAt cs m, P.pt],
        Own ++ Lin, Returns ((aggRun cs h).2.cap ++ [(aggRun cs h).1.2])⟩,
      ⟨"__loop26", true, [1, gen ^ m, P.lf, P.lc, P.pt, P.w, P.lam], Own ++ Lin, Returns []⟩]
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
    intro k hk _
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l25 l25_shape' (rest := [P.absorb, cfresh, P.lf, ccarried, P.lc, cpi])
          (agg_l25 (hcw' rd hm) (hbm rd hm))).2 hne) 16
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l26 l26_shape.1 (rest := [P.sq, P.lam, P.lf, P.lc])
          (agg_l26 (hcw' rd hm) (hbm rd hm))).2 hne) 16
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet])
        (fun rd hm => agg_bs hm1 hrl (hbm rd hm)) 16
    · exact completeAt_of_rel_pureD aggPure (by simp [aggPureSet]) (fun rd hm =>
        (guard_complete find_l27 l27_shape.1 (rest := [P.lf, P.lc, P.pt, P.w, P.lam])
          (agg_l27 (hcw' rd hm) hrl (hbm rd hm))).2 hne) 16
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 16 ks hok (b0 + (aggSizes m).sum)
  have hl0 : outs.length = 4 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain rfl := List.eq_nil_of_length_eq_zero hl4
  obtain ⟨h1, h2, h3, h4, -⟩ := hoo
  -- the layout
  have hWo : Within Own b0 (aggSizes m).sum := bufL_within _ _ _ hfit
  refine ⟨fs "aggregate_claims" + (aggSizes m).sum + Nk, Own ++ Lk, [], [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append (bufL_disj _ _ _ hfit : DisjL Own) hD hWo hW le_rfl,
    fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1', hLin'⟩ := Main.memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := Main.memL_append.mp hm1'
  have hmK : Main.MemL rd (Own ++ Lin) := Main.memL_append.mpr ⟨hmO, hLin'⟩
  have hmem := hbm rd hmK
  -- the valuation and the path
  have hV := agg_core (rd := rd) (cpi := cpi) hm1 rfl hrl hb hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = aggσ rd m cpi cfresh ccarried (gen ^ ds) P cs h := ⟨_, rfl⟩
  rw [← hσ] at hV
  have hw := Main.walk_straight σ [] aggP aggP_straight
  rw [← agg_shape] at hw
  set es := aggP.flatMap (Main.slEvs σ) with hes
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    have hk := List.all_eq_true.mp aggP_kinds st hst
    match st, hk with
    | .atom a, _ => exact hV.atoms a (mem_atomsIn hst)
    | .call .., _ => trivial
    | .ite .., hk => simp [aggKind] at hk
    | .match_ .., hk => simp [aggKind] at hk
    | .dispatch .., hk => simp [aggKind] at hk
    | .ret _, hk => simp [aggKind] at hk
    | .callIf c f args, hk =>
      simp only [aggKind, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at hk
      show IsInK (σ c)
      rcases hk with rfl | rfl | rfl
      · rw [hV.g62, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g95, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [hV.g121, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ aggP_straight
  obtain ⟨s59, s70, s78, s117⟩ := agg_sizes hV.atoms hV.e0
  have hal : allocs σ es = aggSizes m := by
    rw [hes, hpa, aggP_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, hV.e0, s59, s70, s78,
      s117, logG_gen_pow (show m < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 13 * (m + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 2 * m < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 14 * (m + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show m + 1 < 2 ^ 64 - 1 by omega)]
    rfl
  have hT : ∀ {c : V}, σ c = 1 + gen ^ m → decide (σ c ≠ 0) = true :=
    fun h => by rw [h]; exact decide_eq_true hne
  have hcalls : calls es =
      [⟨"__loop24", [.n 63, .n 0, .n 60, .n 2, .n 7, .n 3, .n 8, .n 1], [], true⟩,
        ⟨"__loop25", [.n 96, .n 0, .n 79, .n 71, .n 7, .n 8], [], true⟩,
        ⟨"batch_sumcheck__L23", [.n 105, .n 106, .n 107, .n 108, .n 109, .n 5, .n 103, .n 104],
          [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115], true⟩,
        ⟨"__loop26", [.n 122, .n 0, .n 7, .n 8, .n 104, .n 118, .n 71], [], true⟩] := by
    rw [hes, hpc, aggP_calls]
    simp only [List.map_cons, List.map_nil, Main.mkCall, hT hV.g62, hT hV.g95, hT hV.g121]
  -- the walk
  have hown : ∀ i, Main.RegionL Own i → ownData cert fp b0 "aggregate_claims" (aggSizes m) es i :=
    fun i hi => Or.inl (bufL_region _ _ _ hfit i hi)
  have hz : ∀ {s x j : ℕ}, (s, x) ∈ (aggSizes m).zip (bases b0 (aggSizes m)) → x ≤ j →
      j < x + s → ownData cert fp b0 "aggregate_claims" (aggSizes m) es j :=
    fun hq h1 h2 => Or.inl ⟨_, hq, h1, h2⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := Main.RegionL Lin) (D := Main.RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ m, cpi, cfresh, ccarried, gen ^ ds]) (rets := [])
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
    coreProgram_wf find_aggregate_claims (Or.inl agg_loop) (by
      show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = _
      rw [hV.e0, hV.e1, hV.e2, hV.e3, hV.e4]) hw rfl hev
    (by
      rw [hal, hes, hpd, aggP_allocs]
      simp only [List.map_cons, List.map_nil, hV.v5, hV.v7, hV.v8, hV.v60, hV.v71, hV.v79, hV.v104,
        hV.v118, hP, aggPtrsAt, gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, hpad, aggP_addrs] at hq
      simp at hq)
    ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [hcalls, hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 63), σ (.n 0), σ (.n 60), σ (.n 2), σ (.n 7), σ (.n 3), σ (.n 8), σ (.n 1)] = _
        rw [hV.g63, hV.e0, hV.v60, hV.e2, hV.v7, hV.e3, hV.v8, hV.e1]
      · rw [(h1 rfl).1]; rfl
      · show [σ (.n 96), σ (.n 0), σ (.n 79), σ (.n 71), σ (.n 7), σ (.n 8)] = _
        rw [hV.g96, hV.e0, hV.v79, hV.v71, hV.v7, hV.v8]
      · rw [(h2 rfl).1]; rfl
      · exact hV.bsArgs
      · rw [(h3 rfl).1]; exact hV.bsRets
      · show [σ (.n 122), σ (.n 0), σ (.n 7), σ (.n 8), σ (.n 104), σ (.n 118), σ (.n 71)] = _
        rw [hV.g122, hV.e0, hV.v7, hV.v8, hV.v104, hV.v118, hV.v71]
      · rw [(h4 rfl).1]; rfl
    · intro q hq
      apply hmK
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq ⊢
      tauto
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hkL : k.Lin = Own ++ Lin := by rcases hk with rfl | rfl | rfl | rfl <;> rfl
      rw [hkL] at hi
      obtain ⟨q, hq, hq1, hq2⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (Or.inr (hown i ⟨q, hq, hq1, hq2⟩))
      · exact Or.inl (Or.inl ⟨q, hq, hq1, hq2⟩)
  · intro A hA
    rw [hal]
    rw [hes, B1.loadAddrs_straight σ _ aggP_straight] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' := of_decide_eq_true (List.all_eq_true.mp aggP_loads q hq)
    have zl := agg_zip m b0
    simp only [aggLoadSet, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hq'
    rcases hq' with ((((((⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) |
      ⟨k, hk, rfl⟩) | rfl) | ⟨k, hk, rfl⟩
    · refine ⟨axAbs m b0 + i, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 60)).limb 0 * gpow i = _
      rw [hV.v60]; exact limb0_gen_pow_mul _ _
    · refine ⟨axSq m b0 + k, ?_, Or.inl (hz (s := 14 * (m + 1)) (x := axSq m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 79)).limb 0 * gpow k = _
      rw [hV.v79]; exact limb0_gen_pow_mul _ _
    · refine ⟨axW m b0 + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 118)).limb 0 * gpow 0 = _
      rw [hV.v118]; exact limb0_gen_pow_mul _ _
    · have hcl2 : (aggOut cs h).cells.length = 24 := by
        simp [aggOut, DeferredClaim.cells, aggRun, bsRun_len, hrl]
      refine ⟨ds + k, ?_, Or.inr (Or.inl (regionL_of_mem hdst (by rw [hcl2]; exact hk)))⟩
      show (σ (.n 4)).limb 0 * gpow k = _
      rw [hV.e4]; exact limb0_gen_pow_mul _ _
    · refine ⟨axAbs m b0 + 13 * m + k, ?_, Or.inl (hz (s := 13 * (m + 1)) (x := axAbs m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 69)).limb 0 * gpow k = _
      rw [hV.p69, show P.absorb = gen ^ axAbs m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 13]
    · refine ⟨axSq m b0 + 14 * m + k, ?_, Or.inl (hz (s := 14 * (m + 1)) (x := axSq m b0)
        (by rw [zl]; simp)
        (by omega) (by omega))⟩
      show (σ (.n 102)).limb 0 * gpow k = _
      rw [hV.p102, show P.sq = gen ^ axSq m b0 from rfl, ← pow_mul, ← pow_add,
        limb0_gen_pow_mul, Nat.mul_comm m 14]
    · refine ⟨axW m b0 + m + 0, ?_, Or.inl (hz (s := m + 1) (x := axW m b0)
        (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 123)).limb 0 * gpow 0 = _
      rw [hV.p123, show P.w = gen ^ axW m b0 from rfl, ← pow_add, limb0_gen_pow_mul]
    · refine ⟨axPt m b0 + k, ?_, Or.inl (hz (s := 23) (x := axPt m b0) (by rw [zl]; simp) (by omega)
        (by omega))⟩
      show (σ (.n 104)).limb 0 * gpow k = _
      rw [hV.v104]; exact limb0_gen_pow_mul _ _
end
end LeanVM.Guest.B1.Main
