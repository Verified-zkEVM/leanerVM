/-
  LeanVM.Guest.Budget.L5Count

  The children loop's instructions, per opcode, iteration by iteration: each child's claim lists'
  digests, DA roots, digests and `verify_sub` by their static counts, `verify_sub` within a bound
  `V c` per child.
-/

module

public import LeanVM.Guest.Budget.VsCount
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.B1.Main.MainHonestBudget

/-!
# The children loop's instructions

`ccW op n`: `child_claim_list_digest`'s instructions of `op` on `n` claims: its frame's weight,
`list_split`'s, `n / 17` iterations of `__loop17` and the last group's
`child_claim_list_last__L{n % 17}` (`ccl_weight_le`, on a tree of honest shape `ccHonest n`).
`l5B op X S V c`: iteration `c` of `__loop5`: its frame's weight, the two claim lists' digests
(`X c`, `S c` claims), at most `16` DA roots' `__loop28` iterations, `da_list_digest`,
`statement_digest`, and `verify_sub` within `V c`. `l5_weight_le`: the iterations from `c`
(`L5From`) weigh at most the sum of their `l5B`. `l5B_le`: `l5B` is at most a constant `l5C op`,
`ccS op` per claim, and `V c` (`ccW_le`: `n / 17` iterations within `⌈K / 17⌉` per claim).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.Count
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (ccHonest L5From l5CallList l5Ts l5Ts6 l5Evs l5Pre l5Tail l5Body
  l5Body_split l5Pre_straight l5_body find_l5)

@[expose] public section

/-- **`child_claim_list_digest`'s instructions of `op` on `n` claims.** -/
def ccW (op : Opcode) (n : ℕ) : ℕ :=
  (omT op).getD 1 0 + (if n = 0 then 0 else kcLs op + n / 17 * kcL17 op + (kcCclT op).getD (n % 17) 0)

theorem cclNames_eq {k : ℕ} (hk : k < 17) :
    B1.Digest.cclNames[k]! = "child_claim_list_last__L" ++ B1.Whir.natStr k := by
  interval_cases k <;> decide +kernel

theorem ccl_ne {k : ℕ} (hk : k < 17) :
    B1.Digest.cclNames[k]! ≠ "list_split" ∧ B1.Digest.cclNames[k]! ≠ "__loop17" := by
  interval_cases k <;> decide

set_option maxHeartbeats 1000000 in
/-- **`child_claim_list_digest`'s instructions** on a tree of honest shape. -/
theorem ccl_weight_le (op : Opcode) {n : ℕ} (hn : n / 17 < 2 ^ 64 - 1) {rd : Reader} {t : Tree}
    {args rets : List E} (h : ccHonest n t) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) : t.weight (B2C.ωArm B2C.xmssArmC op) ≤ ccW op n := by
  let W : Call → ℕ := fun c =>
    if c.f = "list_split" then kcLs op
    else if c.f = "__loop17" then n / 17 * kcL17 op else (kcCclT op).getD (n % 17) 0
  obtain ⟨σ, hQ, hle⟩ := NodeHonest.weight_le (B2C.ωArm B2C.xmssArmC op) (fun _ => W) h hv hb
    (by
      intro σ hQ c T hmem ht t' rets' hn' hv' hb' _
      by_cases h0 : n = 0
      · simp [B1.Digest.ccCalls, h0] at hmem
      obtain ⟨h5, h27, -, -, h52⟩ := And.intro hQ.1 (hQ.2 h0)
      simp only [B1.Digest.ccCalls, h0, ↓reduceIte, B1.Digest.clTs, List.zip_cons_cons,
        List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [W, ↓reduceIte]
        exact ls_weightLe op rd t' _ rets' hn' hv' hb'
      · simp only [W, String.reduceEq, ↓reduceIte]
        have hq : n / 17 ≠ 0 := by simpa using ht
        have := l17_loop op rd t' _ rets' 0 (n / 17) hn' hv' hb'
          (by simp only [List.map_cons, List.getD_cons_zero]; rw [h52, one_eq_ofK])
          (by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
              rw [h27, Value.gen_pow_eq_ofK]) (by omega) hn
        simpa using this
      · have hk : n % 17 < 17 := Nat.mod_lt _ (by norm_num)
        obtain ⟨e1, e2⟩ := ccl_ne hk
        simp only [W, e1, e2, ↓reduceIte]
        rw [cclNames_eq hk] at hn'
        exact ccl_weightLe op hk rd t' _ rets' hn' hv' hb')
  have hom := om_eq op (i := 1) (by norm_num)
  simp only [omNames, List.getD_cons_succ, List.getD_cons_zero] at hom
  rw [hom] at hle
  unfold ccW
  by_cases h0 : n = 0
  · have hc : callsW W (B1.Digest.ccCalls n σ) = 0 := by simp [callsW, B1.Digest.ccCalls, h0]
    simp only [h0, ↓reduceIte]
    omega
  · have hc : callsW W (B1.Digest.ccCalls n σ) ≤
        kcLs op + n / 17 * kcL17 op + (kcCclT op).getD (n % 17) 0 := by
      obtain ⟨e1, e2⟩ := ccl_ne (Nat.mod_lt n (show 0 < 17 by norm_num))
      simp only [callsW, B1.Digest.ccCalls, h0, ↓reduceIte, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, W, String.reduceEq, e1, e2]
      clear hle
      generalize n / 17 * kcL17 op = P
      split <;> omega
    simp only [h0, ↓reduceIte]
    omega

/-- **Iteration `c` of `__loop5`**: its frame, the claim lists' digests on `X c` and `S c` claims,
at most `16` iterations of `__loop28`, the DA roots' and the statement's digests, and
`verify_sub` within `V c`. -/
def l5B (op : Opcode) (X S V : ℕ → ℕ) (c : ℕ) : ℕ :=
  (omT op).getD 2 0 + ccW op (X c) + ccW op (S c) + 16 * kcL28 op + kcDl op + kcSd op + V c

theorem l5_walk {σ : Val} {fn : Fn} {es : List Ev} {vs : List V}
    (hf : coreProgram.find? "__loop5" = some fn) (hw : walk σ fn.body = .ret es vs) :
    es = l5Evs σ := by
  rw [find_l5, Option.some.injEq] at hf
  subst hf
  have hw' := walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [← l5Body_split, l5Body, ← l5_body] at hw'
  rw [hw'] at hw
  injection hw with h1
  exact h1.symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- **The children loop's instructions**: the iterations from child `c` weigh at most the sum of
their `l5B`. -/
theorem l5_weight_le (op : Opcode) {ex es ed X S : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} (V : ℕ → ℕ)
    (hX : ∀ c, X c / 17 < 2 ^ 64 - 1) (hS : ∀ c, S c / 17 < 2 ^ 64 - 1)
    (hV : ∀ c (rd : Reader) (t : Tree) (args rets : List E), Pvs c t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ V c) :
    ∀ m c (rd : Reader) (t : Tree) (args rets : List E),
      L5From ex es ed (fun c => ccHonest (X c)) (fun c => ccHonest (S c)) Pvs m c t →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤ iterSum (l5B op X S V) c m
  | 0, _, _, _, _, _, h, _, _ => h.elim
  | m + 1, c, rd, t, args, rets, h, hv, hb => by
    obtain ⟨σ, bufs, ks, rfl, -, -, h63, h73, hed, hcalls, hKT⟩ := h
    have hv' := hv
    obtain ⟨fn, hf, -, es', vs', hw, -, hes, hk⟩ := hv'
    have he := l5_walk hf hw
    subst he
    rw [hcalls] at hk
    have hatom : ∀ a : Atom, decide (a ∈ B1.Digest.atomsIn l5Pre) = true → a.Holds rd σ := by
      intro a ha
      have := hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a,
        List.mem_append_left _ (B1.Main.atom_mem_of_atomsIn' (of_decide_eq_true ha)),
        by simp [slEvs]⟩)
      exact this
    have v72 : σ (.n 72) = σ (.n 71) + σ (.n 63) := hatom (.add (.n 72) (.n 71) (.n 63)) (by decide +kernel)
    have v71 : σ (.n 71) = word 1 0 0 := hatom (.const (.n 71) (word 1 0 0)) (by decide +kernel)
    have hk' := kids_weight_leL (B2C.ωArm B2C.xmssArmC op) (l5CallList σ)
      (l5Ts (ccHonest (X c)) (ccHonest (S c)) (Pvs c)
        (L5From ex es ed (fun c => ccHonest (X c)) (fun c => ccHonest (S c)) Pvs m (c + 1)))
      [ccW op (X c), ccW op (S c), 16 * kcL28 op, kcDl op, kcSd op, V c,
        iterSum (l5B op X S V) (c + 1) m] ks hk hb.2 hKT (by simp [l5CallList, l5Ts, l5Ts6])
      (by simp [l5CallList])
      (fun i hi _ _ ht t' rets' hn hv'' hb'' hT' => by
        have hi7 : i < 7 := by simpa [l5CallList] using hi
        interval_cases i <;>
          simp only [l5CallList, l5Ts, l5Ts6, List.cons_append, List.nil_append,
            List.getElem_cons_zero, List.getElem_cons_succ] at ht hn hv'' hT' ⊢
        · exact ccl_weight_le op (hX c) hT' hv'' hb''
        · exact ccl_weight_le op (hS c) hT' hv'' hb''
        · have h72 : σ (.n 72) ≠ 0 := by simpa using ht
          rw [v72, v71, B1.word_one, h63] at h72
          have hed0 := ne_zero_of_guard h72
          have := kcL28_loop op rd t' _ rets' 0 (ed c) hn hv'' hb''
            (by simp only [List.map_cons, List.getD_cons_zero]; rw [h73, one_eq_ofK])
            (by simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
                rw [h63, Value.gen_pow_eq_ofK]) (by omega)
            (by omega)
          have h16 : (ed c - 0) * kcL28 op ≤ 16 * kcL28 op := Nat.mul_le_mul_right _ (by omega)
          omega
        · exact kcDl_weightLe op rd t' _ rets' hn hv'' hb''
        · exact kcSd_weightLe op rd t' _ rets' hn hv'' hb''
        · exact hV c rd t' _ rets' hT' hv'' hb''
        · exact l5_weight_le op V hX hS hV m (c + 1) rd t' _ rets' hT' hv'' hb'')
    have hom := om_eq op (i := 2) (by norm_num)
    simp only [omNames, List.getD_cons_succ, List.getD_cons_zero] at hom
    rw [Tree.weight, iterSum_succ, hom]
    simp only [List.sum_cons, List.sum_nil] at hk'
    have hl5 : l5B op X S V c = (omT op).getD 2 0 + ccW op (X c) + ccW op (S c) + 16 * kcL28 op +
      kcDl op + kcSd op + V c := rfl
    omega

/-- The per-claim slope of `ccW`: `⌈K / 17⌉` of `__loop17`'s `K` per iteration and `1` more. -/
def ccS (op : Opcode) : ℕ := (kcL17 op + 16) / 17

/-- The constant of `ccW`: the frame, `list_split` and the largest last group. -/
def ccA (op : Opcode) : ℕ := (omT op).getD 1 0 + kcLs op + (kcCclT op).foldl max 0

theorem ccW_le (op : Opcode) (n : ℕ) : ccW op n ≤ ccA op + n * ccS op := by
  unfold ccW ccA ccS
  split
  · omega
  · have hk : (kcCclT op).getD (n % 17) 0 ≤ (kcCclT op).foldl max 0 := by
      cases op <;> (have : n % 17 < 17 := Nat.mod_lt _ (by norm_num); interval_cases (n % 17) <;> decide)
    have hq : n / 17 * kcL17 op ≤ n * ((kcL17 op + 16) / 17) := by
      have h1 : kcL17 op ≤ 17 * ((kcL17 op + 16) / 17) := by omega
      have h2 : 17 * (n / 17) ≤ n := Nat.mul_div_le n 17
      calc n / 17 * kcL17 op ≤ n / 17 * (17 * ((kcL17 op + 16) / 17)) := Nat.mul_le_mul_left _ h1
        _ = 17 * (n / 17) * ((kcL17 op + 16) / 17) := by ring
        _ ≤ n * ((kcL17 op + 16) / 17) := Nat.mul_le_mul_right _ h2
    omega

/-- **An iteration's constant**: all but the claims' slope and `verify_sub`. -/
def l5C (op : Opcode) : ℕ := (omT op).getD 2 0 + 2 * ccA op + 16 * kcL28 op + kcDl op + kcSd op

theorem l5B_le (op : Opcode) (X S V : ℕ → ℕ) (c : ℕ) :
    l5B op X S V c ≤ l5C op + ccS op * (X c + S c) + V c := by
  have h1 := ccW_le op (X c); have h2 := ccW_le op (S c)
  unfold l5B l5C
  have : ccS op * (X c + S c) = X c * ccS op + S c * ccS op := by ring
  omega

/-- **The children loop's instructions, linearly**: `m` iterations from `c` within `m` constants,
the slope on their claims and their `verify_sub`'s. -/
theorem iterSum_l5B_le (op : Opcode) (X S V : ℕ → ℕ) : ∀ c m,
    iterSum (l5B op X S V) c m ≤
      m * l5C op + ccS op * iterSum (fun i => X i + S i) c m + iterSum V c m
  | _, 0 => by simp [iterSum]
  | c, m + 1 => by
    rw [iterSum_succ, iterSum_succ, iterSum_succ]
    have := iterSum_l5B_le op X S V (c + 1) m
    have := l5B_le op X S V c
    have e : (m + 1) * l5C op = l5C op + m * l5C op := by ring
    have e2 : ccS op * (X c + S c + iterSum (fun i => X i + S i) (c + 1) m) =
      ccS op * (X c + S c) + ccS op * iterSum (fun i => X i + S i) (c + 1) m := by ring
    omega

end
end LeanVM.Guest.Budget
