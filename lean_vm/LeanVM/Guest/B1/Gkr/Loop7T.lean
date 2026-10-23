/-
  LeanVM.Guest.B1.Gkr.Loop7T

  `__loop7`'s valid trees are chains of honest shape (`Budget.ChainHonest`): each iteration's node
  pins the bounds of the `__loop29` it calls and which rounds it calls.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7In
public import LeanVM.Guest.Budget.Chain

/-!
# `__loop7`, of honest shape

Iteration `c` of `__loop7` (from `g^c` below `g^M`, layer `L = 2c + sh`) calls `__loop29` from
`1` (`σ 65`) below `g^(c/2)` (`σ 61`, the slot's `half`), then `gkr_rounds__L2` when `c` is odd
(`σ 62`, the slot's parity bit) and `gkr_rounds__L1` when `sh = 1` (`σ 70 = g^(2c+sh) + g^(2c)`),
then itself from `g^(c+1)`, entered iff `c + 1 < M`.

* `ly7Q sh c σ`: those values; `ly7Csb σ`, `ly7Tl σ`: the body's calls and the tail call;
  `ly7Tsb sh c`: one `True` per body call.
* `ly7_calls`: the walk's calls are `ly7Csb σ ++ [ly7Tl σ]`.
* `ly7_chain`: on a memory whose `depth_shift` word is `g^sh` and whose slots hold `half` and
  `parity` (`Ly7Mem`), every valid tree of iteration `c < M` is `ChainHonest … (M - c) c`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- What iteration `c`'s node pins: `__loop29`'s end `g^(c/2)` and start `1`, the parity bit
and whether the odd-depth round is called. -/
def ly7Q (sh c : ℕ) (σ : Val) : Prop :=
  σ (.n 61) = gen ^ (c / 2) ∧ σ (.n 65) = 1 ∧ σ (.n 62) = bitE (c % 2 = 1) ∧
    (σ (.n 70) = 0 ↔ sh = 0)

/-- The body's calls: `__loop29`, then the rounds of the branches taken. -/
noncomputable def ly7Csb (σ : Val) : List Call :=
  (lyA.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
    (if σ (.n 62) = 0 then [] else (ly62.filterMap Main.Stmt.callS).map (Main.mkCall σ)) ++
    (if σ (.n 70) = 0 then [] else (ly70.filterMap Main.Stmt.callS).map (Main.mkCall σ))

/-- The tail call. -/
noncomputable def ly7Tl (σ : Val) : Call :=
  Main.mkCall σ (some (.n 342), "__loop7", [.n 344, .n 1, .n 2, .n 3, .n 4, .n 5], [])

/-- One predicate per body call, none constraining. -/
def ly7Tsb (sh c : ℕ) : List (Tree → Prop) :=
  List.replicate (1 + (if c % 2 = 1 then 1 else 0) + (if sh = 1 then 1 else 0)) fun _ ↦ True

/-- **`__loop7`'s calls**: the body's, then the tail. -/
theorem ly7_calls (σ : Val) {es : List Ev} {vs : List V} (hw : walk σ lyBody = .ret es vs) :
    calls es = ly7Csb σ ++ [ly7Tl σ] := by
  rw [ly_walk σ, Out.ret.injEq] at hw
  rw [← hw.1]
  simp only [calls, List.filterMap_append]
  have hA := (Main.straight_parts σ lyA lyA_straight).2.2.2
  have hB := (Main.straight_parts σ lyB lyB_straight).2.2.2
  have h62 := calls_lyBr (σ := σ) (c := .n 62) ly62_straight
  have h70 := calls_lyBr (σ := σ) (c := .n 70) ly70_straight
  simp only [calls] at hA hB h62 h70
  rw [hA, hB, h62, lyB_calls]
  simp only [List.filterMap_cons, Ev.call?]
  rw [show (lyBr σ (.n 70) ly70).filterMap Ev.call? = _ from h70]
  simp [ly7Csb, ly7Tl, List.append_assoc]

/-- The memory iteration `c < M` reads its bounds from: `depth_shift`'s word `g^sh` and the slots'
`half` and `parity`. -/
def Ly7Mem (rd : Reader) (dsh gmu layers : E) (sh M : ℕ) : Prop :=
  LoadHolds rd (dsh * gmu) 0 (gen ^ sh) ∧
    ∀ j < M, LoadHolds rd layers (17 * (2 * j + sh) + 11) (gen ^ (j / 2)) ∧
      LoadHolds rd layers (17 * (2 * j + sh) + 12) (bitE (j % 2 = 1))

theorem tb_list_append_single_split {α β : Type} {r : α → β → Prop} :
    ∀ {cs : List α} {c : α} {ks : List β}, List.Forall₂ r (cs ++ [c]) ks →
      ∃ ks' k, ks = ks' ++ [k] ∧ List.Forall₂ r cs ks' ∧ r c k
  | [], c, ks, h => by
    obtain ⟨k, rfl, hk, -⟩ : ∃ k, ks = [k] ∧ r c k ∧ True := by
      cases h with
      | cons hr ht => cases ht; exact ⟨_, rfl, hr, trivial⟩
    exact ⟨[], k, rfl, List.Forall₂.nil, hk⟩
  | a :: cs, c, ks, h => by
    cases h with
    | cons hr ht =>
      obtain ⟨ks', k, rfl, h1, h2⟩ := tb_list_append_single_split ht
      exact ⟨_ :: ks', k, rfl, List.Forall₂.cons hr h1, h2⟩

theorem kidsValid_split {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {c : Call} {ks : List Tree}, Tree.KidsValid P rd σ (cs ++ [c]) ks →
      ∃ ks' k, ks = ks' ++ [k] ∧ ks'.length = cs.length ∧
        (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ)) ∧ k.name = c.f
  | [], c, ks, h => by
    match ks, h with
    | [k], ⟨hn, hk, _⟩ =>
      refine ⟨[], k, rfl, rfl, fun ht ↦ ?_, hn⟩
      rw [ite_eq_left ht] at hk; exact hk
  | a :: cs, c, ks, h => by
    match ks, h with
    | k :: ks, ⟨_, _, hks⟩ =>
      obtain ⟨ks', k', rfl, hl, h1, h2⟩ := kidsValid_split hks
      exact ⟨k :: ks', k', rfl, by simp [hl], h1, h2⟩

theorem bufsOkKids_last {P : Core.Program} : ∀ {ks : List Tree} {k : Tree},
    Tree.BufsOkKids P (ks ++ [k]) → k.BufsOk P
  | [], _, h => h.1
  | _ :: _, _, h => bufsOkKids_last h.2

theorem kidsT_true_last : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {ks : List Tree} {c : Call}
    {T : Tree → Prop} {k : Tree}, cs.length = Ts.length → ks.length = cs.length →
    (∀ T' ∈ Ts, ∀ t, T' t) → (c.taken = true → T k) → KidsT (cs ++ [c]) (Ts ++ [T]) (ks ++ [k])
  | [], [], [], _, _, _, _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, _ :: _, _, _, _, hl, hk, hT, h =>
    ⟨fun _ ↦ hT _ List.mem_cons_self _, kidsT_true_last (by simpa using hl) (by simpa using hk)
      (fun T' hT' ↦ hT T' (List.mem_cons_of_mem _ hT')) h⟩
  | [], _ :: _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl
  | [], [], _ :: _, _, _, _, _, hk, _, _ => by simp at hk
  | _ :: _, _ :: _, [], _, _, _, _, hk, _, _ => by simp at hk

theorem tb_gen_pow_add_eq_zero {a b : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) :
    gen ^ a + gen ^ b = 0 ↔ a = b := by
  constructor
  · intro h
    exact gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h)
  · rintro rfl; exact e_add_self _

set_option maxHeartbeats 1000000 in
/-- **`__loop7`'s valid trees are chains of honest shape**: iteration `c < M`, on a memory holding
its bounds' words, runs `M - c` iterations, each pinning `ly7Q`. -/
theorem ly7_chain {rd : Reader} {dsh gmu layers rounds : E} {sh M : ℕ} (hsh2 : sh < 2)
    (hM : 2 * M + 2 < 2 ^ 62) (hmem : Ly7Mem rd dsh gmu layers sh M) :
    ∀ n c (t : Tree) (rets : List E), c + n = M → 0 < n → t.name = "__loop7" →
      t.Valid coreProgram rd [gen ^ c, gen ^ M, dsh, gmu, layers, rounds] rets →
      t.BufsOk coreProgram →
      Budget.ChainHonest coreProgram "__loop7" (ly7Q sh) ly7Csb ly7Tl (fun _ ↦ []) (ly7Tsb sh)
        n c t := by
  obtain ⟨fn, hf, hpar, hbody⟩ := lyFound
  intro n
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
    intro c t rets hcn _ hname hv hb
    cases t with
    | phantom => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hname
      subst hname
      obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, hk⟩ := hv
      rw [hf, Option.some.injEq] at hf'
      subst hf'
      rw [hpar] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
      obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
      rw [hbody] at hw
      -- the body holds of `σ`
      have hH : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyBody True (fun _ ↦ True) :=
        holdsList_of_walk lyBody (by
          rw [hw]
          exact ⟨fun e he ↦ ⟨hes e he, fun _ _ _ _ ↦ trivial⟩, trivial⟩)
      rw [lyBody_eq, holdsList_append] at hH
      have hP : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ lyPre True (fun _ ↦ True) := hH
      have a := fun n a heq ↦ tb_holds_atom lyPre_noRet hP n a heq
      have m6 := a 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)
      have m7 := a 1 (.mul (.n 7) (.n 2) (.n 3)) (by decide +kernel)
      have l8 := a 2 (.load (.n 8) (.n 7) 0) (by decide +kernel)
      have m9 := a 3 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel)
      have m10 := a 4 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel)
      have m11 := a 5 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)
      have m12 := a 6 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
      have m13 := a 7 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
      have m14 := a 8 (.mul (.n 14) (.n 13) (.n 9)) (by decide +kernel)
      have m15 := a 9 (.mul (.n 15) (.n 4) (.n 14)) (by decide +kernel)
      have l61 := a 51 (.load (.n 61) (.n 15) 11) (by decide +kernel)
      have l62 := a 52 (.load (.n 62) (.n 15) 12) (by decide +kernel)
      have c65 := a 55 (.const (.n 65) (word 1 0 0)) (by decide +kernel)
      have a70 := a 58 (.add (.n 70) (.n 9) (.n 6)) (by decide +kernel)
      have c340 := a 289 (.const (.n 340) (word 2 0 0)) (by decide +kernel)
      have m341 := a 290 (.mul (.n 341) (.n 0) (.n 340)) (by decide +kernel)
      have a342 := a 291 (.add (.n 342) (.n 341) (.n 1)) (by decide +kernel)
      have c343 := a 292 (.const (.n 343) (word 2 0 0)) (by decide +kernel)
      have m344 := a 293 (.mul (.n 344) (.n 0) (.n 343)) (by decide +kernel)
      simp only [Atom.Holds] at m6 m7 l8 m9 m10 m11 m12 m13 m14 m15 l61 l62 c65 a70
      simp only [Atom.Holds] at c340 m341 a342 c343 m344
      obtain ⟨hsh, hslot⟩ := hmem
      have hc : c < M := by omega
      obtain ⟨hhalf, hpar'⟩ := hslot c hc
      rw [m7, h2, h3] at l8
      have e8 := tb_loadHolds_unique l8 hsh
      have e6 : σ (.n 6) = gen ^ (2 * c) := by rw [m6, h0, ← pow_add]; ring_nf
      have e9 : σ (.n 9) = gen ^ (2 * c + sh) := by rw [m9, e6, e8, pow_add]
      have e15 : σ (.n 15) = layers * gen ^ (17 * (2 * c + sh)) := by
        rw [m15, h4, m14, m13, m12, m11, m10, e9, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        ring_nf
      rw [e15, tb_loadHolds_mul_gen_pow] at l61 l62
      have e61 := tb_loadHolds_unique l61 hhalf
      have e62 := tb_loadHolds_unique l62 hpar'
      have e70 : σ (.n 70) = 0 ↔ sh = 0 := by
        rw [a70, e9, e6, tb_gen_pow_add_eq_zero (by omega) (by omega)]
        omega
      have e344 : σ (.n 344) = gen ^ (c + 1) := by rw [m344, c343, h0, tb_word_gen, pow_succ]
      have e342 : σ (.n 342) = gen ^ (c + 1) + gen ^ M := by
        rw [a342, m341, c340, h0, h1, tb_word_gen, pow_succ]
      have hQ : ly7Q sh c σ := ⟨e61, by rw [c65, tb_word_one], e62, e70⟩
      have hcalls := ly7_calls σ hw
      rw [hcalls] at hk
      obtain ⟨ks', k, rfl, hkl, hkv, hkn⟩ := kidsValid_split hk
      have hlen : (ly7Csb σ).length = (ly7Tsb sh c).length := by
        have hA : (lyA.filterMap Main.Stmt.callS).length = 1 := by rw [lyA_calls]; rfl
        have h62' : (ly62.filterMap Main.Stmt.callS).length = 1 := by decide +kernel
        have h70' : (ly70.filterMap Main.Stmt.callS).length = 1 := by decide +kernel
        simp only [ly7Csb, ly7Tsb, List.length_append, List.length_map, hA, List.length_replicate]
        rw [e62]
        congr 1
        · congr 1
          by_cases hc2 : c % 2 = 1
          · simp [hc2, bitE, h62']
          · simp [hc2, bitE]
        · by_cases hs : sh = 1
          · have : σ (.n 70) ≠ 0 := fun h ↦ by have := e70.mp h; omega
            simp [hs, this, h70']
          · have : σ (.n 70) = 0 := e70.mpr (by omega)
            simp [hs, this]
      refine ⟨σ, ks' ++ [k], ?_, hQ, fun fn'' es' vs' hf'' hw' ↦ ?_, hlen, ?_⟩
      · have hbufs := hb.1
        rw [hbufs, events_node hf (by rw [hbody]; exact hw)]
        have hal : allocs σ es = [] := by
          rw [ly_walk σ, Out.ret.injEq] at hw
          rw [← hw.1]
          have hA' := (Main.straight_parts σ lyA lyA_straight).2.1
          have hB' := (Main.straight_parts σ lyB lyB_straight).2.1
          have hA : lyA.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          have hB : lyB.filterMap Main.Stmt.allocSz = [] := by decide +kernel
          simp only [allocs, hA, hB, List.map_nil] at hA' hB'
          simp only [allocs, List.filterMap_append, hA', hB', List.nil_append, List.append_nil]
          by_cases e : σ (.n 62) = 0 <;> by_cases e' : σ (.n 70) = 0 <;>
            simp [lyBr, e, e', Ev.alloc?, Main.slEvs, ly62, ly70]
        rw [hal]
      · rw [hf, Option.some.injEq] at hf''
        subst hf''
        rw [hbody] at hw'
        exact ly7_calls σ hw'
      · refine kidsT_true_last (by rw [hlen]) (by rw [hkl, hlen])
          (fun T' hT' t ↦ by simp only [ly7Tsb, List.mem_replicate] at hT'; rw [hT'.2]; trivial)
          (fun ht ↦ ?_)
        have ht' : σ (.n 342) ≠ 0 := by simpa [ly7Tl, Main.mkCall] using ht
        have hc1 : c + 1 ≠ M := fun h ↦ ht' (by rw [e342, h]; exact e_add_self _)
        have hn : 0 < n := by omega
        have hkv' := hkv ht
        simp only [ly7Tl, Main.mkCall, List.map_cons, List.map_nil] at hkv'
        rw [e344, h1, h2, h3, h4, h5] at hkv'
        exact ih (c + 1) k _ (by omega) hn (by simpa [ly7Tl, Main.mkCall] using hkn) hkv'
          (bufsOkKids_last hb.2)

end
end LeanVM.Guest.B1.Tables
