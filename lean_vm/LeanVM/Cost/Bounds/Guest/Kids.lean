module

public import LeanVM.Cost.Bounds.Guest.Da
public import LeanVM.Cost.Decoder.Kids

/-!
# Bounds on the guest decoder's prices: the children

The coverage table's readers and the children (`Cost/Decoder/Kids.lean`), in the price `R` of a
read of the memory, `S` of `main`'s valuation and `W` of the child proofs' reader `wV`; every
count below `2^34` (`gLog_lt`), every search over at most `2^34` slots:

* a mark, a running count (`markOf_cost`, `countOf_cost`: `S + R + G + 21692`), the
  children's count (`nKids_cost`);
* the child a mark falls in (`kidOfAt_cost`, **`kidOf_cost`**: a search over the children), the
  slot a mark is in (`slotOf_cost`), the marks in a segment (`segCount_cost`);
* **`kidStmt_cost`**: a child's statement, for each of its claims a search over the slots, so at
  most `2^35` searches of `2^34` marks: `kidStmtPrice G R S ≈ 2^69·(S + R + G)`;
* `subArgs_cost`, **`decKid_cost`** (`decKidPrice G R S W`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

/-- **`List.find?`** (`find?.c21`): `9` per element and the predicate's price, `3`. -/
theorem find_cost (hP : Includes P Auto.List.find?.c21.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pV : MachineValue) (hp : ∀ a, RunsApp P pV [encodeValue a] (encodeValue (p a)))
    (B : ℕ) : ∀ l : List α, (∀ a ∈ l, appCost P pV [encodeValue a] ≤ B) →
      machineCost P Auto.List.find?.c21.costIdx [pV, encodeValue l] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.find?.c21.costEq_nil P hP p pV hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.find?.c21.costEq_cons P hP p pV hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    cases p a <;> dsimp only <;> nlinarith

/-- `List.range n` and a `List.find?` over it, the predicate's price at most `B` on `k < n`,
`n ≤ M`: at most `(B + 26)·M + 9`. -/
theorem rangeFind_le (hr : Includes P Auto.List.range.loop.c20.costDeps)
    (hm : Includes P Auto.List.find?.c21.costDeps)
    (p : ℕ → Bool) (pV : MachineValue) (hp : ∀ a, RunsApp P pV [encodeValue a] (encodeValue (p a)))
    (B n M : ℕ) (hn : n ≤ M) (hM : M < 2 ^ 64) (hB : ∀ k < n, appCost P pV [encodeValue k] ≤ B) :
    machineCost P Auto.List.range.loop.c20.costIdx [encodeValue n, encodeValue ([] : List ℕ)] +
      machineCost P Auto.List.find?.c21.costIdx [pV, encodeValue (List.range n)] ≤
        (B + 26) * M + 9 := by
  have h1 := rangeLoop_cost P hr n [] (by omega)
  have h2 := find_cost P hm p pV hp B (List.range n) (fun k hk ↦ hB k (List.mem_range.1 hk))
  rw [List.length_range] at h2
  have := Nat.mul_le_mul_left (B + 9) hn
  nlinarith

/-- `List.range n`, a `List.filter` over it and the result's length, the predicate's price at most
`B` on `k < n`, `n ≤ M`: at most `(B + 37)·M + 12`. -/
theorem rangeFilterLength_le (hr : Includes P Auto.List.range.loop.c20.costDeps)
    (hm : Includes P Auto.List.filter.c140.costDeps) (hl : Includes P Auto.List.length.c229.costDeps)
    (p : ℕ → Bool) (pV : MachineValue) (hp : ∀ a, RunsApp P pV [encodeValue a] (encodeValue (p a)))
    (B n M : ℕ) (hn : n ≤ M) (hM : M < 2 ^ 64) (hB : ∀ k < n, appCost P pV [encodeValue k] ≤ B) :
    machineCost P Auto.List.range.loop.c20.costIdx [encodeValue n, encodeValue ([] : List ℕ)] +
      machineCost P Auto.List.filter.c140.costIdx [pV, encodeValue (List.range n)] +
      machineCost P Auto.List.length.c229.costIdx [encodeValue ((List.range n).filter p)] ≤
        (B + 37) * M + 12 := by
  have h1 := rangeLoop_cost P hr n [] (by omega)
  have h2 := filter_cost P hm p pV hp B (List.range n) (fun k hk ↦ hB k (List.mem_range.1 hk))
  have hlen : ((List.range n).filter p).length ≤ n :=
    (List.length_filter_le _ _).trans (by rw [List.length_range])
  have h3 := length_cost P hl ((List.range n).filter p) (by omega)
  rw [List.length_range] at h2
  have := Nat.mul_le_mul_left (B + 13) hn
  nlinarith

theorem segCount_le (rd : Reader) (σ : Val) (lo len a b : ℕ) : segCount rd σ lo len a b ≤ len := by
  unfold segCount
  exact (List.length_filter_le _ _).trans (by rw [List.length_range])

theorem slotOf_le (rd : Reader) (σ : Val) (lo len e : ℕ) : slotOf rd σ lo len e ≤ len := by
  unfold slotOf
  generalize hf : (List.range len).find? _ = o
  cases o with
  | none => simp
  | some s =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    simp only [Option.getD_some]; omega

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hrd hR hσ hS

/-- A mark (`markOfC`), at a slot below `2^40`: `S + R + G + 21692`. -/
theorem markOf_cost (hP : Includes P Decoder.markOfC.costDeps) (hG : GLogBound P G) (s : ℕ) (hs : s < 2 ^ 40) :
    machineCost P Decoder.markOfC.costIdx [rdV, σV, encodeValue s] ≤ S + R + G + 21692 := by
  rw [Decoder.markOfC.costEq P hP rd rdV hrd σ σV hσ]
  have := hG (cellAt rd (σ (.n 67)) s)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 67)) s hs
  have := hS (.n 67)
  omega

/-- A running count (`countOfC`), at a child below `2^40`: `S + R + G + 21692`. -/
theorem countOf_cost (hP : Includes P Decoder.countOfC.costDeps) (hG : GLogBound P G) (c : ℕ) (hc : c < 2 ^ 40) :
    machineCost P Decoder.countOfC.costIdx [rdV, σV, encodeValue c] ≤ S + R + G + 21692 := by
  rw [Decoder.countOfC.costEq P hP rd rdV hrd σ σV hσ]
  have := hG (cellAt rd (σ (.n 380)) c)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 380)) c hc
  have := hS (.n 380)
  omega

omit hrd hR in
/-- The number of children (`nKidsC`): `S + G + 11`. -/
theorem nKids_cost (hP : Includes P Decoder.nKidsC.costDeps) (hG : GLogBound P G) :
    machineCost P Decoder.nKidsC.costIdx [σV] ≤ S + G + 11 := by
  rw [Decoder.nKidsC.costEq P hP σ σV hσ]
  have := hG (σ (.n 6))
  have := hS (.n 6)
  omega

/-- Whether a child's segment ends after a mark (`endsAfterC`): `S + R + G + 21702`. -/
theorem endsAfter_cost (hP : Includes P Decoder.endsAfterC.costDeps) (hG : GLogBound P G) (e c : ℕ) (he : e < 2 ^ 64)
    (hc : c + 1 < 2 ^ 40) :
    machineCost P Decoder.endsAfterC.costIdx [rdV, σV, encodeValue e, encodeValue c] ≤
      S + R + G + 21702 := by
  rw [Decoder.endsAfterC.costEq P hP rd rdV hrd σ σV hσ]
  have := countOf_cost P hrd hR hσ hS (by includes) hG (c + 1) hc
  have := gLog_lt (cellAt rd (σ (.n 380)) (c + 1))
  have hco : countOf rd σ (c + 1) < 2 ^ 64 := by unfold countOf; omega
  rw [limbs_of_lt (by omega : c < 2 ^ 64), limbs_of_lt he, limbs_of_lt hco]
  omega

/-- The child of `n ≤ 2^34` a mark falls in (`kidOfAtC`): `(S + R + G + 21733)·2^34 + 22`. -/
theorem kidOfAt_cost (hP : Includes P Decoder.kidOfAtC.costDeps) (hG : GLogBound P G) (e n : ℕ) (he : e < 2 ^ 64)
    (hn : n ≤ 2 ^ 34) :
    machineCost P Decoder.kidOfAtC.costIdx [rdV, σV, encodeValue e, encodeValue n] ≤
      (S + R + G + 21733) * 2 ^ 34 + 22 := by
  rw [Decoder.kidOfAtC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeFind_le P (by includes) (by includes) _
    (.closure Decoder.kidOfAtC.lam0.costIdx [rdV, σV, encodeValue e])
    (fun c ↦ RunsApp.of_spec (Decoder.kidOfAtC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ e c))
    (S + R + G + 21707) n (2 ^ 34) hn (by norm_num) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.kidOfAtC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := endsAfter_cost P hrd hR hσ hS (by includes) hG e c he (by omega)
      omega)
  cases List.find? (Decoder.endsAfter rd σ e) (List.range n) <;> dsimp only <;> omega

/-- **The child a mark falls in** (`kidOfC`): at most
`S + G + (S + R + G + 21733)·2^34 + 39`. -/
theorem kidOf_cost (hP : Includes P Decoder.kidOfC.costDeps) (hG : GLogBound P G) (e : ℕ) (he : e < 2 ^ 64) :
    machineCost P Decoder.kidOfC.costIdx [rdV, σV, encodeValue e] ≤
      S + G + (S + R + G + 21733) * 2 ^ 34 + 39 := by
  rw [Decoder.kidOfC.costEq P hP rd rdV hrd σ σV hσ]
  have := nKids_cost P hσ hS (by includes) hG
  have := kidOfAt_cost P hrd hR hσ hS (by includes) hG e (nKids σ) he (gLog_lt _).le
  omega

/-- The slot of a region of `len ≤ 2^34` slots holding a mark (`slotOfC`), `lo ≤ 2^35`:
`(S + R + G + 21728)·2^34 + 24`. -/
theorem slotOf_cost (hP : Includes P Decoder.slotOfC.costDeps) (hG : GLogBound P G) (lo len e : ℕ) (hlo : lo ≤ 2 ^ 35)
    (hlen : len ≤ 2 ^ 34) (he : e < 2 ^ 64) :
    machineCost P Decoder.slotOfC.costIdx
      [rdV, σV, encodeValue lo, encodeValue len, encodeValue e] ≤
        (S + R + G + 21728) * 2 ^ 34 + 24 := by
  rw [Decoder.slotOfC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeFind_le P (by includes) (by includes) _
    (.closure Decoder.slotOfC.lam0.costIdx [rdV, σV, encodeValue lo, encodeValue e])
    (fun s ↦ RunsApp.of_spec (Decoder.slotOfC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ
      lo e s))
    (S + R + G + 21702) len (2 ^ 34) hlen (by norm_num) (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.slotOfC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := markOf_cost P hrd hR hσ hS (by includes) hG (lo + s) (by omega)
      have := gLog_lt (cellAt rd (σ (.n 67)) (lo + s))
      have hm : markOf rd σ (lo + s) < 2 ^ 64 := by unfold markOf; omega
      rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : s < 2 ^ 64),
        limbs_of_lt hm, limbs_of_lt he]
      omega)
  cases List.find? (fun s ↦ decide (markOf rd σ (lo + s) = e)) (List.range len) <;> dsimp only <;>
    omega

/-- The marks of a region of `len ≤ 2^34` slots in `[a, b)` (`segCountC`), `lo ≤ 2^35`:
`(2·S + 2·R + 2·G + 43442)·2^34 + 28`. -/
theorem segCount_cost (hP : Includes P Decoder.segCountC.costDeps) (hG : GLogBound P G) (lo len a b : ℕ)
    (hlo : lo ≤ 2 ^ 35) (hlen : len ≤ 2 ^ 34) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    machineCost P Decoder.segCountC.costIdx
      [rdV, σV, encodeValue lo, encodeValue len, encodeValue a, encodeValue b] ≤
        (2 * S + 2 * R + 2 * G + 43442) * 2 ^ 34 + 28 := by
  rw [Decoder.segCountC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeFilterLength_le P (by includes) (by includes) (by includes) _
    (.closure Decoder.segCountC.lam0.costIdx
      [rdV, σV, encodeValue lo, encodeValue a, encodeValue b])
    (fun s ↦ RunsApp.of_spec (Decoder.segCountC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ
      lo a b s))
    (2 * S + 2 * R + 2 * G + 43405) len (2 ^ 34) hlen (by norm_num) (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.segCountC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := markOf_cost P hrd hR hσ hS (by includes) hG (lo + s) (by omega)
      have := gLog_lt (cellAt rd (σ (.n 67)) (lo + s))
      have hm : markOf rd σ (lo + s) < 2 ^ 64 := by unfold markOf; omega
      rw [limbs_of_lt (by omega : lo < 2 ^ 64), limbs_of_lt (by omega : s < 2 ^ 64),
        limbs_of_lt hm, limbs_of_lt ha, limbs_of_lt hb]
      split_ifs <;> omega)
  omega

/-- A child's statement's price. -/
@[expose] def kidStmtPrice (G R S : ℕ) : ℕ :=
  2 * (S + R + G + 21692) + 1 + 3 * (S + G) +
    2 * ((2 * S + 2 * R + 2 * G + 43442) * 2 ^ 34 + 28) +
    ((2 * S + G + 4 * R + ((S + R + G + 21728) * 2 ^ 34 + 24) + 657463 + 28) *
      2 ^ 34 + 9) +
    ((3 * S + 2 * G + 4 * R + ((S + R + G + 21728) * 2 ^ 34 + 24) + 657475 + 28) *
      2 ^ 34 + 9) +
    (2 * S + 2 * R + 43416) + 3 * S + 3 * (1 + 184560) + (24 * R + 521058) + 819 + 2514

/-- **A child's statement** (`kidStmtC`), child `c < 2^34`: at most `kidStmtPrice G R S`. -/
theorem kidStmt_cost (hP : Includes P Decoder.kidStmtC.costDeps) (hG : GLogBound P G) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P Decoder.kidStmtC.costIdx [rdV, σV, encodeValue c] ≤ kidStmtPrice G R S := by
  rw [Decoder.kidStmtC.costEq P hP rd rdV hrd σ σV hσ]
  have hca := countOf_cost P hrd hR hσ hS (by includes) hG c (by omega)
  have hcb := countOf_cost P hrd hR hσ hS (by includes) hG (c + 1) (by omega)
  have na : countOf rd σ c < 2 ^ 34 := by unfold countOf; exact gLog_lt _
  have nb : countOf rd σ (c + 1) < 2 ^ 34 := by unfold countOf; exact gLog_lt _
  have lx : lxSlots σ < 2 ^ 34 := by unfold lxSlots; exact gLog_lt _
  have ls : lsSlots σ < 2 ^ 34 := by unfold lsSlots; exact gLog_lt _
  have g40 := hG (σ (.n 40))
  have g41 := hG (σ (.n 41))
  have s1 := segCount_cost P hrd hR hσ hS (by includes) hG 0 (lxSlots σ) (countOf rd σ c)
    (countOf rd σ (c + 1)) (by omega) lx.le (by omega) (by omega)
  have s2 := segCount_cost P hrd hR hσ hS (by includes) hG (lxSlots σ) (lsSlots σ) (countOf rd σ c)
    (countOf rd σ (c + 1)) (by omega) ls.le (by omega) (by omega)
  have nx := segCount_le rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))
  have ns := segCount_le rd σ (lxSlots σ) (lsSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))
  have m0 := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.kidStmtC.lam0.costIdx [rdV, σV, encodeValue (countOf rd σ c)])
    (fun j ↦ RunsApp.of_spec (Decoder.kidStmtC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ
      _ j))
    (2 * S + G + 4 * R + ((S + R + G + 21728) * 2 ^ 34 + 24) + 657463)
    (segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))) (2 ^ 34) (by omega)
    (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.kidStmtC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := hG (σ (.n 40))
      have := hS (.n 53); have := hS (.n 40)
      have := slotOf_cost P hrd hR hσ hS (by includes) hG 0 (lxSlots σ) (countOf rd σ c + j)
        (by omega) lx.le (by omega)
      have := slotOf_le rd σ 0 (lxSlots σ) (countOf rd σ c + j)
      have := xmssAt_cost P hrd hR (by includes) (σ (.n 53))
        (slotOf rd σ 0 (lxSlots σ) (countOf rd σ c + j)) (by omega)
      rw [limbs_of_lt (by omega : countOf rd σ c < 2 ^ 64), limbs_of_lt (by omega : j < 2 ^ 64)]
      omega)
  have m1 := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.kidStmtC.lam1.costIdx [rdV, σV,
      encodeValue (segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))),
      encodeValue (countOf rd σ (c + 1)), encodeValue (countOf rd σ c)])
    (fun j ↦ RunsApp.of_spec (Decoder.kidStmtC.lam1.costSpec P (by includes) rd rdV hrd σ σV hσ
      _ _ _ j))
    (3 * S + 2 * G + 4 * R + ((S + R + G + 21728) * 2 ^ 34 + 24) + 657475)
    (segCount rd σ (lxSlots σ) (lsSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))) (2 ^ 34)
    (by omega) (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.kidStmtC.lam1.costEq P (by includes) rd rdV hrd σ σV hσ]
      have := hG (σ (.n 40))
      have := hG (σ (.n 41))
      have := hS (.n 56); have := hS (.n 40); have := hS (.n 41)
      have := slotOf_cost P hrd hR hσ hS (by includes) hG (lxSlots σ) (lsSlots σ)
        (countOf rd σ c +
          segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1)) + j)
        (by omega) ls.le (by omega)
      have := slotOf_le rd σ (lxSlots σ) (lsSlots σ)
        (countOf rd σ c +
          segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1)) + j)
      have := sphincsAt_cost P hrd hR (by includes) (σ (.n 56))
        (slotOf rd σ (lxSlots σ) (lsSlots σ)
          (countOf rd σ c +
            segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1)) + j)) (by omega)
      generalize segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1)) = x at *
      generalize countOf rd σ c = y at *
      rw [limbs_of_lt (by omega : y < 2 ^ 64), limbs_of_lt (by omega : x < 2 ^ 64),
        limbs_of_lt (by omega : y + x < 2 ^ 64), limbs_of_lt (by omega : j < 2 ^ 64)]
      omega)
  have hd := daDigestAt_cost P hrd hR hσ hS (by includes) c (by omega)
  have hp := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen (24 * c) 39
    (by norm_num) (by norm_num) (by omega)
  have hr := readCells_cost P hrd hR (by includes)
    (σ (.n 377) * LeanVM.Protocol.Verifier.gen ^ (24 * c)) 24 (by norm_num)
  have hf := deferOfCells_cost P (by includes)
    (readCells rd (σ (.n 377) * LeanVM.Protocol.Verifier.gen ^ (24 * c)) 24)
  have := hS (.n 40); have := hS (.n 41); have := hS (.n 377)
  rw [limbs_of_lt (by omega : c < 2 ^ 64)]
  unfold kidStmtPrice
  omega

/-- The words of a child's `verify_sub` call (`subArgsC`), child `c < 2^34`:
`9·S + 2·R + 599545`. -/
theorem subArgs_cost (hP : Includes P Decoder.subArgsC.costDeps) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P Decoder.subArgsC.costIdx [rdV, σV, encodeValue c] ≤ 9 * S + 2 * R + 599545 := by
  rw [Decoder.subArgsC.costEq P hP rd rdV hrd σ σV hσ]
  have := cellAt_cost P hrd hR (by includes) (σ (.n 365)) (2 * c) (by omega)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 365)) (2 * c + 1) (by omega)
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen (24 * c) 39
    (by norm_num) (by norm_num) (by omega)
  have := hS (.n 365); have := hS (.n 47); have := hS (.n 48); have := hS (.n 49)
  have := hS (.n 50); have := hS (.n 371)
  limbs_one
  omega

section Proofs

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
  {W : ℕ} (hW : ∀ a : List E, appCost P wVV [encodeValue a] ≤ W)
include hwV hW

/-- A child's price. -/
@[expose] def decKidPrice (G R S W : ℕ) : ℕ :=
  kidStmtPrice G R S + 3 * S + 3 * (1 + 184560) + (24 * R + 521058) + 819 +
    (9 * S + 2 * R + 599545) + W + 2433

/-- **A child** (`decKidC`), `c < 2^34`: at most `decKidPrice G R S W`. -/
theorem decKid_cost (hP : Includes P Decoder.decKidC.costDeps) (hG : GLogBound P G) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P Decoder.decKidC.costIdx [rdV, σV, wVV, encodeValue c] ≤ decKidPrice G R S W := by
  rw [Decoder.decKidC.costEq P hP rd rdV hrd σ σV hσ wV wVV hwV]
  have := kidStmt_cost P hrd hR hσ hS (by includes) hG c hc
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen (24 * c) 39
    (by norm_num) (by norm_num) (by omega)
  have := readCells_cost P hrd hR (by includes)
    (σ (.n 371) * LeanVM.Protocol.Verifier.gen ^ (24 * c)) 24 (by norm_num)
  have := fixedOfCells_cost P (by includes)
    (readCells rd (σ (.n 371) * LeanVM.Protocol.Verifier.gen ^ (24 * c)) 24)
  have := subArgs_cost P hrd hR hσ hS (by includes) c hc
  have := hW (subArgs rd σ c)
  have := hS (.n 371)
  rw [limbs_of_lt (by omega : c < 2 ^ 64)]
  unfold decKidPrice
  omega

end Proofs

end Reader

end

end LeanVM.Cost.Bounds.Guest
