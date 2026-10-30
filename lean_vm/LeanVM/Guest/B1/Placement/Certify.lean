/-
  LeanVM.Guest.B1.Placement.Certify

  B1 for `certify_placement`: the committed columns' log sizes, their hinted order certified to
  be `stackOffsets`'s, and the offsets laid out along it.
-/

module

public import LeanVM.Guest.B1.Placement.Common

/-!
# `certify_placement` (TRIAGE G #67)

`certify_placement(kappa_base, g_squares)` (G:2982-3015) builds each committed column's `g^κ`
from its source in `kappa_base` (`COL_KAPPA_SRC`, `COL_KAPPA_ADJ`: `colKappaSrc`, `colKappaAdj`),
reads the hinted order `col_sort_order`, range-checks each entry into the 99 columns and its
size below 34, checks that the sizes do not increase and that ties ascend, stores the running
offset `g^(Σ 2^κ)` of each column write-once, and returns the total. Write-once makes the order
injective, so a bijection (`Value.writeOnce_bijective`); the adjacent checks make it
`stackOffsets`'s `mergeSort` (`Value.eq_mergeSort_of_adjacent`), and the stored offsets are
`stackOffsets`'s (V:830).

The expansion is `cpBody`: the 99 columns' sizes (`cpInit`), the order hint, rank `0`, ranks
`1 .. 98` (`cpRank`, from value `97 + 26·r`) and the returns. Ported from the BLAKE2s-era proof
(92 columns).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^98`, as the data writes it. -/
theorem word_g98 : word 463856467968 0 0 = ofK (Parameters.gpow 98) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 463856467968) = ofK (Parameters.gpow 98)
  rw [show K.ofBits 463856467968 = Parameters.gpow 98 by decide +kernel]

theorem word_g33 : word 8589934592 0 0 = ofK (Parameters.gpow 33) := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 8589934592) = ofK (Parameters.gpow 33)
  rw [show K.ofBits 8589934592 = Parameters.gpow 33 by decide +kernel]

/-! ## The columns' sources -/

/-! ## The template -/

/-- Column `c`'s size, `col_kappa_g[g^c] = kappa_base[g^src] · g^adj`. -/
def cpInit (c : ℕ) : List Stmt :=
  if c < 4 then [.atom (.load (.n (3 + c)) (.n 0) 1), .atom (.load (.n (3 + c)) (.n 2) c)]
  else if c = 4 then
    [.atom (.load (.n 7) (.n 0) 0), .atom (.const (.n 8) (word (2 ^ 19) 0 0)),
      .atom (.mul (.n 9) (.n 7) (.n 8)), .atom (.load (.n 9) (.n 2) 4)]
  else if c = 5 then
    [.atom (.load (.n 10) (.n 0) 7), .atom (.const (.n 11) (word (2 ^ 6) 0 0)),
      .atom (.mul (.n 12) (.n 10) (.n 11)), .atom (.load (.n 12) (.n 2) 5)]
  else [.atom (.load (.n (c + 7)) (.n 0) (colKappaSrc c)), .atom (.load (.n (c + 7)) (.n 2) c)]

/-- `g^98`, the range check against the 99 columns. -/
abbrev w98 : E := word 463856467968 0 0

/-- `g^33`, the range check against `SIZE_BITS = 34`. -/
abbrev w33 : E := word 8589934592 0 0

/-- Rank `0`, values `108 .. 122`. -/
def cpRank0 : List Stmt :=
  [.atom (.load (.n 108) (.n 106) 0), .atom (.const (.n 109) w98),
    .atom (.rangeCheck (.n 108) (.n 110) (.n 111) (.n 112) (.n 109)),
    .atom (.mul (.n 113) (.n 2) (.n 108)), .atom (.load (.n 114) (.n 113) 0),
    .atom (.const (.n 115) (word 1 0 0)), .atom (.mul (.n 116) (.n 107) (.n 108)),
    .atom (.load (.n 115) (.n 116) 0), .atom (.const (.n 117) w33),
    .atom (.rangeCheck (.n 114) (.n 118) (.n 119) (.n 120) (.n 117)),
    .atom (.mul (.n 121) (.n 1) (.n 114)), .atom (.load (.n 122) (.n 121) 0)]

/-- The previous rank's column, by its value number. -/
def cpPc (r : ℕ) : ℕ := if r = 1 then 108 else 71 + 26 * r

/-- The previous rank's size, by its value number. -/
def cpPk (r : ℕ) : ℕ := if r = 1 then 114 else 77 + 26 * r

/-- Rank `r ≥ 1`, from value `B = 97 + 26·r`; the running offset is `B - 1`. -/
def cpRank (r : ℕ) : List Stmt :=
  let B := 97 + 26 * r
  [.atom (.load (.n B) (.n 106) r), .atom (.const (.n (B + 1)) w98),
    .atom (.rangeCheck (.n B) (.n (B + 2)) (.n (B + 3)) (.n (B + 4)) (.n (B + 1))),
    .atom (.mul (.n (B + 5)) (.n 2) (.n B)), .atom (.load (.n (B + 6)) (.n (B + 5)) 0),
    .atom (.const (.n (B + 7)) w33), .atom (.mul (.n (cpPk r)) (.n (B + 8)) (.n (B + 6))),
    .atom (.rangeCheck (.n (B + 8)) (.n (B + 9)) (.n (B + 10)) (.n (B + 11)) (.n (B + 7))),
    .atom (.add (.n (B + 12)) (.n (cpPk r)) (.n (B + 6))),
    .ite (.n (B + 12))
      [.atom (.const (.n (B + 13)) w98), .atom (.mul (.n B) (.n (B + 14)) (.n (cpPc r))),
        .atom (.rangeCheck (.n (B + 14)) (.n (B + 15)) (.n (B + 16)) (.n (B + 17)) (.n (B + 13)))]
      [],
    .atom (.mul (.n (B + 18)) (.n 107) (.n B)), .atom (.load (.n (B - 1)) (.n (B + 18)) 0),
    .atom (.const (.n (B + 19)) w33),
    .atom (.rangeCheck (.n (B + 6)) (.n (B + 20)) (.n (B + 21)) (.n (B + 22)) (.n (B + 19))),
    .atom (.mul (.n (B + 23)) (.n 1) (.n (B + 6))), .atom (.load (.n (B + 24)) (.n (B + 23)) 0),
    .atom (.mul (.n (B + 25)) (.n (B - 1)) (.n (B + 24)))]

/-- The expansion of `certify_placement`. -/
def cpBody : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 99))] ++ ((List.range 99).map cpInit).flatten ++
    [.atom (.hint (.alloc (.n 106) 99)),
      .atom (.hint (.witness "col_sort_order" (.heap (.n 106) 0 99))),
      .atom (.hint (.alloc (.n 107) 99))] ++
    cpRank0 ++ ((List.range 98).map fun r => cpRank (r + 1)).flatten ++
    [.atom (.copy (.n 2671) (.n 2670)), .atom (.copy (.n 2672) (.n 107)),
      .atom (.copy (.n 2673) (.n 2)), .ret [.n 2671, .n 2672, .n 2673]]

theorem core15_body : Fn.body Data.core15 = cpBody := tbStmtsEqb_sound (by decide +kernel)

/-! ## The template's conditions -/

/-- The value number of column `c`'s source word. -/
def cpW (c : ℕ) : ℕ := if c < 4 then 3 + c else if c = 4 then 7 else if c = 5 then 10 else c + 7

/-- The value number of column `c`'s size. -/
def cpV (c : ℕ) : ℕ := if c < 4 then 3 + c else if c = 4 then 9 else if c = 5 then 12 else c + 7

/-- Rank `r`'s column, size and running offset, by their value numbers. -/
def cpCol (r : ℕ) : ℕ := if r = 0 then 108 else 97 + 26 * r
def cpKap (r : ℕ) : ℕ := if r = 0 then 114 else 103 + 26 * r
def cpG (r : ℕ) : ℕ := if r = 0 then 115 else 96 + 26 * r

/-- A range check's atom holds. -/
def TbRcHolds (rd : Reader) (σ : Val) (x y t1 t2 k : ℕ) : Prop :=
  LoadHolds rd (σ (.n x)) 0 (σ (.n t1)) ∧ σ (.n k) = σ (.n x) * σ (.n y) ∧
    LoadHolds rd (σ (.n y)) 0 (σ (.n t2))

/-- What rank `r ≥ 1` asks of a valuation. -/
def CpRankOk (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  let B := 97 + 26 * r
  LoadHolds rd (σ (.n 106)) r (σ (.n B)) ∧ σ (.n (B + 1)) = w98 ∧
    TbRcHolds rd σ B (B + 2) (B + 3) (B + 4) (B + 1) ∧ σ (.n (B + 5)) = σ (.n 2) * σ (.n B) ∧
    LoadHolds rd (σ (.n (B + 5))) 0 (σ (.n (B + 6))) ∧ σ (.n (B + 7)) = w33 ∧
    σ (.n (cpPk r)) = σ (.n (B + 8)) * σ (.n (B + 6)) ∧
    TbRcHolds rd σ (B + 8) (B + 9) (B + 10) (B + 11) (B + 7) ∧
    σ (.n (B + 12)) = σ (.n (cpPk r)) + σ (.n (B + 6)) ∧
    (IsInK (σ (.n (B + 12))) ∧ (σ (.n (B + 12)) = 0 → σ (.n (B + 13)) = w98 ∧
      σ (.n B) = σ (.n (B + 14)) * σ (.n (cpPc r)) ∧
      TbRcHolds rd σ (B + 14) (B + 15) (B + 16) (B + 17) (B + 13))) ∧
    σ (.n (B + 18)) = σ (.n 107) * σ (.n B) ∧
    LoadHolds rd (σ (.n (B + 18))) 0 (σ (.n (B - 1))) ∧ σ (.n (B + 19)) = w33 ∧
    TbRcHolds rd σ (B + 6) (B + 20) (B + 21) (B + 22) (B + 19) ∧
    σ (.n (B + 23)) = σ (.n 1) * σ (.n (B + 6)) ∧
    LoadHolds rd (σ (.n (B + 23))) 0 (σ (.n (B + 24))) ∧
    σ (.n (B + 25)) = σ (.n (B - 1)) * σ (.n (B + 24))

section
variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holds_cpRank (r : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (cpRank r) True kret ↔ CpRankOk rd σ r := by
  simp only [cpRank, CpRankOk, TbRcHolds]
  rw [Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    tb_holds_ite_noRet _ _ _ rfl rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, implies_true]

/-- What column `c`'s size asks of a valuation. -/
def CpInitOk (rd : Reader) (σ : Val) (c : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) (colKappaSrc c) (σ (.n (cpW c))) ∧
    (colKappaAdj c ≠ 0 → σ (.n (cpW c + 1)) = word (2 ^ colKappaAdj c) 0 0 ∧
      σ (.n (cpV c)) = σ (.n (cpW c)) * σ (.n (cpW c + 1))) ∧
    LoadHolds rd (σ (.n 2)) c (σ (.n (cpV c)))

theorem holds_cpInit (c : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (cpInit c) True kret ↔ CpInitOk rd σ c := by
  unfold cpInit CpInitOk cpW cpV colKappaAdj colKappaSrc
  split_ifs <;> subst_vars <;>
    simp_all [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The body's conditions on one valuation. -/
theorem cp_body_iff (C : CallRel) (rd : Reader) (σ : Val) (rets : List E) :
    Stmt.HoldsList C rd σ cpBody False (fun rs => rs = rets) ↔
      (∀ c < 99, CpInitOk rd σ c) ∧
      LoadHolds rd (σ (.n 106)) 0 (σ (.n 108)) ∧ σ (.n 109) = w98 ∧
      TbRcHolds rd σ 108 110 111 112 109 ∧ σ (.n 113) = σ (.n 2) * σ (.n 108) ∧
      LoadHolds rd (σ (.n 113)) 0 (σ (.n 114)) ∧ σ (.n 115) = word 1 0 0 ∧
      σ (.n 116) = σ (.n 107) * σ (.n 108) ∧ LoadHolds rd (σ (.n 116)) 0 (σ (.n 115)) ∧
      σ (.n 117) = w33 ∧ TbRcHolds rd σ 114 118 119 120 117 ∧
      σ (.n 121) = σ (.n 1) * σ (.n 114) ∧ LoadHolds rd (σ (.n 121)) 0 (σ (.n 122)) ∧
      (∀ r < 98, CpRankOk rd σ (r + 1)) ∧
      σ (.n 2671) = σ (.n 2670) ∧ σ (.n 2672) = σ (.n 107) ∧ σ (.n 2673) = σ (.n 2) ∧
      [σ (.n 2671), σ (.n 2672), σ (.n 2673)] = rets := by
  rw [cpBody]
  simp only [holdsList_append, tb_holdsList_range_flatten 99 cpInit (fun c => by
      unfold cpInit; split_ifs <;> rfl),
    tb_holdsList_range_flatten 98 (fun r => cpRank (r + 1)) (fun _ => rfl), holds_cpInit,
    holds_cpRank, cpRank0, TbRcHolds, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, true_and]

/-- The function's body, simplified to its conditions. -/
theorem cp_unfold (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "certify_placement" args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      (∀ c < 99, CpInitOk rd σ c) ∧
      LoadHolds rd (σ (.n 106)) 0 (σ (.n 108)) ∧ σ (.n 109) = w98 ∧
      TbRcHolds rd σ 108 110 111 112 109 ∧ σ (.n 113) = σ (.n 2) * σ (.n 108) ∧
      LoadHolds rd (σ (.n 113)) 0 (σ (.n 114)) ∧ σ (.n 115) = word 1 0 0 ∧
      σ (.n 116) = σ (.n 107) * σ (.n 108) ∧ LoadHolds rd (σ (.n 116)) 0 (σ (.n 115)) ∧
      σ (.n 117) = w33 ∧ TbRcHolds rd σ 114 118 119 120 117 ∧
      σ (.n 121) = σ (.n 1) * σ (.n 114) ∧ LoadHolds rd (σ (.n 121)) 0 (σ (.n 122)) ∧
      (∀ r < 98, CpRankOk rd σ (r + 1)) ∧
      σ (.n 2671) = σ (.n 2670) ∧ σ (.n 2672) = σ (.n 107) ∧ σ (.n 2673) = σ (.n 2) ∧
      [σ (.n 2671), σ (.n 2672), σ (.n 2673)] = rets := by
  rw [tb_rel_iff_sem (by exact Program.find?_of_indexOf? (j := 15) (by decide +kernel) rfl),
    core15_body, show Fn.params Data.core15 = [.n 0, .n 1] from rfl, cpBody]
  simp only [holdsList_append, tb_holdsList_range_flatten 99 cpInit (fun c => by
      unfold cpInit; split_ifs <;> rfl),
    tb_holdsList_range_flatten 98 (fun r => cpRank (r + 1)) (fun _ => rfl), holds_cpInit,
    holds_cpRank, cpRank0, TbRcHolds, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, true_and]

end

/-! ## The meaning -/

/-- `stackOffsets`'s order of the sizes `κs` (V:878-879): larger first, ties by index. -/
def tbStackOrder (κs : List ℕ) : List ℕ :=
  (List.range κs.length).mergeSort (stackLe (κs.getD · 0))

/-- **`certify_placement(kappa_base, g_squares)`** (G:1959-1992; TRIAGE #41): the committed
columns' log sizes `κs`, each below 34 and `kappa_base[src]·g^adj` (`colKappaSrc`, `colKappaAdj`), are laid
out by `stackOffsets` (V:877): a run holds the hinted order, `tbStackOrder κs`, the returned `kaps`
holds `g^κ` per column, `offs` holds `g^offset` per column, and the total is
`g^(Σ 2^κ)`. -/
def MeaningCertifyPlacement (rd : Reader) : List E → List E → Prop
  | [kb, _], [gT, offs, kaps] => ∃ κs : List ℕ, κs.length = 99 ∧
      (∀ c < 99, κs.getD c 0 < 34 ∧
        ∃ w, LoadHolds rd kb (colKappaSrc c) w ∧ w * gen ^ colKappaAdj c = gen ^ κs.getD c 0) ∧
      (∃ so, TbReadsAt rd so ((tbStackOrder κs).map (gen ^ ·))) ∧
      TbReadsAt rd kaps (κs.map (gen ^ ·)) ∧ TbReadsAt rd offs ((stackOffsets κs).1.map (gen ^ ·)) ∧
      gT = gen ^ (κs.map (2 ^ ·)).sum
  | _, _ => False

/-! ## Soundness -/

/-- What rank `r` gives, uniformly. -/
def CpFacts (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  (∃ p < 99, σ (.n (cpCol r)) = gen ^ p) ∧ LoadHolds rd (σ (.n 106)) r (σ (.n (cpCol r))) ∧
    (∃ k < 34, σ (.n (cpKap r)) = gen ^ k) ∧
    LoadHolds rd (σ (.n 2) * σ (.n (cpCol r))) 0 (σ (.n (cpKap r))) ∧
    LoadHolds rd (σ (.n 107) * σ (.n (cpCol r))) 0 (σ (.n (cpG r))) ∧
    (∃ t, LoadHolds rd (σ (.n 1) * σ (.n (cpKap r))) 0 t ∧
      σ (.n (cpG (r + 1))) = σ (.n (cpG r)) * t) ∧
    (1 ≤ r → (∃ d < 34, σ (.n (cpKap (r - 1))) = gen ^ d * σ (.n (cpKap r))) ∧
      (σ (.n (cpKap (r - 1))) + σ (.n (cpKap r)) = 0 →
        ∃ e < 99, σ (.n (cpCol r)) = gen ^ e * σ (.n (cpCol (r - 1)))))

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

theorem rc113 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w98) (h : TbRcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 99, σ (.n x) = gen ^ e :=
  tb_rc_sound' hμ Lm (K := 99) (by omega) (by decide) (by rw [hk]; exact word_g98) h.1 h.2.1 h.2.2

theorem rc34 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w33) (h : TbRcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 34, σ (.n x) = gen ^ e :=
  tb_rc_sound' hμ Lm (K := 34) (by omega) (by decide) (by rw [hk]; exact word_g33) h.1 h.2.1 h.2.2

theorem cpFacts_succ {σ : Val} {r : ℕ} (h : CpRankOk Lm.read σ (r + 1)) : CpFacts Lm.read σ (r + 1) := by
  obtain ⟨l0, c1, rc0, m5, l6, c7, m8, rc8, a12, ⟨hK, hz⟩, m18, l18, c19, rc6, m23, l24, m25⟩ := h
  have hB : ∀ j, 97 + 26 * (r + 1) + j = 123 + 26 * r + j := fun j => by ring
  have ecol : cpCol (r + 1) = 97 + 26 * (r + 1) := by
    simp only [cpCol, Nat.add_one_ne_zero, ↓reduceIte]
  have ekap : cpKap (r + 1) = 97 + 26 * (r + 1) + 6 := by
    simp only [cpKap, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eG : cpG (r + 1) = 97 + 26 * (r + 1) - 1 := by
    simp only [cpG, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eG1 : cpG (r + 1 + 1) = 97 + 26 * (r + 1) + 25 := by
    simp only [cpG, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have ePk : cpPk (r + 1) = cpKap r := by unfold cpPk cpKap; split_ifs <;> omega
  have ePc : cpPc (r + 1) = cpCol r := by unfold cpPc cpCol; split_ifs <;> omega
  unfold CpFacts
  rw [ecol, ekap, eG, eG1]
  refine ⟨rc113 hμ Lm c1 rc0, l0, rc34 hμ Lm c19 rc6, by rw [← m5]; exact l6,
    by rw [← m18]; exact l18, ⟨_, by rw [← m23]; exact l24, m25⟩, fun _ => ⟨?_, fun h0 => ?_⟩⟩
  · obtain ⟨d, hd, hq⟩ := rc34 hμ Lm c7 rc8
    refine ⟨d, hd, ?_⟩
    rw [Nat.add_sub_cancel, ← ePk, m8, hq]
  · rw [Nat.add_sub_cancel, ← ePk, ← a12] at h0
    obtain ⟨c13, m14, rc14⟩ := hz h0
    obtain ⟨e, he, hq⟩ := rc113 hμ Lm c13 rc14
    exact ⟨e, he, by rw [m14, hq, Nat.add_sub_cancel, ePc]⟩

end

/-- Choices below `n` as a function. -/
theorem tb_exists_fun_of_forall {α : Type} [Inhabited α] {n : ℕ} {P : ℕ → α → Prop}
    (h : ∀ r < n, ∃ a, P r a) : ∃ f : ℕ → α, ∀ r < n, P r (f r) := by
  classical
  exact ⟨fun r => if hr : r < n then Classical.choose (h r hr) else default,
    fun r hr => by simp only [hr, ↓reduceDIte]; exact Classical.choose_spec (h r hr)⟩

theorem tb_prefixSize_map (s : ℕ → ℕ) (l : List ℕ) (r : ℕ) :
    tbPrefixSize s l r = tbPrefixSize id (l.map s) r := by
  simp [tbPrefixSize, List.map_take, List.map_map, Function.comp_def]

theorem tb_prefixSize_le (k : ℕ → ℕ) (hk : ∀ r < 99, k r < 34) :
    ∀ r ≤ 99, tbPrefixSize id ((List.range 99).map k) r ≤ r * 2 ^ 33
  | 0, _ => by simp [tbPrefixSize]
  | r + 1, hr => by
    rw [tb_prefixSize_succ _ _ _ (by simp; omega)]
    have := tb_prefixSize_le k hk r (by omega)
    simp only [id, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show r < 99 by omega), Option.map_some, Option.getD_some]
    have : 2 ^ k r ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by have := hk r (by omega); omega)
    nlinarith

theorem tb_prefixSize_strict (k : ℕ → ℕ) :
    ∀ r r', r < r' → r' ≤ 99 →
      tbPrefixSize id ((List.range 99).map k) r < tbPrefixSize id ((List.range 99).map k) r'
  | r, r' + 1, h, h' => by
    rw [tb_prefixSize_succ _ _ _ (by simp; omega)]
    rcases Nat.lt_or_ge r r' with hlt | hge
    · have := tb_prefixSize_strict k r r' hlt (by omega)
      have : 0 < 2 ^ (((List.range 99).map k).getD r' 0) := Nat.two_pow_pos _
      simp only [id]; omega
    · obtain rfl : r = r' := by omega
      have : 0 < 2 ^ (((List.range 99).map k).getD r 0) := Nat.two_pow_pos _
      simp only [id]; omega

theorem cp_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {kb sq : E}
    (hsq : ∀ j < 34, LoadHolds Lm.read sq j (gen ^ 2 ^ j)) (rets : List E)
    (h : coreProgram.Rel Lm.read "certify_placement" [kb, sq] rets) :
    MeaningCertifyPlacement Lm.read [kb, sq] rets := by
  rw [cp_unfold] at h
  obtain ⟨σ, hp, hinit, l101, c102, rc101, m106, l107, c108, m109, l108, c110, rc107, m114, l115,
    hranks, e3049, e3050, e3051, hret⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1⟩ := hp
  -- the uniform facts of every rank
  have hf : ∀ r < 99, CpFacts Lm.read σ r := fun r hr => by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · show CpFacts Lm.read σ 0
      unfold CpFacts
      simp only [cpCol, cpKap, cpG, ↓reduceIte, Nat.zero_add, one_ne_zero, Nat.reduceMul,
        Nat.reduceAdd]
      refine ⟨rc113 hμ Lm c102 rc101, l101, rc34 hμ Lm c110 rc107, by rw [← m106]; exact l107,
        by rw [← m109]; exact l108, ⟨_, by rw [← m114]; exact l115, ?_⟩, fun h => absurd h (by omega)⟩
      rw [c108, tb_word_one, one_mul]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact cpFacts_succ hμ Lm (hranks r' (by omega))
  obtain ⟨π, hπ⟩ := tb_exists_fun_of_forall (n := 99) (fun r hr => (hf r hr).1)
  obtain ⟨k, hk⟩ := tb_exists_fun_of_forall (n := 99) (fun r hr => (hf r hr).2.2.1)
  set S := fun r => tbPrefixSize id ((List.range 99).map k) r
  have hS92 : ∀ r ≤ 99, S r < 2 ^ 62 := fun r hr => by
    show tbPrefixSize id ((List.range 99).map k) r < 2 ^ 62
    have := tb_prefixSize_le k (fun r hr => (hk r hr).1) r hr
    have : r * 2 ^ 33 ≤ 99 * 2 ^ 33 := Nat.mul_le_mul_right _ hr
    omega
  -- the running offsets
  have hG : ∀ r ≤ 99, σ (.n (cpG r)) = gen ^ S r := fun r hr => by
    induction r with
    | zero => show σ (.n 115) = gen ^ 0; rw [c108, tb_word_one, pow_zero]
    | succ r ih =>
      obtain ⟨-, -, -, -, -, ⟨t, lt, et⟩, -⟩ := hf r (by omega)
      rw [(hk r (by omega)).2, tb_loadHolds_mul_gen_pow, h1, Nat.add_zero] at lt
      rw [et, ih (by omega), tb_loadHolds_unique lt (hsq _ (hk r (by omega)).1), ← pow_add]
      simp only [S]
      rw [tb_prefixSize_succ _ _ _ (by simp; omega)]
      simp [List.getElem?_range (show r < 99 by omega)]
  -- write-once: the order is injective
  have hoff : ∀ r < 99, LoadHolds Lm.read (σ (.n 107)) (π r) (gen ^ S r) := fun r hr => by
    have := (hf r hr).2.2.2.2.1
    rw [(hπ r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero, hG r (by omega)] at this
    exact this
  have hinj : ∀ r < 99, ∀ r' < 99, π r = π r' → r = r' := fun r hr r' hr' he => by
    have e := tb_loadHolds_unique (hoff r hr) (he ▸ hoff r' hr')
    have := tb_gen_pow_inj' (by have := hS92 r (by omega); omega) (by have := hS92 r' (by omega); omega) e
    rcases Nat.lt_trichotomy r r' with h | h | h
    · exact absurd this (Nat.ne_of_lt (tb_prefixSize_strict k r r' h (by omega)))
    · exact h
    · exact absurd this (Nat.ne_of_gt (tb_prefixSize_strict k r' r h (by omega)))
  -- pigeonhole: a bijection
  have hsurj : ∀ c < 99, ∃ r < 99, π r = c := by
    let f : Fin 99 → Fin 99 := fun r => ⟨π r, (hπ r r.2).1⟩
    have hfi : Function.Injective f := fun a b hab =>
      Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val hab))
    have hfb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩
    intro c hc
    obtain ⟨r, hr⟩ := hfb.2 ⟨c, hc⟩
    exact ⟨r, r.2, congrArg Fin.val hr⟩
  obtain ⟨πi, hπi⟩ := tb_exists_fun_of_forall (n := 99) (fun c hc => (hsurj c hc))
  have hπiπ : ∀ r < 99, πi (π r) = r := fun r hr =>
    hinj _ (hπi _ (hπ r hr).1).1 _ hr (hπi _ (hπ r hr).1).2
  set κs := (List.range 99).map fun c => k (πi c)
  have hlen : κs.length = 99 := by simp [κs]
  have hsize : ∀ c < 99, κs.getD c 0 = k (πi c) := fun c hc => by
    simp [κs, List.getElem?_range hc]
  have hsizeπ : ∀ r < 99, κs.getD (π r) 0 = k r := fun r hr => by
    rw [hsize _ (hπ r hr).1, hπiπ r hr]
  -- the order is stackOffsets's
  set ord := (List.range 99).map π
  have hordget : ∀ r < 99, ord.getD r 0 = π r := fun r hr => by
    simp [ord, List.getElem?_range hr]
  have hperm : ord.Perm (List.range 99) := by
    rw [List.perm_ext_iff_of_nodup _ List.nodup_range]
    · intro a
      simp only [ord, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact (hπ r hr).1
      · intro ha; obtain ⟨r, hr, he⟩ := hsurj a ha; exact ⟨r, hr, he⟩
    · exact (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb he =>
        hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) he
  have hord : ord = tbStackOrder κs := by
    rw [tbStackOrder, hlen]
    refine eq_mergeSort_of_adjacent (κs.getD · 0) hperm fun i hi => ?_
    have hi' : i + 1 < 99 := by simpa [ord] using hi
    simp only [ord, List.getElem_map, List.getElem_range]
    rw [hsizeπ i (by omega), hsizeπ (i + 1) hi']
    obtain ⟨-, -, -, -, -, -, hadj⟩ := hf (i + 1) hi'
    obtain ⟨⟨d, hd, hdk⟩, htie⟩ := hadj (by omega)
    rw [Nat.add_sub_cancel, (hk i (by omega)).2, (hk (i + 1) hi').2] at hdk htie
    have e1 := tb_gen_pow_eq_mul (by have := (hk i (by omega)).1; omega)
      (by have := (hk (i + 1) hi').1; omega) (by omega) hdk
    refine ⟨by omega, fun heq => ?_⟩
    have h0 : gen ^ k i + gen ^ k (i + 1) = 0 := by rw [heq]; exact e_add_self _
    obtain ⟨e, he, hcol⟩ := htie h0
    rw [(hπ (i + 1) hi').2, (hπ i (by omega)).2] at hcol
    have := tb_gen_pow_eq_mul (by have := (hπ (i + 1) hi').1; omega)
      (by have := (hπ i (by omega)).1; omega) (by omega) hcol
    omega
  -- the sums
  have hSord : ∀ r ≤ 99, tbPrefixSize (κs.getD · 0) ord r = S r := fun r hr => by
    have hmap : ord.map (κs.getD · 0) = (List.range 99).map k := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hsizeπ r (List.mem_range.mp hr)
    rw [tb_prefixSize_map, hmap]
  have hkaps : ∀ r < 99, LoadHolds Lm.read (σ (.n 2)) (π r) (gen ^ k r) := fun r hr => by
    have := (hf r hr).2.2.2.1
    rw [(hπ r hr).2, (hk r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero] at this
    exact this
  have hκc : ∀ r < 99, κs.getD (π r) 0 = k r := hsizeπ
  subst hret
  refine ⟨κs, hlen, fun c hc => ⟨?_, ?_⟩, ⟨σ (.n 106), tbReadsAt_map_iff.mpr fun r hr => ?_⟩,
    tbReadsAt_map_iff.mpr fun c hc => ?_, tbReadsAt_map_iff.mpr fun c hc => ?_, ?_⟩
  · rw [hsize c hc]; exact (hk _ (hπi c hc).1).1
  · obtain ⟨lw, hadj, lv⟩ := hinit c hc
    have hv : σ (.n (cpV c)) = gen ^ κs.getD c 0 := by
      obtain ⟨r, hr, hrc⟩ : ∃ r, r < 99 ∧ π r = c := ⟨πi c, hπi c hc⟩
      have := hkaps _ hr
      rw [hrc] at this
      rw [tb_loadHolds_unique lv this, hsize c hc, ← hrc, hπiπ r hr]
    refine ⟨σ (.n (cpW c)), by rw [← h0]; exact lw, ?_⟩
    by_cases ha : colKappaAdj c = 0
    · rw [ha, pow_zero, mul_one, ← hv]
      unfold colKappaAdj at ha; unfold cpV cpW
      split_ifs at ha ⊢ <;> rfl
    · obtain ⟨ew, ev⟩ := hadj ha
      rw [← hv, ev, ew, tb_word_two_pow (by unfold colKappaAdj; split_ifs <;> omega)]
  · have hr' : r < 99 := by rwa [← hord, List.length_map, List.length_range] at hr
    rw [← hord, hordget r hr', ← (hπ r hr').2]
    exact (hf r hr').2.1
  · have hc' : c < 99 := by rwa [hlen] at hc
    obtain ⟨r, hr, hrc⟩ : ∃ r, r < 99 ∧ π r = c := ⟨πi c, hπi c hc'⟩
    rw [hsize c hc', e3051, ← hrc, hπiπ r hr]
    exact hkaps r hr
  · have hc' : c < 99 := by rwa [tb_stackOffsets_length, hlen] at hc
    obtain ⟨r, hr, hrc⟩ : ∃ r, r < 99 ∧ π r = c := ⟨πi c, hπi c hc'⟩
    rw [e3050, ← hrc, ← hordget r hr, hord, tbStackOrder, tb_stackOffsets_fst κs r (by omega),
      ← tbStackOrder, ← hord, hSord r (by omega), hordget r hr]
    exact hoff r hr
  · have hfull : tbPrefixSize (κs.getD · 0) ord 99 = (ord.map fun i => 2 ^ κs.getD i 0).sum := by
      have := tb_prefixSize_full (κs.getD · 0) ord
      rwa [show ord.length = 99 by simp [ord]] at this
    rw [e3049, show σ (.n 2670) = σ (.n (cpG 99)) from rfl, hG 99 le_rfl, ← hSord 99 le_rfl, hfull]
    refine congrArg (fun x => gen ^ x) ?_
    rw [(hperm.map _).sum_eq]
    simp only [κs, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun c hc => by
      simp only [Function.comp_apply]; rw [hsize c (List.mem_range.mp hc)])

/-- **`certify_placement` is sound** on every memory of at most `2^32` words. -/
theorem certify_placement_holds {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) :
    certify_placement_Spec Lm.read := by
  intro logMem hs kb sq rets hlm hl hhs hkb hsq h
  have hsq' : ∀ j < 34, LoadHolds Lm.read sq j (gen ^ 2 ^ j) := fun j hj => by
    have := hsq j (by simp [gSquaresList]; omega)
    simpa [gSquaresList] using this
  have hm := cp_sound hμ Lm hsq' rets h
  match rets, hm with
  | [gT, offs, kaps], ⟨κs, hlen, hcol, _, hkaps, hoffs, hgT⟩ =>
    have hck := committedKappas_columnKappas logMem hs hl
    have hκ : κs = committedKappas (columnKappas logMem guestLogBytecode hs) := by
      rw [hck]
      apply List.ext_getElem (by simp [hlen])
      intro c hc1 hc2
      have hc : c < 99 := by rwa [hlen] at hc1
      obtain ⟨hlt, w, hw, hwe⟩ := hcol c hc
      have hsrc : colKappaSrc c < 8 := by unfold colKappaSrc; split_ifs <;> omega
      have hbase : (1 :: gen ^ logMem :: hs.map (gen ^ ·)).length = 8 := by simp [hl]
      have hwv := hkb (colKappaSrc c) (by rw [hbase]; exact hsrc)
      have hw' := tb_loadHolds_unique hw hwv
      have hb : (1 :: gen ^ logMem :: hs.map (gen ^ ·))[colKappaSrc c]'(by rw [hbase]; exact hsrc) =
          gen ^ (0 :: logMem :: hs).getD (colKappaSrc c) 0 := by
        rcases Nat.lt_or_ge (colKappaSrc c) 2 with h2 | h2
        · interval_cases (colKappaSrc c) <;> simp
        · obtain ⟨t, ht⟩ : ∃ t, colKappaSrc c = t + 2 := ⟨colKappaSrc c - 2, by omega⟩
          simp only [ht, List.getElem_cons_succ, List.getElem_map, List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by omega)]
      rw [hw', hb, ← pow_add] at hwe
      have hbnd : (0 :: logMem :: hs).getD (colKappaSrc c) 0 < 33 := by
        rcases Nat.lt_or_ge (colKappaSrc c) 2 with h2 | h2
        · interval_cases (colKappaSrc c)
          · simp
          · simp; omega
        · obtain ⟨t, ht⟩ : ∃ t, colKappaSrc c = t + 2 := ⟨colKappaSrc c - 2, by omega⟩
          simp only [ht, List.getD_cons_succ]
          rw [List.getD_eq_getElem _ _ (by omega)]
          have := hhs _ (List.getElem_mem (by omega : t < hs.length))
          omega
      have hadj : colKappaAdj c ≤ 19 := by unfold colKappaAdj; split_ifs <;> omega
      have e := tb_gen_pow_inj' (by omega) (by omega) hwe
      rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem κs 0 hc1, ← e]
    refine ⟨offs, kaps, ?_, columnKappas_length _ _ _, ?_, ?_⟩
    · rw [hgT, hκ]; rfl
    · rw [← hκ]; exact hkaps
    · rw [← hκ]; exact hoffs

end
end LeanVM.Guest.B1.Tables
