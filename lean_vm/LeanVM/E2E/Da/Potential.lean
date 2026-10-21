/-
  LeanVM.E2E.Da.Potential

  The potential of the DA leg: a function of the oracle's log bounding the probability that a
  membership challenge chain accepts rows that are not codewords, and its step inequality.
-/

module

public import LeanVM.E2E.Da.Tree

/-!
# The DA leg: the potential

The membership challenges of a root `ρ` (`Da.membershipChallengesWith`) are squeezed from the
chain state after the label's hash has observed `ρ`'s two halves; the observation of the second
half is an entry of the log whose input completes `ρ` (`DaRootOf`), the chain's *anchor*. The
rows committed to `ρ` by the log *before* the anchor (`ColCommits`) are fixed when the anchor is
drawn, and so is the set of challenge lists accepting rows of them that are not all codewords
(`DaBadSet`). The potential (`daPot pc`) is `1` on a log that failed for DA (`FailDA`), and
otherwise the sum over the anchors of the log of the probability, given the squeezes the log
already answers from the anchor (`gch`), that the remaining challenges, drawn uniformly
(`uni`), land in that set.

**The step inequality** (`daPot_step`). For a log `ℓ` and an input `t` it does not answer,

  `(∑ u, daPot pc (ℓ ++ [(t, u)])) / |Digest| ≤ daPot pc ℓ + (14 / |E| + 4 (|ℓ| + 1) / |Digest|)`:

the new entry fails for DA for at most `4 (|ℓ| + 1)` answers (`sum_badDA_le`); otherwise every
old anchor's term is a martingale step, the challenge of a uniform digest being uniform
(`gch_step`), and a new anchor's term starts at most at `14 / |E|`: the committed rows are
unique (`rows_eq_of_colTree`) and a row that is not a codeword is orthogonal to the dual
codeword for at most `14 |E|^13` of the `|E|^14` challenges (`LeanDa.card_acceptSet_le`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Uniform challenges -/

/-- The expectation of `f` on `n` uniform challenges. -/
noncomputable def uni : ℕ → (List E → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f []
  | n + 1, f => (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, uni n fun rest ↦ f (c :: rest)

/-- A sum over `E^(n+1)` splits off the first challenge. -/
theorem sum_fin_succ_E (n : ℕ) (g : (Fin (n + 1) → E) → ℝ≥0∞) :
    ∑ z : Fin (n + 1) → E, g z = ∑ c : E, ∑ z : Fin n → E, g (Fin.cons c z) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ E).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

/-- The expectation over `n` uniform challenges is the average over `E^n`. -/
theorem uni_eq : ∀ (n : ℕ) (f : List E → ℝ≥0∞),
    uni n f = ((Fintype.card E : ℝ≥0∞)⁻¹) ^ n * ∑ z : Fin n → E, f (List.ofFn z)
  | 0, f => by simp [uni]
  | n + 1, f => by
    rw [uni]
    simp only [uni_eq n]
    rw [← Finset.mul_sum, ← mul_assoc, ← pow_succ', sum_fin_succ_E]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- A sum of the indicator of a finite set is its size. -/
theorem sum_ind_mem {α : Type} [Fintype α] (A : Finset α) :
    ∑ z : α, ind (z ∈ A) = (A.card : ℝ≥0∞) := by
  classical
  have : ∀ z, ind (z ∈ A) = if z ∈ A then 1 else 0 := fun z ↦ by
    by_cases h : z ∈ A
    · rw [ind_of h, ite_eq_left h]
    · rw [ind_of_not h, ite_eq_right h]
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The expectation of an indicator over `14` challenges, for a set of at most `14 |E|^13`
challenge vectors. -/
theorem uni_ind_le {S : Set (List E)}
    (hS : ∑ z : Fin 14 → E, ind (List.ofFn z ∈ S) ≤ 14 * (Fintype.card E : ℝ≥0∞) ^ 13) :
    uni 14 (fun zs ↦ ind (zs ∈ S)) ≤ 14 * (Fintype.card E : ℝ≥0∞)⁻¹ := by
  rw [uni_eq]
  have hE0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hEt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((Fintype.card E : ℝ≥0∞)⁻¹) ^ 14 * ∑ z : Fin 14 → E, ind (List.ofFn z ∈ S)
      ≤ ((Fintype.card E : ℝ≥0∞)⁻¹) ^ 14 * (14 * (Fintype.card E : ℝ≥0∞) ^ 13) :=
        mul_le_mul_right hS _
    _ = 14 * (Fintype.card E : ℝ≥0∞)⁻¹ := by
        rw [show ((Fintype.card E : ℝ≥0∞)⁻¹) ^ 14 * (14 * (Fintype.card E : ℝ≥0∞) ^ 13) =
          14 * (Fintype.card E : ℝ≥0∞)⁻¹ * (((Fintype.card E : ℝ≥0∞)⁻¹) ^ 13 *
            (Fintype.card E : ℝ≥0∞) ^ 13) by ring, ← ENNReal.inv_pow,
          ENNReal.inv_mul_cancel (pow_ne_zero _ hE0) (ENNReal.pow_ne_top hEt), mul_one]

/-! ## The squeeze chain -/

/-- **The value of a squeeze chain** from the state `d` with `n` challenges left and payoff `f`
of the full challenge list: follow the squeezes the log answers; at the first it does not, the
expectation over the remaining challenges drawn uniformly. -/
noncomputable def gch (ℓ : Log) : Digest → ℕ → (List E → ℝ≥0∞) → ℝ≥0∞
  | _, 0, f => f []
  | d, n + 1, f => match look ℓ (sqIn d) with
    | some d' => gch ℓ d' n fun rest ↦ f (daChallenge d' :: rest)
    | none => uni (n + 1) f

/-- A chain whose next squeeze is not answered is the expectation over uniform challenges. -/
theorem gch_of_none {ℓ : Log} {d : Digest} (h : look ℓ (sqIn d) = none) :
    ∀ (n : ℕ) (f : List E → ℝ≥0∞), gch ℓ d n f = uni n f
  | 0, _ => rfl
  | n + 1, f => by simp only [gch, h]

/-- A chain whose next squeeze is answered follows it. -/
theorem gch_of_some {ℓ : Log} {d d' : Digest} (h : look ℓ (sqIn d) = some d') (n : ℕ)
    (f : List E → ℝ≥0∞) :
    gch ℓ d (n + 1) f = gch ℓ d' n fun rest ↦ f (daChallenge d' :: rest) := by
  simp only [gch, h]

/-- A squeeze is the chain's hash of the squeeze input. -/
theorem compressWordsWith_sq (ℓ : Log) (d : Digest) :
    Da.compressWordsWith (Da.daHash (look ℓ)) (Da.toBytes d) [0, 0, 0, LeanDa.K.ofBits 2] =
      Da.daHash (look ℓ) (sqIn d) := rfl

/-- **A chain the log answers in full is the payoff of its challenges.** -/
theorem gch_of_squeezes {ℓ : Log} :
    ∀ (n : ℕ) (d : Digest) (zs : List E) (f : List E → ℝ≥0∞),
      Da.squeezesWith (Da.daHash (look ℓ)) n (Da.toBytes d) = some zs → gch ℓ d n f = f zs
  | 0, d, zs, f, h => by
    simp only [Da.squeezesWith, pure, Option.some.injEq] at h
    subst h; rfl
  | n + 1, d, zs, f, h => by
    simp only [Da.squeezesWith, compressWordsWith_sq, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨s, hs, rest, hrest, rfl⟩ := h
    simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at hs
    obtain ⟨d', hd', rfl⟩ := hs
    rw [gch_of_some hd', gch_of_squeezes n d' rest _ hrest]
    rfl

/-- **The chain is a supermartingale**: averaged over a fresh answer `u` at `t`, on the answers
`F u` whose squeeze input the new log does not answer, the chain's value after the entry
`(t, u)` is at most its value before. -/
theorem gch_step {ℓ : Log} {t : Bytes} (F : Digest → Prop)
    (hF : ∀ u, F u → look (ℓ ++ [(t, u)]) (sqIn u) = none) :
    ∀ (n : ℕ) (d : Digest) (f : List E → ℝ≥0∞),
      (∑ u, ind (F u) * gch (ℓ ++ [(t, u)]) d n f) / Fintype.card Digest ≤ gch ℓ d n f
  | 0, d, f => avg_ind_mul_const_le F _
  | n + 1, d, f => by
    rcases hl : look ℓ (sqIn d) with _ | d'
    · rw [gch_of_none hl]
      by_cases ht : sqIn d = t
      · have hl' : ∀ u, look (ℓ ++ [(t, u)]) (sqIn d) = some u := fun u ↦ by
          rw [ht] at hl ⊢; exact look_append_single_self hl u
        have hterm : ∀ u, ind (F u) * gch (ℓ ++ [(t, u)]) d (n + 1) f ≤
            uni n fun rest ↦ f (daChallenge u :: rest) := by
          intro u
          rw [gch_of_some (hl' u)]
          by_cases hu : F u
          · rw [ind_of hu, one_mul, gch_of_none (hF u hu)]
          · rw [ind_of_not hu, zero_mul]; exact bot_le
        calc (∑ u, ind (F u) * gch (ℓ ++ [(t, u)]) d (n + 1) f) / Fintype.card Digest
            ≤ (∑ u, uni n fun rest ↦ f (daChallenge u :: rest)) / Fintype.card Digest := by
              gcongr with u; exact hterm u
          _ = (∑ c : E, uni n fun rest ↦ f (c :: rest)) / Fintype.card E :=
              sum_daChallenge_div fun c ↦ uni n fun rest ↦ f (c :: rest)
          _ = uni (n + 1) f := by rw [uni, ENNReal.div_eq_inv_mul]
      · have hl' : ∀ u, look (ℓ ++ [(t, u)]) (sqIn d) = none := fun u ↦ by
          rw [look_append_single_of_ne ht, hl]
        simp only [gch_of_none (hl' _)]
        exact avg_ind_mul_const_le F _
    · have hl' : ∀ u, look (ℓ ++ [(t, u)]) (sqIn d) = some d' := fun u ↦
        look_append_single_of_some hl t u
      rw [gch_of_some hl, Finset.sum_congr rfl fun u _ ↦ by rw [gch_of_some (hl' u)]]
      exact gch_step F hF n d' _

/-! ## The anchors and their bad challenges -/

/-- Rows of the shape the DA claim asks (`Witness.Opens`). -/
def RowsShape (rows : List (List K)) : Prop :=
  1 ≤ rows.length ∧ rows.length ≤ LeanDa.maxRows ∧ ∀ row ∈ rows, row.length = 2 ^ LeanDa.logM

/-- **The log commits the rows to `ρ`**: rows of the claim's shape whose column tree it
answers, and whose column root it hashes after some row root into `ρ`. -/
def ColCommits (ℓ : Log) (pc : LeanDa.Digest) (rows : List (List K)) (ρ : LeanDa.Digest) :
    Prop :=
  RowsShape rows ∧ ∃ rt c, colTreeWith (Da.daHash (look ℓ)) pc rows = some c ∧
    Da.daHash (look ℓ) (LeanDa.pairBytes rt c) = some ρ

/-- A row as a codeword's function. -/
def rowFn (row : List K) : LeanDa.Row := fun b ↦ row.getD b 0

/-- The challenges `zs` accept the row: it is orthogonal to their dual codeword. -/
def Accepts (zs : List E) (row : List K) : Prop :=
  ∃ z : Fin 14 → E, zs = List.ofFn z ∧ LeanDa.dot (LeanDa.dual z) (rowFn row) = 0

/-- **The bad challenges of `ρ` in `ℓ`**: those accepting every row of rows `ℓ` commits to `ρ`
that are not all codewords. -/
def DaBadSet (pc : LeanDa.Digest) (ℓ : Log) (ρ : LeanDa.Digest) : Set (List E) :=
  {zs | ∃ rows, ColCommits ℓ pc rows ρ ∧ (∃ row ∈ rows, rowFn row ∉ LeanDa.rsCode) ∧
    ∀ row ∈ rows, Accepts zs row}

open Classical in
/-- The root the input `x` completes in `ℓ`, if any. -/
noncomputable def anchorRoot (ℓ : Log) (x : Bytes) : Option LeanDa.Digest :=
  if h : ∃ ρ, DaRootOf ℓ x ρ then some h.choose else none

/-- The root an input completes is the completed root. -/
theorem anchorRoot_eq_some {ℓ : Log} {x : Bytes} {ρ : LeanDa.Digest} (h : DaRootOf ℓ x ρ) :
    anchorRoot ℓ x = some ρ := by
  have hex : ∃ ρ, DaRootOf ℓ x ρ := ⟨ρ, h⟩
  rw [anchorRoot, dite_eq_left hex, daRootOf_unique hex.choose_spec h]

/-- The term of entry `i`: if its input completes a root `ρ` in the entries before it, the
value of the squeeze chain from its output with the bad challenges of `ρ` there. -/
noncomputable def daTerm (pc : LeanDa.Digest) (ℓ : Log) (i : ℕ) : ℝ≥0∞ :=
  match ℓ[i]? with
  | none => 0
  | some e => match anchorRoot (ℓ.take i) e.1 with
    | none => 0
    | some ρ => gch ℓ e.2 LeanDa.logK fun zs ↦ ind (zs ∈ DaBadSet pc (ℓ.take i) ρ)

open Classical in
/-- **The DA potential**: `1` on a log that failed for DA, otherwise the sum of the terms. -/
noncomputable def daPot (pc : LeanDa.Digest) (ℓ : Log) : ℝ≥0∞ :=
  if FailDA pc ℓ then 1 else ∑ i ∈ Finset.range ℓ.length, daTerm pc ℓ i

/-- The empty log has potential zero. -/
theorem daPot_nil (pc : LeanDa.Digest) : daPot pc [] = 0 := by
  simp [daPot, not_failDA_nil]

/-! ## The step inequality -/

section Step

variable {pc : LeanDa.Digest} {ℓ : Log} {t : Bytes}

/-- An answer that does not fail leaves the next squeeze unanswered. -/
theorem look_sqIn_of_not_badDA {u : Digest} (h : ¬ BadDA pc ℓ t u) :
    look (ℓ ++ [(t, u)]) (sqIn u) = none := by
  rw [look, logLookup_eq_none_iff]
  intro hm
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton] at hm
  refine h (Or.inr (Or.inr ⟨sqIn u, ?_, Or.inl (by simp [chunk0, sqIn, digestBytes_length])⟩))
  rcases hm with hm | hm
  · exact List.mem_cons_of_mem _ hm
  · rw [hm]; exact List.mem_cons_self

/-- An old entry's term after one more entry. -/
theorem daTerm_append_old {i : ℕ} (hi : i < ℓ.length) (u : Digest) :
    daTerm pc (ℓ ++ [(t, u)]) i = match anchorRoot (ℓ.take i) ℓ[i].1 with
      | none => 0
      | some ρ => gch (ℓ ++ [(t, u)]) ℓ[i].2 LeanDa.logK
          fun zs ↦ ind (zs ∈ DaBadSet pc (ℓ.take i) ρ) := by
  rw [daTerm, List.getElem?_append_left hi, List.getElem?_eq_getElem hi,
    List.take_append_of_le_length hi.le]

/-- An entry's term. -/
theorem daTerm_eq {i : ℕ} (hi : i < ℓ.length) :
    daTerm pc ℓ i = match anchorRoot (ℓ.take i) ℓ[i].1 with
      | none => 0
      | some ρ => gch ℓ ℓ[i].2 LeanDa.logK fun zs ↦ ind (zs ∈ DaBadSet pc (ℓ.take i) ρ) := by
  rw [daTerm, List.getElem?_eq_getElem hi]

/-- The new entry's term. -/
theorem daTerm_append_new (u : Digest) :
    daTerm pc (ℓ ++ [(t, u)]) ℓ.length = match anchorRoot ℓ t with
      | none => 0
      | some ρ => gch (ℓ ++ [(t, u)]) u LeanDa.logK fun zs ↦ ind (zs ∈ DaBadSet pc ℓ ρ) := by
  rw [daTerm, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_singleton,
    ite_eq_left rfl, List.take_left' rfl]

/-- **Old terms are supermartingales.** -/
theorem daTerm_step_old {i : ℕ} (hi : i < ℓ.length) :
    (∑ u, ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) i) / Fintype.card Digest ≤
      daTerm pc ℓ i := by
  simp only [daTerm_append_old hi, daTerm_eq hi]
  split
  · simp
  · exact gch_step _ (fun _ ↦ look_sqIn_of_not_badDA) _ _ _

/-- **The bad challenges of a log without failure are few**: the committed rows are unique, and
a row that is not a codeword accepts at most `14 |E|^13` challenge vectors. -/
theorem card_daBadSet_le (h : ¬ FailDA pc ℓ) (ρ : LeanDa.Digest) :
    ∑ z : Fin 14 → E, ind (List.ofFn z ∈ DaBadSet pc ℓ ρ) ≤
      14 * (Fintype.card E : ℝ≥0∞) ^ 13 := by
  by_cases hS : ∃ z : Fin 14 → E, List.ofFn z ∈ DaBadSet pc ℓ ρ
  · obtain ⟨z₀, rows₀, hc₀, ⟨w₀, hw₀, hnc⟩, -⟩ := hS
    obtain ⟨hshape₀, rt₀, c₀, hcol₀, hroot₀⟩ := hc₀
    calc ∑ z : Fin 14 → E, ind (List.ofFn z ∈ DaBadSet pc ℓ ρ)
        ≤ ∑ z : Fin 14 → E, ind (LeanDa.dot (LeanDa.dual z) (rowFn w₀) = 0) := by
          refine Finset.sum_le_sum fun z _ ↦ ind_mono fun hz ↦ ?_
          obtain ⟨rows, hc, -, hacc⟩ := hz
          -- The rows are the rows: one column root, so one set of rows.
          obtain ⟨hshape, rt, c, hcol, hroot⟩ := hc
          obtain ⟨-, rfl⟩ := pairBytes_inj (daHash_inj_of_not_failDA h hroot hroot₀)
          have hrows := rows_eq_of_colTree (fun x y v ↦ daHash_inj_of_not_failDA h)
            (daHash_ne_pc_of_not_failDA h) hshape.2.2 hshape₀.2.2 hcol hcol₀
          subst hrows
          obtain ⟨z', hz', hdot⟩ := hacc w₀ hw₀
          cases List.ofFn_injective hz'
          exact hdot
      _ = ∑ z : Fin 14 → E, ind (z ∈ LeanDa.acceptSet (rowFn w₀)) :=
          Finset.sum_congr rfl fun z _ ↦ by rw [LeanDa.mem_acceptSet]
      _ = ((LeanDa.acceptSet (rowFn w₀)).card : ℝ≥0∞) := sum_ind_mem _
      _ ≤ 14 * (Fintype.card E : ℝ≥0∞) ^ 13 := by
          have h' := Nat.cast_le (α := ℝ≥0∞) |>.mpr (LeanDa.card_acceptSet_le hnc)
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h'
          exact h'
  · push Not at hS
    simp only [ind_of_not (hS _), Finset.sum_const_zero]
    exact bot_le

/-- **A new term starts at most at `14 / |E|`.** -/
theorem daTerm_step_new (h : ¬ FailDA pc ℓ) :
    (∑ u, ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) ℓ.length) / Fintype.card Digest ≤
      14 * (Fintype.card E : ℝ≥0∞)⁻¹ := by
  simp only [daTerm_append_new]
  split
  · simp
  · rename_i ρ _
    have hterm : ∀ u, ind (¬ BadDA pc ℓ t u) * gch (ℓ ++ [(t, u)]) u LeanDa.logK
        (fun zs ↦ ind (zs ∈ DaBadSet pc ℓ ρ)) ≤
        ind (¬ BadDA pc ℓ t u) * (14 * (Fintype.card E : ℝ≥0∞)⁻¹) := by
      intro u
      by_cases hu : BadDA pc ℓ t u
      · simp [ind_of_not (not_not.mpr hu)]
      · rw [gch_of_none (look_sqIn_of_not_badDA hu)]
        gcongr
        exact uni_ind_le (card_daBadSet_le h ρ)
    exact (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hterm u) _).trans
      (avg_ind_mul_const_le _ _)

/-- **The step inequality of the DA potential.** -/
theorem daPot_step :
    (∑ u, daPot pc (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      daPot pc ℓ + (14 * (Fintype.card E : ℝ≥0∞)⁻¹ +
        ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest) := by
  have hD0 : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hDt : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  by_cases hf : FailDA pc ℓ
  · have h1 : ∀ u, daPot pc (ℓ ++ [(t, u)]) = 1 := fun u ↦ by
      rw [daPot, ite_eq_left ((failDA_append pc ℓ t u).mpr (Or.inl hf))]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ENNReal.div_self hD0 hDt, daPot, ite_eq_left hf]
    exact le_self_add
  · -- Each answer: one on failure, otherwise the old terms and the new one.
    have hpt : ∀ u, daPot pc (ℓ ++ [(t, u)]) ≤ ind (BadDA pc ℓ t u) +
        ((∑ i ∈ Finset.range ℓ.length, ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) i) +
          ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) ℓ.length) := by
      intro u
      by_cases hu : BadDA pc ℓ t u
      · rw [daPot, ite_eq_left ((failDA_append pc ℓ t u).mpr (Or.inr hu)), ind_of hu]
        exact le_self_add
      · rw [daPot, ite_eq_right (by rw [failDA_append]; tauto), ind_of_not hu, ind_of hu, zero_add,
          List.length_append, List.length_singleton, Finset.sum_range_succ]
        simp
    calc (∑ u, daPot pc (ℓ ++ [(t, u)])) / Fintype.card Digest
        ≤ (∑ u, (ind (BadDA pc ℓ t u) +
            ((∑ i ∈ Finset.range ℓ.length, ind (¬ BadDA pc ℓ t u) *
              daTerm pc (ℓ ++ [(t, u)]) i) +
            ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) ℓ.length))) /
            Fintype.card Digest := by gcongr with u; exact hpt u
      _ = (∑ u, ind (BadDA pc ℓ t u)) / Fintype.card Digest +
            ((∑ i ∈ Finset.range ℓ.length, (∑ u, ind (¬ BadDA pc ℓ t u) *
              daTerm pc (ℓ ++ [(t, u)]) i) / Fintype.card Digest) +
            (∑ u, ind (¬ BadDA pc ℓ t u) * daTerm pc (ℓ ++ [(t, u)]) ℓ.length) /
              Fintype.card Digest) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ENNReal.add_div, ENNReal.add_div,
            Finset.sum_comm]
          congr 2
          simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]
      _ ≤ ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest +
            ((∑ i ∈ Finset.range ℓ.length, daTerm pc ℓ i) +
              14 * (Fintype.card E : ℝ≥0∞)⁻¹) := by
          gcongr with i hi
          · exact sum_badDA_le pc ℓ t
          · exact daTerm_step_old (Finset.mem_range.mp hi)
          · exact daTerm_step_new hf
      _ = daPot pc ℓ + (14 * (Fintype.card E : ℝ≥0∞)⁻¹ +
            ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest) := by
          rw [daPot, ite_eq_right hf]
          ring

end Step

end
end LeanVM.E2E
