/-
  LeanerVM.Protocol.ListBindingBudget

  The errors of the list-binding compilation at leanVM, one challenge at a time: every challenge
  below `2^-128` but WHIR's query positions, which are below `2^-111`, and `2^-128` after the
  grinding that precedes them.
-/

module

public import LeanerVM.Protocol.ListBindingDeployed
public import LeanerVM.Protocol.Whir.DeployedBudget

/-!
# The compiled protocol's errors challenge by challenge, at leanVM

Category A, on `listBindingError` and the instance and chains of
`LeanerVM.Protocol.ListBindingDeployed`. The result contributes to T4 in the random-oracle model:
the Fiat–Shamir compilation charges each challenge its round's error, at most `2^-128` per
challenge, except the query positions of each WHIR level, which a proof of work precedes.

* `listBindingMark`: the compiled schedule's query positions, WHIR's (`openMark`).
* The front phases, challenge by challenge (`busError_le`, `tableError_le`, `flockError_le_overE`):
  every error is at most `max (4 · 2^μ_bus) (B + 3) 2^31 J` over `|E|`, and the front pays it
  `L₀` times, the level-0 list bound.
* `listBindingError_le_budget`: for any instance and chain whose numbers fit
  (`Whir.Ladder.fits`, and `L₀` times the front's largest numerator at most `2^64`), every
  challenge's error is within the budget its mark selects (`Whir.budget`).
* At leanISA, for admissible sizes: `μ_bus ≤ 55`, `B + 3 ≤ 2^57` and `J ≤ 2^57`
  (`leanIsa_μBus_le`, `leanIsa_B_le`, `leanIsa_poolSize_le`); with `L₀ ≤ 128` from the window
  (`Whir.deployedChain_fits`), `listBindingError_deployed_le` holds with no hypothesis beyond the
  announcement's admissibility: `listBindingError_deployed_le_of_not_mark` (every challenge but
  the query positions, `2^-128`) and `listBindingError_deployed_le_of_mark` (the query
  positions, `2^-111`, so `2^-128` after 17 bits of grinding).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Whir LeanIsa OracleComp OracleSpec ProtocolSpec
  StepSchedule
open scoped NNReal

@[expose] public section

/-! ## The marks of the compiled schedule -/

/-- The query positions of the compiled schedule: WHIR's, one per level; the front has none. -/
def listBindingMark (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) :
    (listBindingSpec I sh κ L).ChallengeIdx → Bool :=
  markAppend (fun _ ↦ false) (openMark L)

/-! ## The front, challenge by challenge -/

section Front

variable (I : M3Instance)

/-- Every challenge of the bus phase has error at most `4 · 2^μ_bus / |E|`. -/
theorem busError_le : ∀ i, busError I i ≤ overE (4 * 2 ^ I.μBus) := by
  have hg : ((max (3 - 1) 4 : ℕ) : ℝ≥0) * overE 1 ≤ overE (4 * 2 ^ I.μBus) := by
    rw [nat_mul_overE]
    exact overE_mono (by have := Nat.one_le_two_pow (n := I.μBus); omega)
  exact errAppend_le_const (errAppend_le_const (errAppend_le_const (fun _ ↦ le_rfl)
    (sayError_le _ _)) fun i ↦ (gkrError_le E _ 3 _ i).trans hg) (sayError_le _ _)

/-- Every challenge of the table sumcheck has error at most `(B + 3) / |E|`. -/
theorem tableError_le : ∀ i, tableError I i ≤ overE (I.B + 3) :=
  errAppend_le_const (errAppend_le_const (fun _ ↦ overE_mono (by omega))
    fun i ↦ (roundsError_le E 3 _ _ i).trans (overE_mono (by omega))) (sayError_le _ _)

/-- The ring switching's challenges have error at most `2^31 / |E|`. -/
private theorem ringError_le : ∀ i, ringError i ≤ overE (2 ^ 31) :=
  errAppend_le_const (errAppend_le_const (errAppend_le_const (errAppend_le_const
    (errAppend_le_const (errAppend_le_const (fun i ↦ Fin.elim0 i.1)
    fun _ ↦ le_rfl) fun _ ↦ overE_mono (by norm_num)) fun _ ↦ overE_mono (by norm_num))
    fun _ ↦ overE_mono (by norm_num)) fun _ ↦ overE_mono (by norm_num))
    fun _ ↦ overE_mono (by norm_num)

/-- Every challenge of a Flock slot has error at most `2^31 / |E|`. -/
private theorem flockErrorOpt_le :
    (o : Option (FlockRegion I.toShape)) → ∀ i, flockErrorOpt I o i ≤ overE (2 ^ 31)
  | none => fun i ↦ Fin.elim0 i.1
  | some r => by
    have h : ∀ c, c ≤ 2 ^ 31 → overE c ≤ overE (2 ^ 31) := fun _ h ↦ overE_mono h
    exact errAppend_le_const (errAppend_le_const (errAppend_le_const (errAppend_le_const
      (errAppend_le_const (errAppend_le_const (errAppend_le_const (errAppend_le_const
      (errAppend_le_const (fun i ↦ (drawsError_le E _ _ i).trans (h 1 (by norm_num)))
      (sayError_le _ _)) fun _ ↦ h 127 (by norm_num))
      fun i ↦ (roundsError_le E 2 _ 8 i).trans (h 2 (by norm_num)))
      fun i ↦ (roundsError_le E 2 _ _ i).trans (h 3 (by norm_num))) (sayError_le _ _))
      fun _ ↦ h 3 (by norm_num)) fun i ↦ (roundsError_le E 2 _ 8 i).trans (h 2 (by norm_num)))
      (sayError_le _ _)) ringError_le

/-- Every challenge of the Flock phase has error at most `2^31 / |E|`. -/
theorem flockError_le_overE : ∀ i, flockError I i ≤ overE (2 ^ 31) := flockErrorOpt_le I I.flock

/-- `L₀` times `x / |E|` is at most `2^-128` when `L₀ x ≤ 2^64`. -/
theorem nsmul_overE_le {L₀ x : ℕ} (h : L₀ * x ≤ 2 ^ 64) : L₀ • overE x ≤ (2 ^ 128)⁻¹ := by
  rw [nsmul_eq_mul, nat_mul_overE, ← natCast_div_card_eq_overE]
  exact natCast_div_card_le h

/-- The largest numerator of a front challenge's error: the fingerprint's `4 · 2^μ_bus`, the
table batching's `B + 3`, the ring switching's `2^31` and the opening batching's `J`. -/
def frontNumerator : ℕ := max (4 * 2 ^ I.μBus) (max (I.B + 3) (max (2 ^ 31) I.poolSize))

/-- **The compiled protocol, challenge by challenge.** On a chain that fits the budgets
(`Whir.Ladder.fits`), with `L₀` times the front's largest numerator at most `2^64`, every
challenge's error is within the budget its mark selects: `2^-128`, or `2^-111` for WHIR's query
positions. -/
theorem listBindingError_le_budget {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (ps : L.Pars)
    (hfit : L.fits ps = true) (hfront : (L.headPar ps).L * frontNumerator I ≤ 2 ^ 64) :
    ∀ i, listBindingError I L ps i ≤ budget (listBindingMark I L i) := by
  have hle : ∀ {c : ℕ}, c ≤ frontNumerator I → ∀ {e : ℝ≥0}, e ≤ overE c →
      (L.headPar ps).L • e ≤ budget false := fun hc _ he ↦
    (nsmul_le_nsmul_right (he.trans (overE_mono hc)) _).trans (nsmul_overE_le hfront)
  have h1 : 4 * 2 ^ I.μBus ≤ frontNumerator I := le_max_left _ _
  have h2 : I.B + 3 ≤ frontNumerator I := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 2 ^ 31 ≤ frontNumerator I :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h4 : I.poolSize - 1 ≤ frontNumerator I :=
    (Nat.sub_le _ _).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have h5 : 1 ≤ frontNumerator I := (Nat.one_le_two_pow).trans h3
  unfold listBindingError listBindingMark
  refine errAppend_le_mark _ ?_ (openErr_le_budget L ps hfit)
  exact errAppend_le_const (errAppend_le_const (errAppend_le_const (errAppend_le_const
    (errAppend_le_const (errAppend_le_const (fun _ ↦ zero_le)
    fun i ↦ hle h1 (busError_le I i)) fun i ↦ hle h2 (tableError_le I i))
    fun _ ↦ hle h5 le_rfl) fun i ↦ hle h3 (flockError_le_overE I i)) fun _ ↦ hle h4 le_rfl)
    fun i ↦ Fin.elim0 i.1

end Front

/-! ## The leanISA instance's sizes -/

section LeanIsa

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- Erasing duplicates does not lengthen a list. -/
private theorem length_eraseDups_le {α : Type} [BEq α] :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length
  | _, [], _ => le_rfl
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    have hf := List.length_filter_le (fun b ↦ !b == a) as
    exact Nat.succ_le_succ ((length_eraseDups_le n _ (by simp at h; omega)).trans hf)

/-- A sum over the sumcheck tables is at most the sum over every table. -/
private theorem sum_sumcheckTables_le (I : M3Instance) (f : Fin I.ntab → ℕ) :
    ∑ j : I.SumcheckTables, f j.1 ≤ ∑ j, f j := by
  calc ∑ j : I.SumcheckTables, f j.1 =
        ∑ j ∈ Finset.univ.map (Function.Embedding.subtype I.SumcheckTable), f j :=
        (Finset.sum_map Finset.univ (Function.Embedding.subtype I.SumcheckTable) f).symm
    _ ≤ ∑ j, f j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The bus phase pools at most `32` claims per boundary block: sixteen coordinates on each
side. -/
private theorem busClaims_le (I : M3Instance) : I.busClaims ≤ 2 * (I.boundary.length * 16) := by
  refine (length_eraseDups_le _ _ le_rfl).trans ?_
  have hside : ∀ sd : Side, ((I.boundary.filter fun b ↦ decide (b.side = sd)).flatMap
      fun b ↦ b.coords.toList.filterMap Coord.committed?).length ≤ I.boundary.length * 16 := by
    intro sd
    rw [List.length_flatMap]
    refine (List.sum_le_length_nsmul _ 16 ?_).trans ?_
    · simp only [List.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact (List.length_filterMap_le _ _).trans (by simp)
    · rw [List.length_map, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (List.length_filter_le _ _)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  have := hside .push
  have := hside .pull
  omega

/-- The opcode tables' constraints, flushes and widths, counted. -/
private theorem leanIsa_counts :
    ∑ j : Fin 9, (LeanIsa.constraints j).length ≤ 2 ^ 56 ∧ ∑ j : Fin 9, LeanIsa.width j ≤ 2 ^ 40 ∧
      ((List.finRange 9).map fun j ↦
        ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length * 2 ^ 40).sum ≤
        2 ^ 54 := by
  decide +kernel

/-- **The table batching's degree at leanISA**: `B + 3 ≤ 2^57`. -/
theorem leanIsa_B_le : (leanIsaInstance F prog s).B + 3 ≤ 2 ^ 57 := by
  have h := sum_sumcheckTables_le (leanIsaInstance F prog s) fun j ↦
    ((leanIsaInstance F prog s).constraints j).length
  have hc : ∑ j, ((leanIsaInstance F prog s).constraints j).length =
      ∑ j : Fin 9, (LeanIsa.constraints j).length := rfl
  have := leanIsa_counts.1
  unfold M3Instance.B
  omega

/-- **The opening's pooled claims at leanISA**: `J ≤ 2^57`. -/
theorem leanIsa_poolSize_le : (leanIsaInstance F prog s).poolSize ≤ 2 ^ 57 := by
  have hb := busClaims_le (leanIsaInstance F prog s)
  have hlen : (leanIsaInstance F prog s).boundary.length = 6 := rfl
  have ht := sum_sumcheckTables_le (leanIsaInstance F prog s) fun j ↦
    (leanIsaInstance F prog s).width j
  have hw : ∑ j, (leanIsaInstance F prog s).width j = ∑ j : Fin 9, LeanIsa.width j := rfl
  have := leanIsa_counts.2.1
  have hf : (leanIsaInstance F prog s).flockClaims ≤ 1 := by
    unfold M3Instance.flockClaims
    split <;> omega
  unfold M3Instance.poolSize M3Instance.pubClaims M3Instance.tableClaims M3Instance.tableColumns
  rw [hlen] at hb
  change _ + _ + 3 + _ ≤ _
  omega

variable {prog s} in
/-- At admissible sizes every table and boundary block of leanISA has at most `2^40` rows. -/
private theorem leanIsa_height_le (hs : s.Admissible prog) (j : Fin 9) : height prog s j ≤ 40 := by
  obtain ⟨-, hm, hτ, -, -⟩ := hs
  have hp := prog.logSize_le
  have hτ' : ∀ k, s.τ k ≤ 32 := hτ
  simp only [maxLogMem, maxLogBytecode] at hm hp
  match j with
  | ⟨0, _⟩ => exact hm.trans (by norm_num)
  | ⟨1, _⟩ => exact hp.trans (by norm_num)
  | ⟨2, _⟩ => show 8 + s.τ 5 ≤ 40; have := hτ' 5; omega
  | ⟨j + 3, h⟩ => exact (hτ' ⟨j, by omega⟩).trans (by norm_num)

variable {prog s} in
/-- **The bus's leaf stacks at leanISA**: `μ_bus ≤ 55` at admissible sizes. -/
theorem leanIsa_μBus_le (hs : s.Admissible prog) : (leanIsaInstance F prog s).μBus ≤ 55 := by
  unfold M3Instance.μBus
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  unfold M3Instance.pushLeaves
  have hb : (((leanIsaInstance F prog s).boundary.filter fun b ↦ decide (b.side = .push)).map
      fun b ↦ 2 ^ b.κ).sum ≤ 6 * 2 ^ 40 := by
    refine (List.sum_le_length_nsmul _ (2 ^ 40) ?_).trans ?_
    · simp only [List.mem_map, List.mem_filter]
      rintro _ ⟨b, ⟨hb, -⟩, rfl⟩
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have hm := hs.2.1
      have hp := prog.logSize_le
      simp only [maxLogMem, maxLogBytecode] at hm hp
      simp only [LeanIsa.boundary, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
    · rw [List.length_map, smul_eq_mul]
      exact Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (by rfl))
  have hf : ((List.finRange (leanIsaInstance F prog s).ntab).map fun j ↦
      (((leanIsaInstance F prog s).flushes j).filter fun f ↦ decide (f.1 = .push)).length *
        2 ^ (leanIsaInstance F prog s).τ j).sum ≤ 2 ^ 54 := by
    refine le_trans (List.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by norm_num) (leanIsa_height_le hs j))) leanIsa_counts.2.2
  omega

end LeanIsa

/-! ## At leanVM -/

section Deployed

variable (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- **Every challenge of the compiled protocol at leanVM within its budget**, at every admissible
announcement and rate: `2^-128`, or `2^-111` for WHIR's query positions. -/
theorem listBindingError_deployed_le :
    ∀ i, listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
        (leanIsaChain prog s hs ρ hρ).pars i ≤
      budget (listBindingMark (leanIsaInstance F prog s)
        (leanIsaChain prog s hs ρ hρ).ladder i) := by
  have hc := deployedChain_fits (admissible_of_sizes hs hρ)
  refine listBindingError_le_budget _ _ _ hc.1 ?_
  have hn : frontNumerator (leanIsaInstance F prog s) ≤ 2 ^ 57 := by
    have hμ := leanIsa_μBus_le F hs
    have h4 : 4 * 2 ^ (leanIsaInstance F prog s).μBus ≤ 2 ^ 57 :=
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hμ)).trans (by norm_num)
    exact max_le h4 (max_le (leanIsa_B_le F prog s) (max_le (by norm_num)
      (leanIsa_poolSize_le F prog s)))
  exact (Nat.mul_le_mul hc.2 hn).trans (by norm_num)

/-- Every challenge but WHIR's query positions has error at most `2^-128`. -/
theorem listBindingError_deployed_le_of_not_mark
    (i : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).ChallengeIdx)
    (hi : listBindingMark _ (leanIsaChain prog s hs ρ hρ).ladder i = false) :
    listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
      (leanIsaChain prog s hs ρ hρ).pars i ≤ (2 ^ 128)⁻¹ := by
  have := listBindingError_deployed_le F prog s hs ρ hρ i
  rwa [hi] at this

/-- WHIR's query positions have error at most `2^-111`, and at most `2^-128` after the 17 bits
of grinding that precede them. -/
theorem listBindingError_deployed_le_of_mark
    (i : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).ChallengeIdx)
    (hi : listBindingMark _ (leanIsaChain prog s hs ρ hρ).ladder i = true) :
    listBindingError (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).ladder
        (leanIsaChain prog s hs ρ hρ).pars i ≤ (2 ^ 111)⁻¹ ∧
      (2 ^ Parameters.Whir.queryGrindingBits)⁻¹ * listBindingError (leanIsaInstance F prog s)
        (leanIsaChain prog s hs ρ hρ).ladder (leanIsaChain prog s hs ρ hρ).pars i ≤
        (2 ^ 128)⁻¹ := by
  have h := listBindingError_deployed_le F prog s hs ρ hρ i
  rw [hi] at h
  refine ⟨h, (mul_le_mul_of_nonneg_left h zero_le).trans (le_of_eq ?_)⟩
  show (2 ^ 17 : ℝ≥0)⁻¹ * (2 ^ 111)⁻¹ = (2 ^ 128)⁻¹
  rw [← mul_inv, ← pow_add]

end Deployed

end

end LeanerVM.Protocol
