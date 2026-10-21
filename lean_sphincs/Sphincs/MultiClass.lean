import Sphincs.MultiPay

/-! **Hash calls of one key.** An input of the key with public parameter `p` starts with the 16
bytes of `p` (`OfKey`); every input the potentials of one sample look at is one. An ordinary query
of another key is free for the linear potential: it touches nothing the potential sees, so its unit
of budget is refunded in full. With the refund of the unused budget, the linear potential pays
`ρ / 2^128` per hash call of the key only (`interp_potential_refund_class`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security

/-- An input of the key with public parameter `p`: its first 16 bytes are `p`. -/
def OfKey (p : PublicParameter) (x : HashInput) : Prop := x.take 16 = bytesLE 16 p

theorem ofKey_append (p : PublicParameter) (rest : HashInput) : OfKey p (bytesLE 16 p ++ rest) :=
  List.take_left' (bytesLE_length 16 p)

theorem ofKey_tweakable (p : PublicParameter) (d : HashDomain) (m : HashInput) :
    OfKey p (tweakableHashInput p d m) := by
  unfold tweakableHashInput
  rw [List.append_assoc]
  exact ofKey_append p _

end Sphincs.Security

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- The cost of an entry unless it is an ordinary query of the free class. -/
noncomputable def chargedEntry (Free : D → Prop) : Entry D → ℕ
  | .inl input => if Free input then 0 else 1
  | .inr amount => amount

/-- The cost of a trace, the ordinary queries of the free class not counted. -/
noncomputable def chargedCost (Free : D → Prop) (entries : List (Entry D)) : ℕ := (entries.map (chargedEntry Free)).sum

theorem chargedCost_append (Free : D → Prop) (first second : List (Entry D)) :
    chargedCost Free (first ++ second) = chargedCost Free first + chargedCost Free second := by
  simp [chargedCost]

theorem chargedEntry_le (Free : D → Prop) (entry : Entry D) : chargedEntry Free entry ≤ entryCost entry := by
  cases entry with
  | inl input => simp only [chargedEntry, entryCost]; split_ifs <;> omega
  | inr amount => rfl

theorem chargedCost_le (Free : D → Prop) (entries : List (Entry D)) :
    chargedCost Free entries ≤ traceCost entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [chargedCost, traceCost, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (chargedEntry_le Free entry) ih

/-- The charged cost of one step's record: its cost, unless it is an ordinary query of the free
class. -/
theorem chargedCost_recorded (Free : D → Prop) (input : (SourceCostSpec D R ι).Domain) :
    chargedCost Free (recorded input) =
      if ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ Free bytes then 0 else sourceCost input := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · simp [chargedCost, recorded, sourceCost]
  · by_cases h : Free bytes
    · simp [chargedCost, recorded, chargedEntry, h]
    · simp [chargedCost, recorded, chargedEntry, h, sourceCost]
  · simp [chargedCost, recorded, sourceCost]
  · simp [chargedCost, recorded, chargedEntry, sourceCost]

/-- **Linear potential with a refund of the unused budget, the free class refunded in full.** If an
ordinary query of the free class gives its whole unit of budget back to the potential, the start
potential bounds the final value, the payments and `refund` per unit of budget that was not spent on
charged entries. -/
theorem interp_potential_refund_class {α : Type} (IsFleaf : D → Prop) (Free : D → Prop)
    (Inv : DebtState D R ι → Prop)
    (Φ : ℕ → DebtState D R ι → ℝ≥0∞) (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞)
    (pay pay2 refund : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state + refund * budget ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι).Domain), (¬∃ bytes, input = .inl (.inr (.inl bytes)) ∧ Free bytes) →
      ∀ budget state, Inv state → sourceCost input ≤ budget →
      ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input) ≤ Φ budget state)
    (hfree : ∀ (bytes : D) budget state, Inv state → Free bytes → 1 ≤ budget →
      ∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result] *
          Φ (budget - 1) result.2 + refund ≤ Φ budget state)
    (hfreeDigest : ∀ bytes, Free bytes → ¬tg.digest bytes) (hfreeFleaf : ∀ bytes, Free bytes → ¬IsFleaf bytes)
    (hinv : ∀ input state, Inv state → ∀ result ∈ support (costStep model input state), Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget state, Inv state →
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1 +
          refund * ((budget - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞)) ≤
        Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
      simpa [digestCount, fleafCount, chargedCost] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul]
        by_cases hF : ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ Free bytes
        · obtain ⟨bytes, rfl, hb⟩ := hF
          have hc1 : sourceCost (D := D) (R := R) (ι := ι) (.inl (.inr (.inl bytes))) = 1 := rfl
          rw [hc1] at hcost ⊢
          have hd : digestCount tg (recorded (D := D) (R := R) (ι := ι) (.inl (.inr (.inl bytes)))) = 0 := by
            change digestCount tg [.inl bytes] = 0
            simp [digestCount, hfreeDigest bytes hb]
          have hl : fleafCount IsFleaf (recorded (D := D) (R := R) (ι := ι) (.inl (.inr (.inl bytes)))) = 0 :=
            fleafCount_recorded_eq_zero IsFleaf _ fun b h hb' => by
              cases h
              exact hfreeFleaf bytes hb hb'
          have hcc : chargedCost Free (recorded (D := D) (R := R) (ι := ι) (.inl (.inr (.inl bytes)))) = 0 := by
            rw [chargedCost_recorded]
            exact ite_eq_left_of_eq_true _ _ (eq_true ⟨bytes, rfl, hb⟩)
          calc ∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result] *
                ∑' out, Pr{let x ← ((fun out => ((out.1.1, revealed (.inl (.inr (.inl bytes))) ++ out.1.2.1,
                    recorded (.inl (.inr (.inl bytes))) ++ out.1.2.2.1,
                    touch tg initial state (.inl (.inr (.inl bytes))) ++ out.1.2.2.2), out.2)) <$>
                  interp tg initial model (next result.1) (budget - 1) result.2)}[x = out] *
                  (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                    pay2 * fleafCount IsFleaf out.1.2.2.1 +
                    refund * ((budget - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞))
              ≤ ∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result] *
                  (Φ (budget - 1) result.2 + refund) := by
                refine ENNReal.tsum_le_tsum fun result => ?_
                by_cases hr : result ∈ support (costStep model (.inl (.inr (.inl bytes))) state)
                · refine mul_le_mul_right ?_ _
                  rw [OracleComp.tsum_prEvent_map_mul]
                  simp only [digestCount_append, fleafCount_append, chargedCost_append, hd, hl, hcc, zero_add]
                  have hle : ∀ out ∈ support (interp tg initial model (next result.1) (budget - 1) result.2),
                      ((budget - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞) =
                        ((budget - 1 - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞) + 1 := by
                    intro out hout
                    have h1 := (chargedCost_le Free out.1.2.2.1).trans
                      (interp_traceCost_le tg initial model (next result.1) (budget - 1) result.2 out hout)
                    have he : budget - chargedCost Free out.1.2.2.1 = budget - 1 - chargedCost Free out.1.2.2.1 + 1 := by
                      omega
                    rw [he, Nat.cast_add, Nat.cast_one]
                  calc ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - 1)
                          result.2)}[x = out] *
                        (endValue payoff out.2 + pay * (digestCount tg out.1.2.2.1 : ℝ≥0∞) +
                          pay2 * (fleafCount IsFleaf out.1.2.2.1 : ℝ≥0∞) +
                          refund * ((budget - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞))
                      = ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - 1)
                            result.2)}[x = out] *
                          (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                            pay2 * fleafCount IsFleaf out.1.2.2.1 +
                            refund * ((budget - 1 - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞)) +
                        (∑' out, Pr{let x ← (interp tg initial model (next result.1)
                          (budget - 1) result.2)}[x = out]) * refund := by
                        rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                        refine tsum_congr fun out => ?_
                        by_cases hout : out ∈ support (interp tg initial model (next result.1) (budget - 1) result.2)
                        · rw [hle out hout]
                          ring
                        · rw [(prEvent_eq_zero_of_not_mem_support _) hout]
                          simp
                    _ ≤ Φ (budget - 1) result.2 + 1 * refund :=
                        add_le_add (ih result.1 _ _ (hinv _ state hstate result hr))
                          (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
                    _ = _ := by rw [one_mul]
                · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
            _ = ∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result] *
                  Φ (budget - 1) result.2 +
                  (∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result]) * refund := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                refine tsum_congr fun result => ?_
                ring
            _ ≤ ∑' result, Pr{let x ← costStep model (.inl (.inr (.inl bytes))) state}[x = result] *
                  Φ (budget - 1) result.2 + 1 * refund :=
                add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
            _ ≤ _ := by
                rw [one_mul]
                exact hfree bytes budget state hstate hb hcost
        · set c : ℝ≥0∞ := pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input)
            with hc
          have hcc : chargedCost Free (recorded input) = sourceCost input := by
            rw [chargedCost_recorded]
            exact ite_eq_right_of_eq_false _ _ (eq_false hF)
          calc ∑' result, Pr{let x ← costStep model input state}[x = result] *
                ∑' out, Pr{let x ← ((fun out => ((out.1.1, revealed input ++ out.1.2.1,
                    recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
                  interp tg initial model (next result.1) (budget - sourceCost input) result.2)}[x = out] *
                  (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                    pay2 * fleafCount IsFleaf out.1.2.2.1 +
                    refund * ((budget - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞))
              ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] *
                  (Φ (budget - sourceCost input) result.2 + c) := by
                refine ENNReal.tsum_le_tsum fun result => ?_
                by_cases hr : result ∈ support (costStep model input state)
                · refine mul_le_mul_right ?_ _
                  rw [OracleComp.tsum_prEvent_map_mul]
                  simp only [digestCount_append, fleafCount_append, chargedCost_append, hcc, Nat.cast_add]
                  calc ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                          result.2)}[x = out] *
                        (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                          digestCount tg out.1.2.2.1) + pay2 * ((fleafCount IsFleaf (recorded input) : ℝ≥0∞) +
                          fleafCount IsFleaf out.1.2.2.1) +
                          refund * ((budget - (sourceCost input + chargedCost Free out.1.2.2.1) : ℕ) : ℝ≥0∞))
                      = ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                            result.2)}[x = out] *
                          (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                            pay2 * fleafCount IsFleaf out.1.2.2.1 +
                            refund * ((budget - sourceCost input - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞)) +
                        (∑' out, Pr{let x ← (interp tg initial model (next result.1)
                          (budget - sourceCost input) result.2)}[x = out]) * c := by
                        rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                        refine tsum_congr fun out => ?_
                        rw [hc, Nat.sub_add_eq]
                        ring
                    _ ≤ Φ (budget - sourceCost input) result.2 + 1 * c :=
                        add_le_add (ih result.1 _ _ (hinv input state hstate result hr))
                          (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
                    _ = _ := by rw [one_mul]
                · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
            _ = ∑' result, Pr{let x ← costStep model input state}[x = result] *
                  Φ (budget - sourceCost input) result.2 +
                  (∑' result, Pr{let x ← costStep model input state}[x = result]) * c := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                refine tsum_congr fun result => ?_
                ring
            _ ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] *
                  Φ (budget - sourceCost input) result.2 + 1 * c :=
                add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
            _ ≤ _ := by
                rw [one_mul, hc, ← add_assoc]
                exact hstep input hF budget state hstate hcost
      · rw [OracleComp.tsum_prEvent_pure_mul]
        simpa [digestCount, fleafCount, chargedCost] using hfinal budget state hstate

end Sphincs.Security.HiddenDebt

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable [Params]

namespace Ctx

variable (K : Ctx)

omit [Params] in
theorem ofKey_of_isA {l : Index} {i : ChainIndex} {x : HashInput} (h : K.IsA l i x) : OfKey K.p x := by
  obtain ⟨st, payload, -, rfl⟩ := h
  exact ofKey_tweakable _ _ _

omit [Params] in
theorem ofKey_of_isB {l : Index} {i : ChainIndex} {v : Digest} {x : HashInput} (h : K.IsB l i v x) :
    OfKey K.p x := by
  obtain ⟨st, -, rfl⟩ := h
  exact ofKey_tweakable _ _ _

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- **An ordinary query of another key is free**: it gives its whole unit of budget back. -/
theorem stepFree {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hparse : ∀ x, ¬OfKey K.p x → M.parse x = none) (hkind : ∀ x, ¬OfKey K.p x → K.tg.kind x = .none)
    (bytes : HashInput) (hx : ¬OfKey K.p bytes) (budget : ℕ) (s : St) (hinv : K.Inv s) (hcost : 1 ≤ budget) :
    ∑' r, Pr{let x ← costStep M (.inl (.inr (.inl bytes))) s}[x = r] * K.potCap total (budget - 1) r.2 +
      ENNReal.ofReal (K.ρ / 2 ^ 128) ≤ K.potCap total budget s := by
  unfold potCap
  by_cases hb : budget ≤ total
  swap
  · rw [ite_eq_right hb]
    exact le_top
  rw [ite_eq_left hb]
  have hpot : ∀ r : HashOutput × St,
      (if budget - 1 ≤ total then K.pot (budget - 1) r.2 else ⊤) = K.pot (budget - 1) r.2 :=
    fun r => ite_eq_left ((Nat.sub_le _ _).trans hb)
  simp only [hpot]
  obtain ⟨y', rfl⟩ : ∃ y', budget = y' + 1 := ⟨budget - 1, by omega⟩
  rw [Nat.add_sub_cancel, payment_eq, costStep_inl, lazyStep_unparsed M bytes s (hparse bytes hx)]
  cases hc : s.cache bytes with
  | some u =>
      rw [readOutside_cached bytes s u hc, OracleComp.tsum_prEvent_pure_mul, K.pot_succ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (K.rate_ge_rho hN s) bot_le)
  | none =>
      refine K.fresh_other hN (y' := y') hinv hc
        (fun l _ => ⟨fun i h => hx (K.ofKey_of_isA h), fun i v h => hx (K.ofKey_of_isB h)⟩)
        (fun l msg ctr _ h => hx (h ▸ ofKey_tweakable _ _ _)) (fun f h => hx (h ▸ ofKey_tweakable _ _ _)) ?_
      rw [K.kindUnit_none (hkind bytes hx), add_zero]

end Model

end Ctx

end Sphincs.Security.PotentialA

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The message-digest inputs of the key with parameter `p`. -/
def MsgOfKey (p : PublicParameter) (x : HashInput) : Prop := ForestSigner.IsMsgInput x ∧ OfKey p x

omit [Params] in
theorem msgOfKey_digestInput (p : PublicParameter) (root : Digest) (m : Message) (r : Randomness) :
    MsgOfKey p (Security.digestInput p root m r) :=
  ⟨GraphView.msgInput_digestInput p root m r, ofKey_tweakable _ _ _⟩

theorem sampleModel_parse_free (parameterOutput : HashOutput) (highs : CoordinateHighs) (x : HashInput)
    (hx : ¬OfKey (truncateHash parameterOutput) x) : (sampleModel parameterOutput highs).parse x = none := by
  rw [sampleModel_parse]
  cases h : HiddenGraph.parse (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput)) x with
  | none => rfl
  | some q =>
      exfalso
      obtain ⟨hq, -⟩ := (parse_some_iff _ _ _ q).1 h
      exact hx (hq ▸ ofKey_tweakable _ _ _)

theorem targetingA_kind_free (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (x : HashInput)
    (hx : ¬OfKey (truncateHash parameterOutput) x) :
    (targetingA parameterOutput fixed highs remaining results).kind x = .none := by
  show (if SecondOrderInput (truncateHash parameterOutput) results x then .none
    else sampleKind parameterOutput fixed highs remaining results x) = .none
  split_ifs
  · rfl
  · unfold sampleKind
    cases h : TargetAssignment.parseFields (truncateHash parameterOutput) x with
    | none => rfl
    | some fields =>
        exfalso
        obtain ⟨payload, hp⟩ := (TargetAssignment.parseFields_some_iff _ _ _).1 h
        rw [hp, List.append_assoc] at hx
        exact hx (ofKey_append _ _)

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- **The linear potential of the small route, paid per hash call of the key**: `ρ / 2^128` per unit
of budget the run spends on the key's inputs and ticks; the inputs of other keys are free. -/
theorem smallRoute_potential_payClass
    (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (tg : Targeting HashInput HashOutput Coordinate) (hdigest : tg.digest = MsgOfKey (truncateHash parameterOutput))
    (total : ℕ) (hN : Numeric ρ ((total : ℝ) / 2 ^ 128))
    {α : Type} (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∑' out, Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs) comp total
        (DebtState.start prepared.2 known))}[x = out] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        ENNReal.ofReal (ρ / 2 ^ 128) * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1) ≤
      ENNReal.ofReal (ρ / 2 ^ 128) * ∑' out, Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs)
        comp total (DebtState.start prepared.2 known))}[x = out] *
        (chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) out.1.2.2.1 : ℝ≥0∞) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set run := interp tg prepared.2 (sampleModel parameterOutput highs) comp total (DebtState.start prepared.2 known)
    with hrun
  set a : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with ha
  have hMp : (sampleModel parameterOutput highs).parse = HiddenGraph.parse K.p (candidateActive K.p) :=
    sampleModel_parse parameterOutput highs
  have hMi := sampleModel_incoming parameterOutput highs
  have hMo := sampleModel_outgoing parameterOutput highs
  have hρ2 : K.ρ ≤ 2 := hN.high
  set Free : HashInput → Prop := fun x => ¬OfKey (truncateHash parameterOutput) x with hFree
  set tgM : Targeting HashInput HashOutput Coordinate := { tg with digest := ForestSigner.IsMsgInput } with htgM
  have hdc : ∀ input : (SourceCostSpec HashInput HashOutput Coordinate).Domain,
      (¬∃ bytes, input = .inl (.inr (.inl bytes)) ∧ Free bytes) →
        digestCount tg (recorded input) = digestCount tgM (recorded input) := by
    intro input hnf
    rcases input with (draw | (bytes | coordinate)) | amount
    · rfl
    · have hk : OfKey (truncateHash parameterOutput) bytes := by
        by_contra hb
        exact hnf ⟨bytes, rfl, hb⟩
      have h1 := Ctx.digestCount_bytes tg bytes
      have h2 := Ctx.digestCount_bytes tgM bytes
      have he : tg.digest bytes ↔ tgM.digest bytes := by
        rw [hdigest]
        exact ⟨fun h => h.1, fun h => ⟨h, hk⟩⟩
      have h3 : (if tg.digest bytes then (1 : ℝ≥0∞) else 0) = if tgM.digest bytes then 1 else 0 :=
        if_congr he rfl rfl
      exact_mod_cast h1.trans (h3.trans h2.symm)
    · rfl
    · rfl
  have h := interp_potential_refund_class tg prepared.2 (sampleModel parameterOutput highs) (IsFchainIn K.p) Free K.Inv
    (K.potCap total) K.payoff (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128)) (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (fun budget state _ => by
      unfold Ctx.potCap
      split_ifs
      · exact K.endValue_add_le hρ2 budget state
      · exact le_top)
    (fun input hnf budget state hinv hcost => by
      rw [hdc input hnf]
      exact K.stepF (sampleModel parameterOutput highs) hMp hMi hMo tgM rfl hN
        (ctxA_sec parameterOutput fixed highs remaining prepared known ρ)
        (ctxA_msg parameterOutput fixed highs remaining prepared known ρ) input budget state hinv hcost)
    (fun bytes budget state hinv hb hcost => K.stepFree (sampleModel parameterOutput highs) hN
      (fun x hx => sampleModel_parse_free parameterOutput highs x hx)
      (fun x hx => targetingA_kind_free parameterOutput fixed highs remaining prepared.1 x hx)
      bytes hb budget state hinv hcost)
    (fun bytes hb hd => by
      rw [hdigest] at hd
      exact hb hd.2)
    (fun bytes hb hf => by
      obtain ⟨f, rfl⟩ := hf
      exact hb (ofKey_tweakable _ _ _))
    (fun input state hinv => K.inv_step (sampleModel parameterOutput highs) hMp hMi input state hinv)
    comp total (DebtState.start prepared.2 known)
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown)
  have hp : K.pot total (DebtState.start prepared.2 known) = ENNReal.ofReal (ρ * total / 2 ^ 128) :=
    pot_start K known (show (0 : ℝ) ≤ ρ by linarith [hN.low]) total
  have hstart : K.potCap total total (DebtState.start prepared.2 known) = a * total := by
    unfold Ctx.potCap
    rw [ite_eq_left le_rfl, hp, ha, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by linarith [hN.low])]
    congr 1
    ring
  rw [hstart] at h
  have hle : ∀ out ∈ support run, chargedCost Free out.1.2.2.1 ≤ total := fun out hout =>
    (chargedCost_le Free _).trans
      (interp_traceCost_le tg prepared.2 (sampleModel parameterOutput highs) comp total _ out hout)
  have hsplit : ∑' out, Pr{let x ← run}[x = out] * ((total - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞) +
      ∑' out, Pr{let x ← run}[x = out] * (chargedCost Free out.1.2.2.1 : ℝ≥0∞) = total := by
    rw [← ENNReal.tsum_add]
    calc ∑' out, (Pr{let x ← run}[x = out] * ((total - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞) +
          Pr{let x ← run}[x = out] * (chargedCost Free out.1.2.2.1 : ℝ≥0∞))
        = ∑' out, Pr{let x ← run}[x = out] * (total : ℝ≥0∞) := by
          refine tsum_congr fun out => ?_
          rw [← mul_add]
          by_cases hout : out ∈ support run
          · rw [← Nat.cast_add, Nat.sub_add_cancel (hle out hout)]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
      _ = total := by rw [ENNReal.tsum_mul_right, HiddenDebt.interp_mass, one_mul]
  have hfin : a * ∑' out, Pr{let x ← run}[x = out] * ((total - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.natCast_ne_top total) ?_)
    rw [← hsplit]
    exact le_self_add
  have h' : ∑' out, Pr{let x ← run}[x = out] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        a * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1 +
        a * ((total - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞)) ≤ a * total := h
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc _ = ∑' out, Pr{let x ← run}[x = out] *
        (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
          a * digestCount tg out.1.2.2.1 +
          ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
            fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1 +
          a * ((total - chargedCost Free out.1.2.2.1 : ℕ) : ℝ≥0∞)) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun out => ?_
        ring
    _ ≤ a * total := h'
    _ = _ := by
        rw [← hsplit, mul_add]
        ring

end Sample

end Sphincs.Security.PotentialA

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

open Completeness SeedModel _root_.Sphincs.Security.Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route, the linear potential paid per hash call of the key**:
the baseline `ρ / 2^128` is paid by every unit of budget the run spends on the key's own inputs and
ticks; the hash calls of other keys are free. The cover, coin, near and cap terms are those of
`sample_boundF`. -/
theorem sample_boundF_class (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℝ) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ κ) (hκ1 : κ ≤ 1)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      ENNReal.ofReal (ρ / 2 ^ 128) *
          ∑' out, Pr{let x ← (interp { targetingA parameterOutput fixed highs remaining prepared.1 with digest := MsgOfKey (truncateHash parameterOutput) } prepared.2
            (sampleModel parameterOutput highs) (costGameX (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining) (internalize adversary)) q
            (DebtState.start prepared.2 known))}[x = out] *
            (chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) out.1.2.2.1 : ℝ≥0∞) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
        (ENNReal.ofReal κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * ENNReal.ofReal (((2 ^ b * on.En : ℚ) / 2 : ℚ) : ℝ))) +
          (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * failMass (failSet prepared.1) + signatureLimit * failMass (failSet prepared.1))) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := { targetingA parameterOutput fixed highs remaining prepared.1 with digest := MsgOfKey (truncateHash parameterOutput) } with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay'
  set q' := q - keygenCost with hq'
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((ρ - 1 - ((q' : ℕ) : ℝ) / 2 ^ 128) / 2 ^ 128) with hc0
  set IsF := IsFchainIn param with hIsF
  have hrunK : ∀ hK : keygenCost ≤ q, run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1,
      out.1.2.2.2), out.2)) <$> interp tgA prepared.2 model
        (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := fun hK => by
    rw [hrun]
    unfold costGameX
    rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
  have hrunA : ¬keygenCost ≤ q → run = pure ((none, [], [], []), start) := fun hK => by
    rw [hrun]
    unfold costGameX
    exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
  have hA3 : ∑' out, Pr{let x ← run}[x = out] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) +
      c0 * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)) ≤
      b0 * ∑' out, Pr{let x ← run}[x = out] *
        (chargedCost (fun x => ¬OfKey (truncateHash parameterOutput) x) out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      refine le_trans (le_of_eq ?_) ((smallRoute_potential_payClass parameterOutput fixed highs remaining
        prepared known ρ hk tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) [])).trans
        (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl ?_)))
      · refine tsum_congr fun out => ?_
        simp only [digestCount_cons_inrF, fleafCount_cons_inr]
        rfl
      · simp only [chargedCost, chargedEntry, List.map_cons, List.sum_cons, Nat.cast_add]
        exact le_add_self
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrunA hK]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potential_payClass parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_monoF hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary))
  exact sample_boundF_of hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared known hk ρ κ
    hκ hκ1 b N hbb hNN (MsgOfKey (truncateHash parameterOutput)) (fun m r => msgOfKey_digestInput _ _ m r) t o on hpt qtop
    hrt hqtop ho hon hcthr _ hA3

end Sphincs.Security.ForsPotential
