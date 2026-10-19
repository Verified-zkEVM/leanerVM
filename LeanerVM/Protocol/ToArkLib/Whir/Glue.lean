/-
  LeanerVM.Protocol.ToArkLib.Whir.Glue

  The claims WHIR glues into the running sumcheck at a level boundary, their weights, and the
  fact that the round polynomial of the glued claim is the glued round polynomials. Candidate for
  ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.WhirSumcheck
public import LeanerVM.Protocol.ToArkLib.WeightBatch
public import LeanerVM.Protocol.ToArkLib.Whir.Word

/-!
# Gluing claims into the running sumcheck

At a level boundary the verifier of WHIR adds two claims to the residual claim `(W', c')`: the
out-of-domain claim `(eq(z, ·), c_ood)` and the batch of the consistency claims of the queried
positions `(Σ_q λ^q W_{y_q}, Σ_q λ^q c_q)`. The three are summed with the scalars `1, λ, λ²`
(`Weight.batch` of the three at `λ`, the batching of Annex B step 1 with the residual first, the
out-of-domain claim next and the queries after: `λ^0, λ^1, λ^(2+q)`). The prover sends each
claim's own first-round polynomial and the verifier sums them with the same scalars; the sum is the
honest round polynomial of the summed claim because the round polynomial is linear in the
weight (`roundPoly_batch`), and the summed claim's value is the sum of the three values
(`claim_batch`), each the weighted claim it is (`claim_zero`).

* `queryWeight`: the weight of the query batch, the column weights of the sampled positions
  combined by the powers of `λ`;
* `gluedWeight`: the three weights combined at `λ`;
* `batchMessage`: round polynomials combined by the powers of `λ`;
* `roundPoly_batch`, `claim_batch`: linearity in the weight;
* `claim_zero`: the sumcheck's claim at stage `0` is the weighted claim.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-! ## Linearity of the sumcheck in the weight -/

/-- Round polynomials combined by the powers of `ρ`, coefficient by coefficient. -/
def batchMessage {J : ℕ} (ms : Fin J → SumcheckRound.Message E 2) (ρ : E) :
    SumcheckRound.Message E 2 :=
  Vector.ofFn fun k ↦ powerBatch (fun i ↦ (ms i)[k]) ρ

/-- The extension of a batched weight table at the free point is the batch of the extensions. -/
theorem atFree_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E) {j : ℕ}
    (hj : j < n) (c : Vector E j) (x' : Fin (2 ^ (n - (j + 1)))) (z : E) :
    WhirSum.atFree (batchWeight Ts ρ) hj c x' z =
      powerBatch (fun i ↦ WhirSum.atFree (Ts i) hj c x' z) ρ := by
  unfold WhirSum.atFree
  rw [evalMle_batchWeight]

/-- A sum of batched terms against a fixed factor is the batch of the sums. -/
theorem sum_powerBatch_mul {J : ℕ} {α : Type} (s : Finset α) (a : α → Fin J → E)
    (g : α → E) (ρ : E) :
    ∑ x ∈ s, powerBatch (a x) ρ * g x =
      powerBatch (fun i ↦ ∑ x ∈ s, a x i * g x) ρ := by
  simp only [powerBatch, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- Batching commutes with differences. -/
theorem powerBatch_sub {J : ℕ} (a b : Fin J → E) (ρ : E) :
    powerBatch a ρ - powerBatch b ρ = powerBatch (fun i ↦ a i - b i) ρ := by
  simp only [powerBatch, ← Finset.sum_sub_distrib, sub_mul]

/-- Batching commutes with sums. -/
theorem powerBatch_add {J : ℕ} (a b : Fin J → E) (ρ : E) :
    powerBatch a ρ + powerBatch b ρ = powerBatch (fun i ↦ a i + b i) ρ := by
  simp only [powerBatch, ← Finset.sum_add_distrib, add_mul]

/-- The constant coefficient is linear in the weight. -/
theorem coef0_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E)
    (B : CMlPolynomialEval E n) {j : ℕ} (hj : j < n) (c : Vector E j) :
    WhirSum.coef0 (batchWeight Ts ρ) B hj c =
      powerBatch (fun i ↦ WhirSum.coef0 (Ts i) B hj c) ρ := by
  unfold WhirSum.coef0
  simp only [atFree_batch]
  exact sum_powerBatch_mul _ (fun x' i ↦ WhirSum.atFree (Ts i) hj c x' 0)
    (fun x' ↦ WhirSum.atFree B hj c x' 0) ρ

/-- The quadratic coefficient is linear in the weight. -/
theorem coef2_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E)
    (B : CMlPolynomialEval E n) {j : ℕ} (hj : j < n) (c : Vector E j) :
    WhirSum.coef2 (batchWeight Ts ρ) B hj c =
      powerBatch (fun i ↦ WhirSum.coef2 (Ts i) B hj c) ρ := by
  unfold WhirSum.coef2
  simp only [atFree_batch, powerBatch_sub]
  exact sum_powerBatch_mul _
    (fun x' i ↦ WhirSum.atFree (Ts i) hj c x' 1 - WhirSum.atFree (Ts i) hj c x' 0)
    (fun x' ↦ WhirSum.atFree B hj c x' 1 - WhirSum.atFree B hj c x' 0) ρ

/-- The linear coefficient is linear in the weight. -/
theorem coef1_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E)
    (B : CMlPolynomialEval E n) {j : ℕ} (hj : j < n) (c : Vector E j) :
    WhirSum.coef1 (batchWeight Ts ρ) B hj c =
      powerBatch (fun i ↦ WhirSum.coef1 (Ts i) B hj c) ρ := by
  unfold WhirSum.coef1
  simp only [atFree_batch, powerBatch_sub]
  rw [Finset.sum_add_distrib,
    sum_powerBatch_mul _ (fun x' i ↦ WhirSum.atFree (Ts i) hj c x' 0)
      (fun x' ↦ WhirSum.atFree B hj c x' 1 - WhirSum.atFree B hj c x' 0) ρ,
    sum_powerBatch_mul _
      (fun x' i ↦ WhirSum.atFree (Ts i) hj c x' 1 - WhirSum.atFree (Ts i) hj c x' 0)
      (fun x' ↦ WhirSum.atFree B hj c x' 0) ρ, powerBatch_add]
  congr 1
  funext i
  rw [Finset.sum_add_distrib]

/-- The round polynomial is linear in the weight: the round polynomial of a batch of weights is
the batch of their round polynomials. -/
theorem roundPoly_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E)
    (B : CMlPolynomialEval E n) (j : ℕ) (c : Vector E j) :
    WhirSum.roundPoly (batchWeight Ts ρ) B j c =
      batchMessage (fun i ↦ WhirSum.roundPoly (Ts i) B j c) ρ := by
  apply Vector.ext
  intro k hk
  by_cases hj : j < n
  · have h : ∀ (T : CMlPolynomialEval E n), WhirSum.roundPoly T B j c =
        #v[WhirSum.coef0 T B hj c, WhirSum.coef1 T B hj c, WhirSum.coef2 T B hj c] := fun T ↦ by
      unfold WhirSum.roundPoly
      rw [dite_eq_left hj]
    rw [h, batchMessage, Vector.getElem_ofFn]
    simp only [h]
    interval_cases k
    · exact coef0_batch Ts ρ B hj c
    · exact coef1_batch Ts ρ B hj c
    · exact coef2_batch Ts ρ B hj c
  · have h : ∀ (T : CMlPolynomialEval E n), WhirSum.roundPoly T B j c = #v[0, 0, 0] :=
        fun T ↦ by
      unfold WhirSum.roundPoly
      rw [dite_eq_right hj]
    rw [h, batchMessage, Vector.getElem_ofFn]
    simp only [h]
    interval_cases k <;> simp [powerBatch]

/-- The claim is linear in the weight. -/
theorem claim_batch {n J : ℕ} (Ts : Fin J → CMlPolynomialEval E n) (ρ : E)
    (B : CMlPolynomialEval E n) (j : ℕ) (c : Vector E j) :
    WhirSum.claim (batchWeight Ts ρ) B j c =
      powerBatch (fun i ↦ WhirSum.claim (Ts i) B j c) ρ := by
  unfold WhirSum.claim plainSum
  by_cases hj : j ≤ n
  · simp only [hj, ↓reduceDIte]
    have h : ∀ x : Fin (2 ^ (n - j)),
        WhirSum.summand (batchWeight Ts ρ) B (fixLow hj c (boolVec x)) =
          powerBatch (fun i ↦ evalMle (Ts i) (fixLow hj c (boolVec x))) ρ *
            evalMle B (fixLow hj c (boolVec x)) := fun x ↦ by
      unfold WhirSum.summand
      rw [evalMle_batchWeight]
    simp only [h]
    rw [sum_powerBatch_mul]
    rfl
  · simp [hj, powerBatch]

/-- The sumcheck's claim at stage `0` is the weighted claim. -/
theorem claim_zero {n : ℕ} (W : Weight E n) (f : CMlPolynomialEval E n) :
    WhirSum.claim W.onCube f 0 #v[] = W.pair (RingHom.id E) f := by
  rw [WhirSum.claim, plainSum_zero]
  simp only [WhirSum.summand, evalMle_boolVec, Weight.pair, Fin.getElem_fin, RingHom.id_apply]

/-! ## The glued weights -/

/-- The weight of the consistency claims of the sampled positions, combined by the powers of
`λ`: the column weight of position `pos q` carries `λ^q`. -/
def queryWeight (κ R : ℕ) {t : ℕ} (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E) :
    Weight E κ :=
  Weight.batch (fun q ↦ columnWeight (algebraMap K E) κ R (pos q)) lam

/-- The equality kernel's claim on a table is the table's extension at its point. -/
theorem pair_eqWeight_id {κ : ℕ} (z : Vector E κ) (f : CMlPolynomialEval E κ) :
    (eqWeight z).pair (RingHom.id E) f = evalMle f z := by
  have hmap : CMlPolynomialEval.map (RingHom.id E) f = f := by
    apply Vector.ext
    intro i hi
    simp [CMlPolynomialEval.map]
  rw [Weight.pair_eqWeight]
  unfold CMlPolynomialEval.eval₂Mle
  rw [hmap]

/-- The query batch's claim on a table is the batch of the table's encodings at the positions. -/
theorem pair_queryWeight {κ R t : ℕ} (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E)
    (f : CMlPolynomialEval E κ) :
    (queryWeight κ R pos lam).pair (RingHom.id E) f =
      powerBatch (fun q ↦ encode (algebraMap K E) κ R f (pos q)) lam := by
  unfold queryWeight
  rw [Weight.pair_batch]
  rfl

/-- The weight of the running sumcheck after the boundary: the residual weight, the
out-of-domain weight and the query batch combined at `λ` with the scalars `1, λ, λ²`
(`λ^0, λ^1, λ^(2+q)` on the queries). -/
def gluedWeight {κ R t : ℕ} (W' : Weight E κ) (z : Vector E κ)
    (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E) : Weight E κ :=
  Weight.batch ![W', eqWeight z, queryWeight κ R pos lam] lam

/-- The glued weight's claim on a table is the glued claims: the residual claim, the
out-of-domain claim and the query batch combined at `λ`. -/
theorem pair_gluedWeight {κ R t : ℕ} (W' : Weight E κ) (z : Vector E κ)
    (pos : Fin t → Fin (2 ^ (κ + R))) (lam : E) (f : CMlPolynomialEval E κ) :
    (gluedWeight W' z pos lam).pair (RingHom.id E) f =
      powerBatch ![W'.pair (RingHom.id E) f, evalMle f z,
        powerBatch (fun q ↦ encode (algebraMap K E) κ R f (pos q)) lam] lam := by
  unfold gluedWeight
  rw [Weight.pair_batch]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact pair_eqWeight_id z f
  · exact pair_queryWeight pos lam f


/-- The residual weight: the weight with its lane coordinates bound at the fold point `r`;
its extension at `z` is the weight's at `r ++ z`. -/
def foldWeight {ℓ κ : ℕ} (W : Weight E (ℓ + κ)) (r : Vector E ℓ) : Weight E κ where
  onCube := foldTable W.onCube r
  mle := fun z ↦ W.mle (r ++ z)
  mle_eq := fun z ↦ by rw [W.mle_eq, evalMle_foldTable]

/-- The sumcheck's running claim after the `ℓ` lane rounds is the residual weight's claim on the
folded table. -/
theorem claim_fold {ℓ κ : ℕ} (W : Weight E (ℓ + κ)) (f : CMlPolynomialEval E (ℓ + κ))
    (r : Vector E ℓ) :
    WhirSum.claim W.onCube f ℓ r = (foldWeight W r).pair (RingHom.id E) (foldTable f r) := by
  unfold WhirSum.claim plainSum
  rw [dite_eq_left (Nat.le_add_right ℓ κ)]
  let e : Fin (2 ^ κ) ≃ Fin (2 ^ (ℓ + κ - ℓ)) := finCongr (by rw [Nat.add_sub_cancel_left])
  rw [Weight.pair]
  refine (Fintype.sum_equiv e _ _ fun y ↦ ?_).symm
  have hv : fixLow (Nat.le_add_right ℓ κ) r (boolVec (e y) : Vector E _) =
      r ++ (boolVec y : Vector E κ) := by
    apply Vector.ext
    intro i hi
    simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, boolVec, Vector.getElem_ofFn, e,
      finCongr_apply, Fin.val_cast]
  rw [hv]
  have h1 := evalMle_boolVec (foldTable W.onCube r) y
  have h2 := evalMle_boolVec (foldTable f r) y
  have h3 : (foldTable W.onCube r)[y] * (foldTable f r)[y] =
      evalMle W.onCube (r ++ (boolVec y : Vector E κ)) *
        evalMle f (r ++ (boolVec y : Vector E κ)) := by
    rw [← h1, ← h2, evalMle_foldTable, evalMle_foldTable]
  simp only [WhirSum.summand, RingHom.id_apply]
  exact h3

end Whir

end

end LeanerVM.Protocol
