/-
  LeanerVM.Protocol.ToArkLib.GrandProductCached

  The grand-product argument with a cached honest prover: every tree's levels built once from the
  leaves and carried through the layers, and in each layer's sumcheck the children of the level
  below bound to the challenges one at a time. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.GrandProduct
public import LeanerVM.Protocol.ToArkLib.CachedRounds
public import LeanerVM.Protocol.ToCompPoly.ProductLevels
public import LeanerVM.Protocol.ToCompPoly.BindStep
import CompPoly.Univariate.ToPoly.RingHom

/-!
# The grand product with a cached prover

`Gkr.roundPoly` and `Gkr.children` read the trees' level below the layer, `layerTable` of the
leaves, which they rebuild from the leaves at every round, and the leaves from the public data and
the oracles. The cached prover builds every tree's levels once (`treesOf`, by `levelsOf`) and
carries them, beside the trivial witness, through every component of the argument
(`cachedGkr`). In the sumcheck of a layer it also keeps the `2 ^ ρ` children of each tree's level
below, as tables of the layer's coordinates, with the low ones bound to the challenges so far
(`boundChildren`): the round polynomial is read off two entries per child and point
(`roundFromBound`, equal to `roundPoly` by `roundFromBound_eq`), each challenge is bound once,
one halving per child (`stepChildren`), and the descendants' values are the tables bound on
every coordinate (`childrenFromBound`). Round `j` of a layer from `m` costs `2 ^ (m - j)` per
child instead of `m`'s level rebuilt from the leaves. `cachedGkr` is a `Component.Cached` of
`gkr`: from the trees of its input, it runs as `gkr`'s honest prover.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace Gkr

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]
  {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)

/-! ## The trees -/

/-- Every tree's levels, built once from its leaves. -/
def treesOf (x : X) (o : ∀ i, O i) : Vector (Levels F μ) nside :=
  Vector.ofFn fun s ↦ levelsOf (leaves x o s)

omit [BEq F] [LawfulBEq F] [∀ i, OracleInterface (O i)] in
/-- A level read off the built trees is the tree's level. -/
theorem get_treesOf (x : X) (o : ∀ i, O i) (s : Fin nside) (k : ℕ) :
    (treesOf nside μ leaves x o)[s].get k = layerTable (leaves x o s) k := by
  simp only [treesOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, get_levelsOf]

/-- The trees at a layer statement. -/
abbrev treesAtLayer {k : ℕ} (p : (LayerStmt X F nside k × ∀ i, O i) × Unit) :
    Vector (Levels F μ) nside :=
  treesOf nside μ leaves p.1.1.1 p.1.2

/-- The trees at the roots. -/
abbrev treesAtRoots (p : ((X × (Fin nside → F)) × ∀ i, O i) × Unit) : Vector (Levels F μ) nside :=
  treesOf nside μ leaves p.1.1.1 p.1.2

/-! ## The children of the level below, bound -/

section Layer

variable (ρ m : ℕ)

/-- The trees at a statement of a layer's sumcheck. -/
abbrev treesAtStage {j : ℕ} (p : (SumcheckRound.Stmt (LayerX X F nside m) F j × ∀ i, O i) × Unit) :
    Vector (Levels F μ) nside :=
  treesOf nside μ leaves p.1.1.1.1.1 p.1.2

/-- The trees after the descendants' message. -/
abbrev treesAtInterp {i : ℕ} (p : (InterpStmt X F nside m ρ i × ∀ j, O j) × Unit) :
    Vector (Levels F μ) nside :=
  treesOf nside μ leaves p.1.1.1.1 p.1.2

omit [BEq F] [LawfulBEq F] in
/-- Child `c` of a level `ρ` below a layer on `m` variables, as a table of the layer's
coordinates. -/
def lowsOf (L : CMlPolynomialEval F (m + ρ)) (c : Fin (2 ^ ρ)) : CMlPolynomialEval F m :=
  sliceLow (Vector.cast (congrArg (2 ^ ·) (Nat.add_comm m ρ)) L) c

variable {μ} in
omit [BEq F] [LawfulBEq F] in
/-- Every child of every tree's level below the layer, its low `j` coordinates bound to the
challenges `cv`, lowest first: what the prover keeps from round to round. -/
def boundChildren (T : Vector (Levels F μ) nside) (j : ℕ) (cv : Vector F j) :
    Vector (Vector (CMlPolynomialEval F (m - j)) (2 ^ ρ)) nside :=
  if hj : j ≤ m then
    Vector.ofFn fun s ↦ Vector.ofFn fun c ↦ bindLows (k := m - j)
      (Vector.cast (congrArg (2 ^ ·) (by omega)) (lowsOf ρ m (T[s].get (m + ρ)) c)) cv
  else Vector.replicate nside (Vector.replicate _ (Vector.replicate _ 0))

omit [BEq F] [LawfulBEq F] in
/-- An even index of a table on `m - j` variables, `j < m`. -/
private theorem two_mul_lt {m j : ℕ} (hj : j < m) (x : Fin (2 ^ (m - (j + 1)))) :
    2 * x.val < 2 ^ (m - j) := by
  have h := two_mul_add_one_lt x.isLt
  rw [show m - (j + 1) + 1 = m - j by omega] at h
  omega

omit [BEq F] [LawfulBEq F] in
/-- An odd index of a table on `m - j` variables, `j < m`. -/
private theorem two_mul_add_one_lt' {m j : ℕ} (hj : j < m) (x : Fin (2 ^ (m - (j + 1)))) :
    2 * x.val + 1 < 2 ^ (m - j) := by
  have h := two_mul_add_one_lt x.isLt
  rwa [show m - (j + 1) + 1 = m - j by omega] at h

variable {nside ρ m} in
/-- The honest round polynomial of round `j`, read off the bound children: per point `x'` of the
coordinates not yet bound and per child, the descendant's values at the round's variable `0` and
`1` are two adjacent entries of the bound child. -/
def roundFromBound (ctx : LayerCtx X F O nside m) (j : ℕ)
    (B : Vector (Vector (CMlPolynomialEval F (m - j)) (2 ^ ρ)) nside) :
    SumcheckRound.Message F (2 ^ ρ) :=
  if h : j < m then
    let lam := combinerOf ctx
    let w := lagrangeBasis ((pointOf ctx).drop (j + 1))
    let pows : Vector F nside := Vector.ofFn fun s ↦ lam ^ s.val
    let inner (x' : Fin (2 ^ (m - (j + 1)))) : SumcheckRound.Message F (2 ^ ρ) :=
      Fin.foldl nside (fun acc s ↦ axpy acc pows[s] (affineProd (2 ^ ρ) fun c ↦
        (B[s][c][2 * x'.val]'(by exact two_mul_lt h x'),
          B[s][c][2 * x'.val + 1]'(by exact two_mul_add_one_lt' h x'))))
        (Vector.replicate _ 0)
    Fin.foldl (2 ^ (m - (j + 1))) (fun acc x' ↦ axpy acc w[x'] (inner x')) (Vector.replicate _ 0)
  else SumcheckRound.ofCPolynomial _ 0

omit [BEq F] [LawfulBEq F] [∀ i, OracleInterface (O i)] in
/-- An entry of a bound child is the bound table's of the next coordinate, whatever the number of
free coordinates is called. -/
private theorem boundChildren_getElem (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (s : Fin nside) (c : Fin (2 ^ ρ)) (i : ℕ) (hi : i < 2 ^ (m - j)) :
    (boundChildren nside ρ m (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx)) j cv)[s][c][i] =
      (bindLowsNext hj (lowsOf ρ m (below nside μ leaves ρ m ctx s) c) cv)[i]'(by
        rwa [show m - (j + 1) + 1 = m - j by omega]) := by
  rw [boundChildren, dite_eq_left hj.le]
  simp only [treesOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, get_levelsOf]
  rw [bindLowsNext, getElem_bindLows_cast (show m - j = m - (j + 1) + 1 by omega) (by omega)
    (by omega)]
  rfl

omit [BEq F] [LawfulBEq F] [∀ i, OracleInterface (O i)] in
/-- A descendant's value at a Boolean value of the round's variable is the entry of the bound
child at that value and the point. -/
private theorem descendant_eq_bound (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (x' : Fin (2 ^ (m - (j + 1)))) (s : Fin nside) (c : Fin (2 ^ ρ)) :
    descendant nside μ leaves ρ m ctx hj cv x' s c 0 =
        (boundChildren nside ρ m (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx)) j cv)[s][c][
          2 * x'.val]'(two_mul_lt hj x') ∧
      descendant nside μ leaves ρ m ctx hj cv x' s c 1 =
        (boundChildren nside ρ m (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx)) j cv)[s][c][
          2 * x'.val + 1]'(two_mul_add_one_lt' hj x') := by
  have hcast : ∀ {a b : ℕ} (h : a = b) (t : CMlPolynomialEval F a) (P : Vector F b),
      evalMle t (Vector.cast h.symm P) = evalMle (Vector.cast (congrArg (2 ^ ·) h) t) P := by
    intro a b h t P
    subst h
    rfl
  have key : ∀ z : F, descendant nside μ leaves ρ m ctx hj cv x' s c z =
      evalMle (lowsOf ρ m (below nside μ leaves ρ m ctx s) c) (fixLow hj (cv.push z) (boolVec x')) := by
    intro z
    unfold descendant childPoint lowsOf
    rw [hcast (Nat.add_comm m ρ), evalMle_boolVec_append]
  rw [boundChildren_getElem nside μ leaves ρ m ctx hj cv s c,
    boundChildren_getElem nside μ leaves ρ m ctx hj cv s c, key, key, evalMle_fixLow_push_zero,
    evalMle_fixLow_push_one]
  exact ⟨rfl, rfl⟩

omit [∀ i, OracleInterface (O i)] in
/-- The round polynomial read off the bound children is the honest one. -/
theorem roundFromBound_eq (ctx : LayerCtx X F O nside m) {j : ℕ} (h : j < m) (cv : Vector F j) :
    roundFromBound ctx j
        (boundChildren nside ρ m (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx)) j cv) =
      roundPoly nside μ leaves ρ m ctx j cv := by
  unfold roundFromBound
  rw [dite_eq_left h, roundPoly, dite_eq_left h]
  apply Vector.ext
  intro i hi
  rw [show (SumcheckRound.ofCPolynomial (2 ^ ρ) (roundPolyRaw nside μ leaves ρ m ctx h cv))[i] =
    (roundPolyRaw nside μ leaves ρ m ctx h cv).coeff i from Vector.getElem_ofFn ..,
    CPolynomial.coeff_toPoly, roundPolyRaw, ← CPolynomial.toPolyRingHom_apply]
  dsimp only
  rw [foldl_axpy_getElem]
  simp only [map_sum, map_mul, map_prod, map_add, CPolynomial.toPolyRingHom_apply,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Vector.getElem_replicate, zero_add, Fin.getElem_fin]
  refine Finset.sum_congr rfl fun x' _ ↦ ?_
  rw [foldl_axpy_getElem]
  simp only [Vector.getElem_replicate, zero_add, Vector.getElem_ofFn]
  refine congrArg _ (Finset.sum_congr rfl fun t _ ↦ ?_)
  rw [affineProd_getElem]
  congr 3
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  obtain ⟨e0, e1⟩ := descendant_eq_bound nside μ leaves ρ m ctx h cv x' t c
  rw [e0, e1]
  rfl

omit [BEq F] [LawfulBEq F] in
/-- The bound children after one more challenge `a`: each bound at its new lowest coordinate. -/
def stepChildren {j : ℕ} (B : Vector (Vector (CMlPolynomialEval F (m - j)) (2 ^ ρ)) nside)
    (a : F) : Vector (Vector (CMlPolynomialEval F (m - (j + 1))) (2 ^ ρ)) nside :=
  if hj : j < m then
    B.map fun row ↦ row.map fun t ↦
      bindLow (Vector.cast (congrArg (2 ^ ·) (show m - j = m - (j + 1) + 1 by omega)) t) a
  else Vector.replicate nside (Vector.replicate _ (Vector.replicate _ 0))

variable {μ} in
omit [BEq F] [LawfulBEq F] in
/-- Binding the next challenge updates the bound children. -/
theorem stepChildren_boundChildren (T : Vector (Levels F μ) nside) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (a : F) :
    stepChildren nside ρ m (boundChildren nside ρ m T j cv) a =
      boundChildren nside ρ m T (j + 1) (cv.push a) := by
  rw [stepChildren, dite_eq_left hj, boundChildren, dite_eq_left hj.le, boundChildren,
    dite_eq_left (Nat.succ_le_of_lt hj)]
  refine Vector.ext fun s hs ↦ Vector.ext fun c hc ↦ ?_
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  rw [bindLows_cast (show m - j = m - (j + 1) + 1 by omega), Vector.cast_cast, bindLow_bindLows,
    Vector.cast_cast]

omit [BEq F] [LawfulBEq F] in
/-- The descendants' values, read off the children bound on every coordinate. -/
def childrenFromBound (B : Vector (Vector (CMlPolynomialEval F (m - m)) (2 ^ ρ)) nside) :
    Fin nside → CMlPolynomialEval F ρ :=
  let vals : Vector (CMlPolynomialEval F ρ) nside :=
    B.map fun row ↦ row.map fun t ↦ t[0]'(Nat.two_pow_pos _)
  fun s ↦ vals[s]

omit [BEq F] [LawfulBEq F] [∀ i, OracleInterface (O i)] in
/-- The children bound on every coordinate hold the honest descendants' values. -/
theorem childrenFromBound_eq (x : X) (o : ∀ i, O i) (cv : Vector F m) :
    childrenFromBound nside ρ m (boundChildren nside ρ m (treesOf nside μ leaves x o) m cv) =
      children nside μ leaves ρ m x o cv := by
  funext s
  rw [children_eq_childrenFast]
  refine Vector.ext fun c hc ↦ ?_
  simp only [childrenFromBound, childrenFast]
  rw [boundChildren, dite_eq_left le_rfl]
  simp only [Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  rw [bindLows_getElem_zero (Nat.sub_self m), evalMle_cast]
  simp only [lowsOf, treesOf, Vector.getElem_ofFn, get_levelsOf]

/-- The round cache of a layer's sumcheck: the trees, and the children of each tree's level below
bound to the challenges so far. -/
def roundCache : SumcheckRound.RoundCache (roundPoly nside μ leaves ρ m) m where
  C j := Vector (Levels F μ) nside × Vector (Vector (CMlPolynomialEval F (m - j)) (2 ^ ρ)) nside
  cache j ctx cv := (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx),
    boundChildren nside ρ m (treesOf nside μ leaves (dataOf ctx) (oraclesOf ctx)) j cv)
  msg j ctx _ TB := roundFromBound ctx j TB.2
  step _ _ _ TB a := (TB.1, stepChildren nside ρ m TB.2 a)
  msg_eq j ctx cv hj := roundFromBound_eq nside μ leaves ρ m ctx hj cv
  step_eq _ _ cv a hj := by
    simp only [stepChildren_boundChildren nside ρ m _ hj cv a]

variable [DecidableEq F] [SampleableType F]

/-! ## The cached step -/

variable {S : Type} (inp : S → LayerStmt X F nside m)

/-- The cached combiner: the trees kept. -/
def cachedLambda : Component.Cached (lambdaStep nside m inp)
    (fun p ↦ treesOf nside μ leaves (inp p.1.1).1 p.1.2) (treesAtStage nside μ leaves m (j := 0)) :=
  Component.Cached.sample (upd := fun _ T _ ↦ T) fun _ _ ↦ rfl

/-- The cached sumcheck of a layer: the children of the level below read off the trees once, then
bound one challenge at a time. -/
def cachedLayerRounds :
    Component.Cached (SumcheckRound.rounds (roundPoly nside μ leaves ρ m) (weights nside m) m m 0
      (Nat.zero_add m)) (treesAtStage nside μ leaves m (j := 0))
      ((roundCache nside μ leaves ρ m).at (j := m)) :=
  (SumcheckRound.cachedRounds (roundCache nside μ leaves ρ m) (weights nside m) m 0
    (Nat.zero_add m)).adaptIn (fun p T ↦ (T, boundChildren nside ρ m T 0 p.1.1.2.1)) fun _ ↦ rfl

/-- The cached descendants' message: the values read off the children bound on every
coordinate; the trees kept. -/
def cachedChildren : Component.Cached (sendChildren nside μ leaves ρ m)
    ((roundCache nside μ leaves ρ m).at (j := m)) (treesAtInterp nside μ leaves ρ m (i := 0)) :=
  Component.Cached.sendChecked (msg := fun _ TB ↦ childrenFromBound nside ρ m TB.2)
    (upd := fun _ TB _ ↦ TB.1) (fun _ ↦ childrenFromBound_eq nside μ leaves ρ m _ _ _) fun _ ↦ rfl

/-- The cached first `i` combination challenges: the trees kept. -/
def cachedInterpPrefix : (i : ℕ) →
    Component.Cached (interpPrefix (F := F) (X := X) (O := O) nside ρ m i)
      (treesAtInterp nside μ leaves ρ m (i := 0)) (treesAtInterp nside μ leaves ρ m (i := i))
  | 0 => Component.Cached.passThrough (upd := fun _ T ↦ T) fun _ ↦ rfl
  | i + 1 => (cachedInterpPrefix i).append (Component.Cached.sample (upd := fun _ T _ ↦ T)
      fun _ _ ↦ rfl)

/-- The cached combination challenges: the trees kept. -/
def cachedInterpolate : Component.Cached (interpolate (F := F) (X := X) (O := O) nside ρ m)
    (treesAtInterp nside μ leaves ρ m (i := 0)) (treesAtLayer nside μ leaves (k := m + ρ)) :=
  match ρ with
  | 0 => Component.Cached.passThrough (upd := fun _ T ↦ T) fun _ ↦ rfl
  | ρ' + 1 => (cachedInterpPrefix nside μ leaves (ρ' + 1) m ρ').append
      (Component.Cached.sample (upd := fun _ T _ ↦ T) fun _ _ ↦ rfl)

/-- The cached step from layer `m`: the trees carried through its four parts. -/
def cachedLayerStep : Component.Cached (layerStep nside μ leaves ρ m inp)
    (fun p ↦ treesOf nside μ leaves (inp p.1.1).1 p.1.2)
    (treesAtLayer nside μ leaves (k := m + ρ)) :=
  (((cachedLambda nside μ leaves m inp).append (cachedLayerRounds nside μ leaves ρ m)).append
    (cachedChildren nside μ leaves ρ m)).append (cachedInterpolate nside μ leaves ρ m)

end Layer

variable [DecidableEq F] [SampleableType F]

/-! ## The whole argument -/

/-- The cached radix-four steps. -/
def cachedLayerSteps : (k m : ℕ) → (h : m + 2 * k = μ) →
    Component.Cached (layerSteps nside μ leaves k m h) (treesAtLayer nside μ leaves (k := m))
      (treesAtLayer nside μ leaves (k := μ))
  | 0, _, h => Component.Cached.passThrough (upd := fun _ T ↦ T) fun _ ↦ by
    simp only [treesAtLayer]
  | k + 1, m, h =>
    (cachedLayerStep nside μ leaves 2 m id).append (cachedLayerSteps k (m + 2) (by omega))

/-- The cached first step. -/
def cachedOdd : (r : ℕ) → (hr : r ≤ 1) →
    Component.Cached (odd nside μ leaves r hr) (treesAtRoots nside μ leaves)
      (treesAtLayer nside μ leaves (k := r))
  | 0, _ => Component.Cached.passThrough (upd := fun _ T ↦ T) fun _ ↦ rfl
  | 1, _ => cachedLayerStep nside μ leaves 1 0 (rootStmt nside)
  | _ + 2, h => absurd h (by omega)

/-- The cached last combiner: the trees dropped. -/
def cachedLastCombiner : Component.Cached (lastCombiner (F := F) (X := X) (O := O) nside μ)
    (treesAtLayer nside μ leaves (k := μ)) (fun _ ↦ ()) :=
  Component.Cached.sample (upd := fun _ _ _ ↦ ()) fun _ _ ↦ rfl

end Gkr

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] [SampleableType F]
  {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)

/-- **The cached prover of the grand-product argument**: from the trees of its leaves, it runs
as `gkr`'s honest prover, the trees built once and carried through every layer. -/
def cachedGkr : Component.Cached (gkr nside μ leaves) (Gkr.treesAtRoots nside μ leaves)
    (fun _ ↦ ()) :=
  ((Gkr.cachedOdd nside μ leaves (μ % 2) _).append
    (Gkr.cachedLayerSteps nside μ leaves (μ / 2) (μ % 2) (Nat.mod_add_div μ 2))).append
    (Gkr.cachedLastCombiner nside μ leaves)

end
end LeanerVM.Protocol
