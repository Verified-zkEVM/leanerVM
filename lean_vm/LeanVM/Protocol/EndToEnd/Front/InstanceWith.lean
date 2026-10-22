/-
  LeanVM.Protocol.EndToEnd.Front.InstanceWith

  The leanISA instance with any Flock region: the deployed one at `BLAKE2s`'s region, the
  Flock-blind one with none. Everything the bus, the table sumcheck and the public input read of
  it is the deployed instance's.
-/

module

public import LeanVM.Protocol.LeanIsa

/-!
# The leanISA instance with any Flock region

`leanIsaWith F prog s fl` is `leanIsaInstance F prog s` with the Flock region `fl`: the deployed
instance at `fl = some (flockRegion prog s F)` (`leanIsaWith_some`, by `rfl`), and the instance the
Flock-blind verifier (`docs/roadmap/e2e-security.md` (removed; in git at `6ffa1d1f`) D3) proves knowledge for at `fl = none`, whose
relation has no Flock predicate (`M3Instance.aux` holds of every stack, `aux_none`).

The region is read only by the Flock predicate and the Flock phase: the bus, the table sumcheck and
the public input read the same fields at every `fl`. The statements about them that the front
phases prove at the deployed instance are stated at every `fl` (`TableFidLeanIsa`, `PubPhase`,
`BusTable`); here, the bus phase's side conditions (`leanIsaWith_conditions`), whose leaf counts
are the same at every region (`leafCount_leanIsaWith`).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **The leanISA instance with the Flock region `fl`**: `leanIsaInstance F prog s` but for its
region. -/
abbrev leanIsaWith (F : FlockSpec) (prog : Program) (s : Sizes)
    (fl : Option (FlockRegion (shape prog s))) : M3Instance where
  toShape := shape prog s
  Stmt := PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  rows := rows prog s
  rows_le := rows_le prog s
  padRow := padRow
  boundary := boundary prog s
  μ := leanIsaμ prog s
  layout := layout prog s F.slot
  nLines := 3
  publicLines := publicLines prog s
  flock := fl

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- At `BLAKE2s`'s region, the deployed instance. -/
theorem leanIsaWith_some :
    leanIsaWith F prog s (some (flockRegion prog s F)) = leanIsaInstance F prog s :=
  rfl

/-- Without a region, the Flock predicate holds of every stack. -/
theorem aux_none (q : Column (leanIsaμ prog s)) : (leanIsaWith F prog s none).aux q :=
  fun _ h ↦ nomatch h

/-- The boundary blocks' tuples do not read the region. -/
theorem boundaryTuples_with (I : M3Instance) (fl : Option (FlockRegion I.toShape))
    (q : Column I.μ) (side : Side) :
    ({ I with flock := fl } : M3Instance).boundaryTuples q side = I.boundaryTuples q side := by
  unfold M3Instance.boundaryTuples
  refine congrArg (List.flatMap · _) (funext fun b ↦ ?_)
  refine congrArg (List.map · _) (funext fun x ↦ ?_)
  refine congrArg (Vector.map · _) (funext fun co ↦ ?_)
  cases co <;> rfl

/-- **The bus does not read the region**: the stacks it balances are the same at every region. -/
theorem balanced_with (I : M3Instance) (fl : Option (FlockRegion I.toShape)) (q : Column I.μ) :
    ({ I with flock := fl } : M3Instance).Balanced q ↔ I.Balanced q := by
  have hf : ∀ side, ({ I with flock := fl } : M3Instance).flushTuples q side =
      I.flushTuples q side := fun _ ↦ rfl
  unfold M3Instance.Balanced M3Instance.tuples
  rw [hf, hf, boundaryTuples_with I fl q .push, boundaryTuples_with I fl q .pull]

/-- A side's leaf count, from its blocks' log-heights. -/
theorem leafCount_eq_κ (I : M3Instance) (k : Fin 3) :
    Bus.leafCount I k = (((Bus.sources I k).map Bus.Source.κ).map (2 ^ ·)).sum := by
  rw [Bus.leafCount, List.map_map]
  rfl

/-- **The leaf counts do not depend on the region.** -/
theorem leafCount_leanIsaWith (fl fl' : Option (FlockRegion (shape prog s))) (k : Fin 3) :
    Bus.leafCount (leanIsaWith F prog s fl) k = Bus.leafCount (leanIsaWith F prog s fl') k := by
  rw [leafCount_eq_κ, leafCount_eq_κ]
  fin_cases k
  · change (((Bus.sideSources _ .push).map Bus.Source.κ).map _).sum =
      (((Bus.sideSources _ .push).map Bus.Source.κ).map _).sum
    rw [Bus.sideSources_map_κ, Bus.sideSources_map_κ]
  · change (((Bus.sideSources _ .pull).map Bus.Source.κ).map _).sum =
      (((Bus.sideSources _ .pull).map Bus.Source.κ).map _).sum
    rw [Bus.sideSources_map_κ, Bus.sideSources_map_κ]
  · change (((Bus.countSources _).map Bus.Source.κ).map _).sum =
      (((Bus.countSources _).map Bus.Source.κ).map _).sum
    rw [Bus.countSources_map_κ, Bus.countSources_map_κ]

/-- **The bus phase's side conditions hold at every region**: they are the deployed instance's
(`leanIsa_conditions`). -/
theorem leanIsaWith_conditions (fl : Option (FlockRegion (shape prog s))) :
    Bus.Conditions (leanIsaWith F prog s fl) :=
  have h := leanIsa_conditions F prog s
  { one_le_d := h.one_le_d
    constrained := h.constrained
    pull_fits := by
      rw [leafCount_leanIsaWith F prog s fl (some (flockRegion prog s F))]
      exact h.pull_fits
    count_fits := by
      rw [leafCount_leanIsaWith F prog s fl (some (flockRegion prog s F))]
      exact h.count_fits
    separator := h.separator }

end
end LeanVM.Protocol
