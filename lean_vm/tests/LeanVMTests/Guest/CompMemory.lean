import LeanVM.Guest.Memory.StaticWordsB
import LeanVM.Guest.Memory.DischargeB
import LeanVM.Guest.Memory.SizeTransferB
import LeanVM.Guest.Memory.WeightRatioB
import LeanVM.Guest.Memory.StraightB

/-!
# Tests: the Memory layer under any `BLAKE2S` semantics (L2, Memory)

* The generic lemmas of `Guest/Memory/*B.lean` and `Guest/MemoryB.lean` (valid trees, placed
  relations, the honest memory, re-chosen temporaries, the discharge, the weight and words
  bounds) rest on Lean's three axioms.
* **At the deployed semantics they are the deployed ones**: `Tree.ValidB.rel`,
  `weightLeB_of_stat`, `totalLeB_of_stat` and `honestAtB_retemp` at `blakeDeployed`, through the
  `…B_deployed` lemmas, give `Tree.Valid.rel`, `weightLe_of_stat`, `totalLe_of_stat` and
  `honestAt_retemp`.
-/

namespace LeanVMTests.Guest.CompMemory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.Memory.Tree.ValidB.rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.Tree.ValidB.rel

/-- info: 'LeanVM.Guest.Memory.Tree.ValidB.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.Tree.ValidB.transfer

/-- info: 'LeanVM.Guest.Memory.Tree.ValidB.eqns_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.Tree.ValidB.eqns_read

/-- info: 'LeanVM.Guest.Memory.validB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.validB_deployed

/-- info: 'LeanVM.Guest.Memory.out_satB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.out_satB_deployed

/-- info: 'LeanVM.Guest.Memory.relB_iff_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relB_iff_tree

/-- info: 'LeanVM.Guest.Core.Program.RelB.tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Core.Program.RelB.tree

/-- info: 'LeanVM.Guest.Memory.relAtB_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtB_of_walk

/-- info: 'LeanVM.Guest.Memory.relAtB_of_rel_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtB_of_rel_pure

/-- info: 'LeanVM.Guest.Memory.kidsFromB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.kidsFromB_deployed

/-- info: 'LeanVM.Guest.Memory.HonestB.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.HonestB.consistent

/-- info: 'LeanVM.Guest.Memory.HonestB.valid_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.HonestB.valid_image

/-- info: 'LeanVM.Guest.Memory.HonestAtB.nodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.HonestAtB.nodeAt

/-- info: 'LeanVM.Guest.Memory.honestAtB_of_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.honestAtB_of_read

/-- info: 'LeanVM.Guest.Memory.honestAtB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.honestAtB_deployed

/-- info: 'LeanVM.Guest.Memory.relAtInB_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_of_walk

/-- info: 'LeanVM.Guest.Memory.relInB_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInB_of_walk

/-- info: 'LeanVM.Guest.Memory.relAtInB_of_rel_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_of_rel_quiet

/-- info: 'LeanVM.Guest.Memory.kidsFromInB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.kidsFromInB_deployed

/-- info: 'LeanVM.Guest.Memory.relInB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInB_deployed

/-- info: 'LeanVM.Guest.Memory.retempB_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.retempB_valid

/-- info: 'LeanVM.Guest.Memory.relAtInB_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_transfer

/-- info: 'LeanVM.Guest.Memory.relAtInB_uniform_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_uniform_pure

/-- info: 'LeanVM.Guest.Memory.relAtInB_uniform_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_uniform_quiet

/-- info: 'LeanVM.Guest.Memory.relInB_of_rel_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInB_of_rel_supp

/-- info: 'LeanVM.Guest.Memory.relAtInB_uniform_of_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_uniform_of_supp

/-- info: 'LeanVM.Guest.Memory.totalLeB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeB_deployed

/-- info: 'LeanVM.Guest.Memory.weightLeB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightLeB_deployed

/-- info: 'LeanVM.Guest.Memory.totalLeB_of_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeB_of_weightLe

/-- info: 'LeanVM.Guest.Memory.totalLeOnB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeOnB_deployed

/-- info: 'LeanVM.Guest.Memory.totalLeB_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeB_transfer

/-- info: 'LeanVM.Guest.Memory.weightLeB_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightLeB_transfer

/-- info: 'LeanVM.Guest.Memory.weightB_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightB_le_ratio

/-- info: 'LeanVM.Guest.Memory.holdsB_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.holdsB_atoms

/-- info: 'LeanVM.Guest.Memory.honestAtB_retemp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.honestAtB_retemp

/-- info: 'LeanVM.Guest.Memory.dischargeHypsB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.dischargeHypsB_deployed

/-- info: 'LeanVM.Guest.Memory.weightLeB_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightLeB_of_stat

/-- info: 'LeanVM.Guest.Memory.weightB_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.weightB_le_of_loop

/-- info: 'LeanVM.Guest.Memory.kBB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.kBB_deployed

/-- info: 'LeanVM.Guest.Memory.totalLeB_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalLeB_of_stat

/-- info: 'LeanVM.Guest.Memory.totalB_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.totalB_le_of_loop

/-- info: 'LeanVM.Guest.Memory.handOkB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.handOkB_deployed

/-! ## At the deployed semantics -/

/-- `Tree.ValidB.rel` at `blakeDeployed` is `Tree.Valid.rel`. -/
example {P : Core.Program} {rd : Reader} (t : Tree) {args rets : List E}
    (h : t.Valid P rd args rets) : P.Rel rd t.name args rets := by
  have := Tree.ValidB.rel (S := blakeDeployed) t (by rwa [validB_deployed])
  rwa [relB_deployed] at this

/-- `weightLeB_of_stat` at `blakeDeployed` is `weightLe_of_stat`. -/
example {P : Core.Program} {cert : String → Cert} {ω : String → ℕ} (hchk : Checked P false cert ω)
    {f : String} {B : ℕ} {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) :
    WeightLe P ω f fun _ => B := by
  rw [← weightLeB_deployed]; exact weightLeB_of_stat hchk hcf

/-- `totalLeB_of_stat` at `blakeDeployed` is `totalLe_of_stat`. -/
example {P : Core.Program} {fs : String → ℕ} {cert : String → Cert} {X : String → Prop}
    (hchk : CheckedExcept P true cert fs X) (hX : HandOk P fs cert X) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) : TotalLe P fs f fun _ => B := by
  rw [← totalLeB_deployed]; exact totalLeB_of_stat hchk (by rwa [handOkB_deployed]) hcf

/-- `honestAtB_retemp` at `blakeDeployed` is `honestAt_retemp`. -/
example {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {H : Inst → ℕ → E × E}
    {C : Inst → List (ℕ × E)} {hdr : E × E} {T : Tree} {R : ℕ → Prop}
    {M : MemImage (logMem (T.total fs))} {args rets : List E}
    (h : DischargeHyps P fs cert H C hdr T R M args rets) :
    ∃ ν, HonestAt P fs H C hdr (T.retemp P fs ν 0) cert
      (honest P fs H C hdr (T.retemp P fs ν 0)).read args rets := by
  obtain ⟨ν, hν⟩ := honestAtB_retemp (S := blakeDeployed) (by rwa [dischargeHypsB_deployed])
  exact ⟨ν, by rwa [honestAtB_deployed] at hν⟩

end LeanVMTests.Guest.CompMemory
