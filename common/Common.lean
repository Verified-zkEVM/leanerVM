import Common.Model
import Common.Sponge
import Common.Indiff.Main
import Common.Transfer
import Common.Transfer2
import Common.Keccak
import Common.Signature
import Common.Lanes
import Common.Duplex.Vec
import Common.Linear

/-! The random-permutation model and the indifferentiability of the sponge (Keccak-256) from a
random oracle, with one oracle (`H`) or two (`H` and direct permutation calls `F`), the
transfer of SUF-CMA signature games, and the duplex lemma: challenges derived by a duplex over
the random function `F` are a random oracle of the absorbed roots, up to capacity collisions
(`Common.Duplex.duplex_le`). The build
fails if the axiom footprint of the main theorems ever grows beyond Lean's three standard
axioms. -/

/-- info: 'Common.indifferentiability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.indifferentiability

/-- info: 'Common.transfer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.transfer

/-- info: 'Common.pathsOf_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.pathsOf_sound

/-- info: 'Common.pathsOf_ideal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.pathsOf_ideal

/-- info: 'Common.keccak256_indifferentiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.keccak256_indifferentiable

/-- info: 'Common.keccak256_transfer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.keccak256_transfer

/-- info: 'Common.transfer2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.transfer2

/-- info: 'Common.pathsOf_ideal2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.pathsOf_ideal2

/-- info: 'Common.not_keccakNF_of_pad' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.not_keccakNF_of_pad

/-- info: 'Common.keccakNF_blockTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.keccakNF_blockTo

/-- info: 'Common.keccak256_transfer2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.keccak256_transfer2

/-- info: 'Common.SufCma.rpm_le_romB' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.SufCma.rpm_le_romB

/-- info: 'Common.runK_relabel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.runK_relabel

/-- info: 'Common.isWeightBound_relabel_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.isWeightBound_relabel_iff

/-- info: 'Common.SufCma.rpm_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.SufCma.rpm_bound

/-- info: 'Common.SufCma.rpm_bound_perm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.SufCma.rpm_bound_perm

/-- info: 'Common.Duplex.duplex_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.Duplex.duplex_le

/-- info: 'Common.Duplex.run'_romImpl_evalDistEq_vec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.Duplex.run'_romImpl_evalDistEq_vec

/-- info: 'Common.run'_romImpl_evalDistEq_eager' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.run'_romImpl_evalDistEq_eager

/-- info: 'Common.run'_romImpl_evalDistEq_swap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.run'_romImpl_evalDistEq_swap

/-- info: 'Common.run_rerun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.run_rerun
