import LeanRpm.Model
import LeanRpm.Sponge
import LeanRpm.Indiff.Main
import LeanRpm.Transfer
import LeanRpm.Transfer2
import LeanRpm.Keccak
import LeanRpm.Signature

/-! The random-permutation model and the indifferentiability of the sponge (Keccak-256) from a
random oracle, with one oracle (`H`) or two (`H` and direct permutation calls `F`), and the
transfer of SUF-CMA signature games. The build
fails if the axiom footprint of the main theorems ever grows beyond Lean's three standard
axioms. -/

/-- info: 'LeanRpm.indifferentiability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.indifferentiability

/-- info: 'LeanRpm.transfer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.transfer

/-- info: 'LeanRpm.pathsOf_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.pathsOf_sound

/-- info: 'LeanRpm.pathsOf_ideal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.pathsOf_ideal

/-- info: 'LeanRpm.keccak256_indifferentiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.keccak256_indifferentiable

/-- info: 'LeanRpm.keccak256_transfer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.keccak256_transfer

/-- info: 'LeanRpm.transfer2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.transfer2

/-- info: 'LeanRpm.pathsOf_ideal2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.pathsOf_ideal2

/-- info: 'LeanRpm.not_keccakNF_of_pad' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.not_keccakNF_of_pad

/-- info: 'LeanRpm.keccakNF_blockTo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.keccakNF_blockTo

/-- info: 'LeanRpm.keccak256_transfer2' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.keccak256_transfer2

/-- info: 'LeanRpm.SufCma.rpm_le_rom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.SufCma.rpm_le_rom

/-- info: 'LeanRpm.SufCma.rpm_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.SufCma.rpm_bound

/-- info: 'LeanRpm.SufCma.rpm_bound_perm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanRpm.SufCma.rpm_bound_perm
