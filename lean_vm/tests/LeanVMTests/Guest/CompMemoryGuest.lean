import LeanVM.Guest.Memory.GuestBoundsAtB
import LeanVM.Guest.Memory.GuestSizeB
import LeanVM.Guest.Memory.GuestRelInB
import LeanVM.Guest.Memory.GuestCntBB
import LeanVM.Guest.Memory.GuestCntDB
import LeanVM.Guest.Memory.GuestCntJB
import LeanVM.Guest.Memory.GuestCntMB
import LeanVM.Guest.Memory.GuestCntSB
import LeanVM.Guest.Memory.GuestCntXB
import LeanVM.Guest.Memory.GuestCntOBB
import LeanVM.Guest.Memory.GuestCntODB
import LeanVM.Guest.Memory.GuestCntOJB
import LeanVM.Guest.Memory.GuestCntOMB
import LeanVM.Guest.Memory.GuestCntOSB
import LeanVM.Guest.Memory.GuestCntOXB

/-!
# Tests: the guest's generated bounds under any `BLAKE2S` semantics (L2, Memory)

* The B versions of the generated bound wrappers (`Memory/GuestWordsB`, `GuestBoundsB`,
  `GuestBoundsAtB`, `GuestSizeB`, `GuestRelInB`, `GuestCnt*B`, `GuestCntO*B`) rest on Lean's three
  axioms.
* **At the deployed semantics they are the deployed ones**: `verifyB_lean_xmss_totalLe_at`,
  `kwxB_weightLe`, `kwoxB_weightLe` and `relInB_of_inv` at `blakeDeployed`, through the
  `…B_deployed` lemmas, give `verify_lean_xmss_totalLe_at`, `kwx_weightLe`, `kwox_weightLe` and
  `relIn_of_inv`'s conclusion.
-/

namespace LeanVMTests.Guest.CompMemoryGuest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.handOkB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.handOkB_of

/-- info: 'LeanVM.Guest.coreB_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.coreB_totalLe

/-- info: 'LeanVM.Guest.coreB_total_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.coreB_total_le_of_stat

/-- info: 'LeanVM.Guest.coreB_total_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.coreB_total_le_of_loop

/-- info: 'LeanVM.Guest.whandB_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.whandB_none

/-- info: 'LeanVM.Guest.verifyB_lean_xmss_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.verifyB_lean_xmss_totalLe

/-- info: 'LeanVM.Guest.statementB_digest_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.statementB_digest_totalLe

/-- info: 'LeanVM.Guest.loop86B_totalLeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.loop86B_totalLeOn

/-- info: 'LeanVM.Guest.verifyB_lean_xmss_totalLe_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.verifyB_lean_xmss_totalLe_at

/-- info: 'LeanVM.Guest.loop86B_totalLeOn_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.loop86B_totalLeOn_at

/-- info: 'LeanVM.Guest.assertB_canonical_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.assertB_canonical_totalLe

/-- info: 'LeanVM.Guest.loop84B_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.loop84B_totalLe

/-- info: 'LeanVM.Guest.loop85B_totalLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.loop85B_totalLe

/-- info: 'LeanVM.Guest.Memory.relInB_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInB_of_inv

/-- info: 'LeanVM.Guest.Memory.relInTB_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInTB_of_inv

/-- info: 'LeanVM.Guest.Memory.RelInTB.relIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.RelInTB.relIn

/-- info: 'LeanVM.Guest.Memory.relAtInB_of_relInT_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relAtInB_of_relInT_pure

/-- info: 'LeanVM.Guest.Memory.relInTB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.Memory.relInTB_deployed

/-- info: 'LeanVM.Guest.kwbB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwbB_weightLe

/-- info: 'LeanVM.Guest.kwbB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwbB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwbB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwbB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwdB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwdB_weightLe

/-- info: 'LeanVM.Guest.kwdB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwdB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwdB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwdB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwjB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwjB_weightLe

/-- info: 'LeanVM.Guest.kwjB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwjB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwjB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwjB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwmB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwmB_weightLe

/-- info: 'LeanVM.Guest.kwmB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwmB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwmB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwmB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwsB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwsB_weightLe

/-- info: 'LeanVM.Guest.kwsB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwsB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwsB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwsB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwxB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwxB_weightLe

/-- info: 'LeanVM.Guest.kwxB_weight_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwxB_weight_le_of_stat

/-- info: 'LeanVM.Guest.kwxB_weight_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwxB_weight_le_of_loop

/-- info: 'LeanVM.Guest.kwobB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwobB_weightLe

/-- info: 'LeanVM.Guest.kwodB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwodB_weightLe

/-- info: 'LeanVM.Guest.kwojB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwojB_weightLe

/-- info: 'LeanVM.Guest.kwomB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwomB_weightLe

/-- info: 'LeanVM.Guest.kwosB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwosB_weightLe

/-- info: 'LeanVM.Guest.kwoxB_weightLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.kwoxB_weightLe

/-! ## At the deployed semantics -/

/-- `verifyB_lean_xmss_totalLe_at` at `blakeDeployed` is `verify_lean_xmss_totalLe_at`. -/
example {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLe coreProgram fs' "verify_lean_xmss" fun _ => 1721 := by
  rw [← totalLeB_deployed]; exact verifyB_lean_xmss_totalLe_at h

/-- `kwxB_weightLe` at `blakeDeployed` is `kwx_weightLe`. -/
example {f : String} {B : ℕ} {ks : List (V × ℕ)} (hcf : kwxcertOf f = .stat [] ⟨B, []⟩ ks) :
    WeightLe coreProgram (kcOm .xor) f fun _ => B := by
  rw [← weightLeB_deployed]; exact kwxB_weightLe hcf

/-- `kwoxB_weightLe` at `blakeDeployed` is `kwox_weightLe`. -/
example {f : String} {B : ℕ} {ks : List (V × ℕ)} (hcf : kwoxcertOf f = .stat [] ⟨B, []⟩ ks) :
    WeightLe coreProgram (kcOm .xor) f fun _ => B := by
  rw [← weightLeB_deployed]; exact kwoxB_weightLe hcf

/-- `relInB_of_inv` at `blakeDeployed` gives `relIn_of_inv`'s conclusion. -/
example {rd : Reader} {R : ℕ → Prop} (Inv : String → List E → Prop)
    (hinv : ∀ f args σ fn es vs, Inv f args → coreProgram.find? f = some fn →
      fn.params.map σ = args → walk σ fn.body = .ret es vs →
      (∀ e ∈ es, e.Ok (coreProgram.Rel rd) rd σ) →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i) ∧
        ∀ c ∈ calls es, c.taken = true → Inv c.f (c.args.map σ))
    {f : String} {args rets : List E} (hI : Inv f args) (hrel : coreProgram.Rel rd f args rets) :
    coreProgram.RelIn rd R f args rets := by
  rw [← relInB_deployed]
  refine relInB_of_inv Inv (fun f args σ fn es vs hI hf hp hw hok => hinv f args σ fn es vs hI hf hp hw
    fun e he => ?_) hI (by rwa [relB_deployed])
  rw [← ev_okB_deployed, ← relB_deployed]; exact hok e he

end LeanVMTests.Guest.CompMemoryGuest
