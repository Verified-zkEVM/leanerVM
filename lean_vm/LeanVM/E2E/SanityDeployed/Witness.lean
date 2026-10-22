/-
  LeanVM.E2E.SanityDeployed.Witness

  S1 is not vacuous: a leaf holding one leanXMSS claim directly, by a signature valid at
  BLAKE2s (honest leanXMSS's, `xgCore`), meets every hypothesis of `sanity_deployed_of_tree` but
  its proofs of work.
-/

module

public import LeanVM.E2E.SanityDeployed
public import LeanVM.E2E.Complete.Rom.Gen

/-!
# An inhabitant of S1

The leaf `xmssLeaf pk σ` (`Complete/Rom/Gen.lean`: one leanXMSS claim `(pk, 0)` held directly by
`σ`), at the rate `1`:

* it is valid at BLAKE2s whenever `σ` verifies under `pk` at BLAKE2s (`valid_xmssLeaf`); honest
  leanXMSS run at BLAKE2s outputs such a pair (`xg_correct`, leanXMSS's correctness at every hash);
* it is within the deployed limits and budget (`withinLimitsDep_xmssLeaf`; the work is the
  shapes', the budget evaluated by the kernel as in `Witness.lean`);
* its size is `1`.

The one condition left is the event that the leaf's proofs of work succeed within `pfuel`
(`PowGoodDep`, about BLAKE2s outputs, not decided here; each search of the deployed verifier's
`17`-bit proofs of work fails with probability `(1 - 2^-17)^pfuel` under the random-oracle reading,
the completeness term of `LeanVM.completeness`). Under it, `sanity_deployed_xmssLeaf`: the deployed
prover outputs, the deployed verifier accepts, and V_I accepts or a compression collision occurs.
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa
open LeanVM.E2E.Complete LeanVM.E2E.Sanity

@[expose] public section

/-- **A leaf holding one leanXMSS claim directly is within the deployed limits and the budget**,
at its deployed deferred claim, for every key and signature (`xmssLeaf_limits` at
`leafDeferDep`). -/
theorem xmssLeaf_limitsDep (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    End.Limits ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩ ⟨[], [.direct σ], [], [], noHints⟩ ∧
      B2C.b2cBudget'.size
        (End.work ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩ ⟨[], [.direct σ], [], [], noHints⟩) ≤
        2 ^ 28 := by
  have hcov : End.coverage ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩
      ⟨[], [.direct σ], [], [], noHints⟩ = 1 := by
    simp [End.coverage, Hints.plan, Hints.direct, Hints.takeSlots, Hints.takeSlot,
      Hints.takeSlotsAll]
  have hwork : End.work ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩ ⟨[], [.direct σ], [], [], noHints⟩ =
      ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := by
    rw [End.work, hcov]
    rfl
  refine ⟨{ stackLog := fun c hc ↦ absurd hc List.not_mem_nil
            stream := fun c hc ↦ absurd hc List.not_mem_nil
            directDa := Nat.zero_le _
            xmssHeld := fun x ↦ by simp [Hints.direct]
            sphincsHeld := fun x ↦ by simp
            daHeld := fun x ↦ by simp
            children := Nat.zero_le _
            daRoots := ⟨Nat.zero_le _, fun c hc ↦ absurd hc List.not_mem_nil⟩
            lists := fun c hc ↦ absurd hc List.not_mem_nil
            coverage := by rw [hcov]; norm_num
            nonempty := Nat.one_pos }, ?_⟩
  rw [hwork]
  refine (End.sizeOf_mono words_wTree instrs_wTree).trans ?_
  simp only [End.sizeOf, instrsBound, Memory.logMem, Nat.clog_pow 2 _ one_lt_two, guest_logSize,
    minLogMem]
  norm_num

variable (ρ pfuel : ℕ)

/-- A leaf has no children's outputs. -/
theorem kidOutsDep_nil : kidOutsDep ρ pfuel [] = some [] := rfl

/-- A leaf's deployed deferred claim. -/
theorem deferDep_nil : deferDep [] = some (noHints, leafDeferDep) := by
  simp only [deferDep, ↓reduceIte]

/-- The leaf's children's outputs and deferred claim. -/
theorem leaf_outsDep {kos : List DepOut} (hkos : kidOutsDep ρ pfuel [] = some kos)
    {hd : BatchHints × DeferredClaim} (hdef : deferDep (kos.map DepOut.child) = some hd) :
    kos = [] ∧ hd = (noHints, leafDeferDep) := by
  rw [kidOutsDep_nil, Option.some.injEq] at hkos
  subst hkos
  rw [List.map_nil, deferDep_nil, Option.some.injEq] at hdef
  exact ⟨rfl, hdef.symm⟩

/-- **The leaf is within the deployed limits and budget.** -/
theorem withinLimitsDep_xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssLeaf pk σ).WithinLimitsDep ρ pfuel := by
  rw [xmssLeaf, HonestTree.WithinLimitsDep, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef
  obtain ⟨rfl, rfl⟩ := leaf_outsDep ρ pfuel hkos hdef
  exact xmssLeaf_limitsDep pk σ

/-- **The leaf's proofs of work are found** when the proof-of-work event holds at its digest. -/
theorem powFoundDep_xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature)
    (hpow : PowGoodDep pfuel (digestOf blake2sBytes ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩)) :
    (xmssLeaf pk σ).PowFoundDep ρ pfuel := by
  rw [xmssLeaf, HonestTree.PowFoundDep, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef
  obtain ⟨rfl, rfl⟩ := leaf_outsDep ρ pfuel hkos hdef
  exact hpow

/-- **S1 on a leanXMSS leaf.** For a leanXMSS key and a signature of the zero message valid at
BLAKE2s, if the leaf's proofs of work succeed within `pfuel`: the deployed prover outputs at the
rate `1`, the statement makes the claim, the deployed verifier accepts it, and V_I with BLAKE2s
accepts it at every positive fuel unless a compression collision occurs. -/
theorem sanity_deployed_xmssLeaf {pk : LeanXmss.PublicKey} {σ : LeanXmss.Signature}
    (hsig : xmssVerifyWith (fun x ↦ some (blake2sBytes x)) pk 0 σ = some true)
    (hpow : PowGoodDep pfuel (digestOf blake2sBytes ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩))
    {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    ∃ s π ip, deployedProve 1 pfuel (xmssLeaf pk σ) = some (s, π, ip) ∧
      s.claims = ⟨[(pk, 0)], [], []⟩ ∧ Node.verifyAggregate guest s π ∧
      (idealVerify (m := Id) blakeId guest ip fuel s = true ∨ CompressionCollision) :=
  sanity_deployed_of_tree 1 pfuel (xmssLeaf pk σ) hyps_wTree.1 (valid_xmssLeaf hsig)
    (withinLimitsDep_xmssLeaf 1 pfuel pk σ) (powFoundDep_xmssLeaf 1 pfuel pk σ hpow)
    ((xmssLeaf_size pk σ).trans hfuel)

/-- **S1 on honest leanXMSS at BLAKE2s**: the key and signature honest leanXMSS outputs with
BLAKE2s (`xgCore`: key generation from the zero seed, a signature at leaf `0` of the zero
message), under the leaf's proof-of-work event. -/
theorem sanity_deployed_honestXmss {pk : LeanXmss.PublicKey} {σ : LeanXmss.Signature}
    (hgen : xgEv (xgBits blake2sBytes) xgCore = some (pk, σ))
    (hpow : PowGoodDep pfuel (digestOf blake2sBytes ⟨⟨[(pk, 0)], [], []⟩, leafDeferDep⟩))
    {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    ∃ s π ip, deployedProve 1 pfuel (xmssLeaf pk σ) = some (s, π, ip) ∧
      s.claims = ⟨[(pk, 0)], [], []⟩ ∧ Node.verifyAggregate guest s π ∧
      (idealVerify (m := Id) blakeId guest ip fuel s = true ∨ CompressionCollision) :=
  sanity_deployed_xmssLeaf pfuel
    (by rw [xmssVerifyWith_some_eq_xgEv, xg_correct _ _ _ hgen]) hpow hfuel

end
end LeanVM.E2E.SanityDeployed
