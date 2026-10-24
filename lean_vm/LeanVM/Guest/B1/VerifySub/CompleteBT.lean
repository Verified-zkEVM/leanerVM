/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteAll
public import LeanVM.Guest.B1.Terminal.KidsDepBT
public import LeanVM.Guest.ChildShape

/-!
# `verify_sub` by its callees' trees

`vsNames μ r`: the thirteen callees in call order (`vs_calls`), `open_stacked`'s candidate
`openName μ r`. `vsTs fs W Bvk μ r`: callee `j` a call of `vsNames μ r`'s `j`-th name within
`vsBsAt W Bvk μ r`'s `j`-th bound. `vsBoundAt W Bvk μ r = fs "verify_sub" + 9156 +
(vsBsAt W Bvk μ r).sum`.

`verify_sub_completeBT`: `verify_sub_completeB` within the child's own bound (its announced stack
log and rate, `childShape`), by a node of `Budget.FlatShape` for `vsTs`. `verify_sub_completeBT_fs`:
at `B2C.fs`, `verify_keccak` within `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`verify_sub`'s callees' names**, in call order (`vs_calls`). -/
def vsNames (μ r : ℕ) : List String :=
  ["g_power_of_word", "g_power_of_word", "log2_ceil_in_the_exponent__L0_L34", "assert_canonical",
    "assert_canonical", "verify_bus_gkr", "verify_tables", "verify_keccak", "ring_switch_target",
    "certify_placement", "log2_ceil_in_the_exponent__L15_L34", B1.Whir.openName μ r,
    "check_opening_terminal"]

/-- **`verify_sub`'s callees' trees**: callee `j` a call of its name within its bound. -/
noncomputable def vsTs (fs : String → ℕ) (W : VsWords fs) (Bvk μ r : ℕ) : List (Tree → Prop) :=
  List.zipWith (Budget.NamedWithin fs) (vsNames μ r) (vsBsAt W Bvk μ r)

/-- **`verify_sub`'s bound at one candidate.** -/
noncomputable def vsBoundAt {fs : String → ℕ} (W : VsWords fs) (Bvk μ r : ℕ) : ℕ :=
  fs "verify_sub" + 9156 + (vsBsAt W Bvk μ r).sum

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (lpE sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs lpE sqE) (vsNames S.μs S.rate) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) .nil))))))))))))

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxHeartbeats 2000000 in
/-- **`verify_sub` is complete on every honest child within its own bound**, by a node whose
callees are calls of their names within their bounds, at the child's announced stack log and
rate. -/
theorem verify_sub_completeBT {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hap : Lift.RunsApart cert) (W : VsWords fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtB fs cert κ Bvk) (seed : Digest) (c : Child)
    (lpE sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Hints.streamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode
      (statementDigest seed c.statement)) (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin lpE sqE, q ∈ Lin) (hout : (outE, fixedCells c.fresh) ∈ Lin) :
    CompleteAtDTB fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs fs W Bvk (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W Bvk (childShape bytecode c).1 (childShape bytecode c).2) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hnz hcaps
  rw [childShape_of S.hann]
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs hκ hexpL hout
  have h := completeAt_flatDepRBT (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.μ) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.μ)) lpE sqE)
    (vsNames S.μs S.rate) (vsBsAt W Bvk S.μs S.rate) (fun _ ↦ vs_names S _ lpE sqE)
    (fun fp ↦ vs_kidsDepBAt hbl S hκ hrf hap W hvk _ lpE sqE) hkr hkm hσ
  refine h.mono ?_ fun _ ht ↦ ht
  have := (S.μ_bounds hbl).2
  simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]
  omega

/-- **`verify_sub` is complete within its own bound by its callees' trees** at the deployed frame
sizes, `verify_keccak` within `vkBound`. -/
theorem verify_sub_completeBT_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hap : Lift.RunsApart cert) (W : VsWords LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (seed : Digest) (c : Child) (lpE sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announced bytecode c.proof.stream = some (layout, r) →
      Hints.muMin ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Hints.streamCap)
    (hnz : Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.fresh
      c.proof = true)
    (hcaps : ∀ b ∈ Limits.queriesOf (deferredProgram c.fresh bytecode
      (statementDigest seed c.statement)) (Hints.childStart seed c), Limits.BatchAgrees b.1 b.2)
    (hexpL : ∀ q ∈ log2Lin lpE sqE, q ∈ Lin) (hout : (outE, fixedCells c.fresh) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin
      [(digestScalars (statementDigest seed c.statement)).1,
        (digestScalars (statementDigest seed c.statement)).2, (digestScalars seed).1,
        (digestScalars seed).2, ofK (gpow lpE), ofK (gpow sqE), ofK (gpow outE)] (Returns [])
      (Budget.FlatShape coreProgram "verify_sub"
        (vsTs LeanVM.Guest.B2C.fs W vkBound (childShape bytecode c).1 (childShape bytecode c).2))
      (vsBoundAt W vkBound (childShape bytecode c).1 (childShape bytecode c).2) :=
  verify_sub_completeBT hbl hrf hap W hκ (verify_keccak_completeAtB_fs κ) seed c lpE sqE outE Lin
    hmu hst hnz hcaps hexpL hout

end
end LeanVM.Guest.B1.VerifySub
