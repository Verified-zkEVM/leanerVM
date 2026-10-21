/-
  LeanVM.Guest.B2C.CntWeightB

  Counts as weights (`CntWeight.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CntWeight
public import LeanVM.Guest.Memory.EvalB

/-!
# Counts as weights under any `BLAKE2S` semantics

`CntWeight.lean`'s lemmas over the trees valid under `S : BlakeSem`: `weightVB_le_valid`,
`cntB_le_weight_valid`, `pathCountNB_le_arm`, `cntB_le_weight_arm`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

section Valid

variable {P : Core.Program} {rd : Reader} (ω : String → Val → ℕ) (ω' : String → ℕ)

mutual
theorem weightVB_le_valid
    (h : ∀ f σ bufs kids args rets, (Memory.Tree.node f σ bufs kids).ValidB S P rd args rets → ω f σ ≤ ω' f) :
    ∀ (t : Tree) (args rets : List E), t.ValidB S P rd args rets → weightV ω t ≤ t.weight ω'
  | .node f σ bufs kids, args, rets, hv => by
    have hn := h f σ bufs kids args rets hv
    obtain ⟨_, _, _, es, _, _, _, _, hk⟩ := hv
    rw [weightV, Tree.weight]
    exact Nat.add_le_add hn (weightVKidsB_le_valid h σ (calls es) kids hk)
  | .phantom .., _, _, hv => hv.elim

theorem weightVKidsB_le_valid
    (h : ∀ f σ bufs kids args rets, (Memory.Tree.node f σ bufs kids).ValidB S P rd args rets → ω f σ ≤ ω' f) :
    ∀ (σ : Val) (cs : List Call) (ks : List Tree), Tree.KidsValidB S P rd σ cs ks →
      weightVKids ω ks ≤ Tree.weightKids ω' ks
  | _, [], [], _ => by rw [weightVKids, Tree.weightKids]
  | _, [], _ :: _, hk => hk.elim
  | _, _ :: _, [], hk => hk.elim
  | σ, c :: cs, k :: ks, ⟨_, hk, hks⟩ => by
    rw [weightVKids, Tree.weightKids]
    refine Nat.add_le_add ?_ (weightVKidsB_le_valid h σ cs ks hks)
    split_ifs at hk
    · exact weightVB_le_valid h k _ _ hk
    · obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [weightV]
      exact Nat.zero_le _
end

end Valid

/-- **The counts within the weights** of a valid tree, each valid instance's path count within
its function's weight. -/
theorem cntB_le_weight_valid (ω : Opcode → String → ℕ)
    (h : ∀ op f σ bufs kids rd args rets, (Memory.Tree.node f σ bufs kids).ValidB S coreProgram rd args rets →
      pathCountN f σ op ≤ ω op f) :
    ∀ (rd : Reader) (t : Tree), t.ValidB S coreProgram rd [] [] → ∀ op, cnt t op ≤ t.weight (ω op) + jtSets op :=
  fun rd t hv op ↦ Nat.add_le_add_right
    (weightVB_le_valid _ _ (fun f σ bufs kids args rets hv' ↦ h op f σ bufs kids rd args rets hv') t [] [] hv) _

/-! ## The separately counted arms -/

/-- **A valid instance's path count within its weight**, given `verify_lean_xmss`'s arms within
`C` on its valid instances. -/
theorem pathCountNB_le_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node "verify_lean_xmss" σ bufs kids).ValidB S coreProgram rd args rets →
        costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ C op)
    (op : Opcode) (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) (rd : Reader)
    (args rets : List E) (hv : (Memory.Tree.node f σ bufs kids).ValidB S coreProgram rd args rets) :
    pathCountN f σ op ≤ ωArm C op f := by
  unfold ωArm pathCountN pathMax
  split
  · rename_i j hj
    unfold pathCount
    by_cases h17 : j = 17
    · subst h17
      obtain ⟨i, hi1, hi, hn, -, hcore, -⟩ := fn_of_idx hj
      have hf : f = "verify_lean_xmss" := by rw [← hn, ← hcore, coreOf17_name]
      subst hf
      simp only [↓reduceIte]
      have := hC op σ bufs kids rd args rets hv
      omega
    · rw [cplArms_only17 j h17, costW_nil, Pi.zero_apply]
      omega
  · exact Nat.zero_le _

/-- **The counts within the weights `ωArm C`** on valid trees. -/
theorem cntB_le_weight_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node "verify_lean_xmss" σ bufs kids).ValidB S coreProgram rd args rets →
        costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ C op) :
    ∀ (rd : Reader) (t : Tree), t.ValidB S coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ωArm C op) + jtSets op :=
  cntB_le_weight_valid (ωArm C) fun op f σ bufs kids rd args rets hv ↦
    pathCountNB_le_arm C hC op f σ bufs kids rd args rets hv

end
end LeanVM.Guest.B2C
