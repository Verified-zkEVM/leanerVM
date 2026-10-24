/-
  LeanVM.Guest.Budget.Final

  `MainComplete` within a budget from `main`'s bounded completeness (B1-f's `main_honest_budgetB`),
  its callees' static bounds and counts, each child's `verify_sub` within `Bvf` at its announced stack log and rate, and the budget's
  two clauses on the bounds.
-/

module

public import LeanVM.Guest.Budget.End
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.Budget.Instrs

/-!
# `main` within the budget

`mainComplete_of_main`: `End.MainComplete fs cert cnt b` from
* B1-f's `main_honest_budgetB` at `0` (the signature schemes' specs, the frame runs' fit, the
  static callees' words `MainStatics`, each child's `verify_sub` within `Bvf` at its announced stack log and rate);
* the counts within the frame weights `ω op` and the jump table's `jt op` (`hcnt`), `main`'s
  callees' weights `MainCounts (ω op) fs` (`H`), and the children's loop's within `K5 op s w`
  (`h5`);
* the budget's clauses: `Bmain` within its words, `mainCount` plus `jt` within its
  instructions.
`mainComplete_budget`: within `mainBudget`, the children's loop at `l5Lin`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.End (MainComplete Budget work bytecode bytecode_length)
open LeanVM.Guest.B1.Main (Bmain mainBsH hm hData mainPredsH hDvNH VerifySubGoalsTB MainStatics
  main_honest_budgetB hData_bounds childBv)

@[expose] public section

/-- **`main` is complete within the budget `b`**, from its bounded completeness, its callees'
bounds and counts, and the budget's clauses. -/
theorem mainComplete_of_main (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    (b : Budget) {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hS : MainStatics fs SB SK)
    (hV : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w →
      CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
      VerifySubGoalsTB fs cert 0 seed s w (Pvs w) (childBv Bvf w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op)
    (K5 : Opcode → NodeStatement → NodeWitness → ℕ)
    (h5 : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "__loop5" → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH s w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ K5 op s w)
    (hwords : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w →
      Bmain fs SB SK (childBv Bvf w) 0 seed s w ≤ b.words.eval (work s w))
    (hinstrs : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w → ∀ op,
      mainCount (H op) (hm fs 0 seed s w) (mainBsH fs SB SK (childBv Bvf w) s w) (K5 op s w) +
        jt op ≤ (b.instrs op).eval (work s w)) :
    MainComplete fs cert cnt b := by
  refine mainComplete_of_bounds fs cert cnt b
    (fun seed s w rd t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧
      B1.Main.MVals rd σ (hm fs 0 seed s w) ∧
      KidsT (B1.Main.mCalls σ (hm fs 0 seed s w))
        ((fun _ => True) :: B1.Main.mTs (hm fs 0 seed s w)
          ((mainPredsH s w (hDvNH s w) (Pvs w)).withTotal fs (mainBsH fs SB SK (childBv Bvf w) s w))) ks ∧
      calls (B1.Main.mEvs σ) = B1.Main.mCalls σ (hm fs 0 seed s w) ∧ bufs = B1.Main.mSizes (hData seed s w))
    (fun seed s w => Bmain fs SB SK (childBv Bvf w) 0 seed s w) hfs ?_ ?_ hwords
  · intro seed s w hrel hlim hcap hnz
    obtain ⟨n, L, hn, hW, hab, hD, -, hR⟩ := main_honest_budgetB bytecode_length hrel hlim hxc hsc
      hrf hS (hV seed s w hrel hlim hcap hnz)
    exact ⟨n, L, hn, hW, fun q hq => by simpa using hab q hq, hD, hR⟩
  · intro seed s w hrel hlim rd t hTt hv hb op
    obtain ⟨σ, bufs, ks, ht, hMV, hT, hc, -⟩ := hTt
    subst ht
    have hw := main_weight_count (H op) (K5 op s w) (h5 seed s w hrel hlim op) hv hb hc hMV
      (hData_bounds hlim fs 0) hT
    have := hcnt rd _ hv op
    have := hinstrs seed s w hrel hlim op
    omega

/-- **The budget**: `main`'s words (B1-f's `mainWords`) and instructions (`mainInstrs`) at the
static bounds `SB`, `SK`, `verify_sub`'s words `Bvf μ r` at a child's announced stack log `μ` and
rate `r`, the callees' weights `H`, the children's loop's instructions `l5Lin (c5 op) (s5 op)
(v5 op)` and the jump table's `jt`. -/
def mainBudget (fs : String → ℕ) (SB SK : String → ℕ) (Bvf : ℕ → ℕ → ℕ) (ω : Opcode → String → ℕ)
    (H : ∀ op, MainCounts (ω op) fs) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (jt : Opcode → ℕ) : Budget :=
  ⟨B1.Main.mainWords fs SB SK Bvf,
    fun op => mainInstrs (H op) SB SK (c5 op) (s5 op) (v5 op) (jt op)⟩

/-- **`main` is complete within `mainBudget`.** -/
theorem mainComplete_budget (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hS : MainStatics fs SB SK)
    (hV : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w →
      CapsAgree bytecode seed w → NoZeroChallenge bytecode seed w →
      VerifySubGoalsTB fs cert 0 seed s w (Pvs w) (childBv Bvf w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRel bytecode seed s w → Limits bytecode s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "__loop5" → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH s w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (work s w)) :
    MainComplete fs cert cnt (mainBudget fs SB SK Bvf ω H c5 s5 v5 jt) :=
  mainComplete_of_main fs cert cnt _ ω jt H hfs hxc hsc hrf hS hV hcnt
    (fun op s w => l5Lin (c5 op) (s5 op) (v5 op) (work s w)) h5
    (fun _ _ _ hr hl => B1.Main.Bmain_le fs SB SK Bvf hr hl)
    (fun _ _ w hr hl op => mainCount_le (H op) SB SK (childBv Bvf w) (c5 op) (s5 op) (v5 op) (jt op)
      hr hl)

end
end LeanVM.Guest.Budget
