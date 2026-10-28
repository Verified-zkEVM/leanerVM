/-
  LeanVM.Guest.B1.Main.MainGoalsHAgT

  `main`'s honest `aggregate_claims` call, by a tree of honest shape (`aggHonest`): `mainGoalAg`
  (same proof) with `aggregate_claims_completeAtT`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHAg
public import LeanVM.Guest.B1.Main.AggAtT

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (Limits)
open LeanVM.Guest.B1 (CompleteAtDT CompleteAtD Returns bufL)

@[expose] public section

variable (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
variable {seed s w}

/-- **`main`'s honest `aggregate_claims` call is complete, by a tree of honest shape**: under `NodeRel` and `Limits`, for a
bytecode of `2^bytecodeVars` words. -/
theorem mainGoalAgT (cert : String → V → ℕ) {bytecode : List K}
    (hbl : bytecode.length = 2 ^ bytecodeVars) (hrel : NodeRel bytecode seed s w)
    (hl : Limits s w) : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDT fs cert 16 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417] (Returns [])
        (aggHonest (hm fs fp seed s w).nc) := by
  intro hnc
  have hnc' : w.children.length ≠ 0 := hnc
  have hne : w.children ≠ [] := fun h => hnc' (by rw [h, List.length_nil])
  have hb := hrel.2.2.2.2.2
  simp only [hne, ↓reduceIte] at hb
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  have hrl : w.hints.bytecodeRounds.length = 23 := by
    have hpt : s.defer.bytecodePoint.length = 23 := by rw [hrel.1, hlog]
    rw [(batch_out hb).1, aggOut, aggRun, bsRun_len] at hpt
    exact hpt
  have hdst := mem_hLmain fs fp seed s w (i := 10) (by omega)
  simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero] at hdst
  have := aggregate_claims_completeAtT fs cert (m := w.children.length) (by omega) hl.children
    (cs := hKids seed w) (by rw [List.length_map]) hrl hb
    (fun rd hM => hkids_words fs fp hbl hrel hM) hdst
  exact this

end
end LeanVM.Guest.B1.Main
