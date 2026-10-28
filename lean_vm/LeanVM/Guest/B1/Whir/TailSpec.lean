/-
  LeanVM.Guest.B1.Whir.TailSpec

  The Spec's tail rounds as fold rounds and one last sample.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Run

/-!
# The tail rounds (V:1761-1773)

`tailRounds (k + 1)` is `foldRounds k` (each round sampling, folding and reading the next
quadratic) then one last sample, its fold the final claim (`tailRounds_eq`): the guest runs the
tail as `k` `opening_fold` calls and a closing squeeze.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem tailRounds_eq : ∀ (k : ℕ) (t : E) (q : List E) (F : List E) (G : List GluedClaim)
    (lf : List E),
    (tailRoundsT (k + 1) t q).bind (fun r ↦ Prog.ret (lf ++ r.1, r.2)) =
      (foldRoundsT k ⟨t, q, F, G⟩ lf).bind fun p ↦
        Prog.sampleE.bind fun c ↦ Prog.ret (p.2 ++ [c], polyEval p.1.quad c)
  | 0, t, q, F, G, lf => by
    simp only [tailRoundsT, foldRoundsT, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind,
      ↓reduceIte, Prog.sampleE]
  | k + 1, t, q, F, G, lf => by
    simp only [tailRoundsT, foldRoundsT, Nat.add_one_ne_zero, ↓reduceIte, Prog.bind_eq,
      Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]
    refine prog_bind_congr fun c ↦ prog_bind_congr fun quad ↦ ?_
    have := tailRounds_eq k (polyEval q c) quad (F ++ [c]) G (lf ++ [c])
    simp only [List.append_assoc, List.singleton_append] at this ⊢
    exact this

end
end LeanVM.Guest.B1.Whir
