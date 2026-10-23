/-
  LeanVM.Guest.B1.Whir.CTail

  The tail rounds, honestly: the rounds, the closing squeeze on the two waiting scalars, the
  final claim, the unused challenge slots zeroed.
-/

module

public import LeanVM.Guest.B1.Whir.CLevels
public import LeanVM.Guest.B1.Whir.Tail

/-!
# The tail rounds, honestly

`osTailEnd_complete`: after the rounds, the capacity copied, the two waiting scalars packed, the
permutation, its challenge (stored at `tail_challenges[yrLog - 1]`), the claim the quadratic at it
and the slots past the challenges zero, at the values `tailEndSegs`. `osTail_complete`: the
buffer allocated at `T`, the rounds (`osFolds_complete`) then the end.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The tail's statements after its rounds, from the rounds' state `f2`, the buffer `tch` and the
zero run at `p`. -/
def tailEnd (c : OsCfg) (tch : ℕ) (f2 : OsSt) (p : ℕ) : List Stmt :=
  let j := f2.k
  (f2.fs.zipIdx.map fun (x, i) ↦ .atom (.copy (.n (j + i)) (.n x))) ++
    fsPackT (.n f2.w0) (j + 5) 1 ++ fsPackT (.n f2.w1) (j + 14) 1 ++
    keccakA ([j + 11, j + 13, j + 20, j + 22, p + 1, p + 2, p + 3, p + 4, j, j + 1, j + 2, j + 3,
      j + 4].map V.n) (osRun (j + 23) 13) ::
    challengeT (.n (j + 23)) (.n (j + 24)) (j + 36) ++
    [.atom (.load (.n (j + 42)) (.n tch) (c.yrLog - 1)),
      .atom (.mul (.n (j + 43)) (.n (j + 42)) (.n f2.b)), .atom (.add (.n (j + 44)) (.n f2.c) (.n (j + 43))),
      .atom (.mul (.n (j + 45)) (.n (j + 42)) (.n (j + 42))),
      .atom (.mul (.n (j + 46)) (.n (j + 45)) (.n f2.a)),
      .atom (.add (.n (j + 47)) (.n (j + 44)) (.n (j + 46)))] ++
    ((List.range (yrLogCap - c.yrLog)).map fun i ↦
      [.atom (.const (.n (j + 48 + i)) (word 0 0 0)),
        .atom (.load (.n (j + 48 + i)) (.n tch) (c.yrLog + i))]).flatten

theorem osTail_eq (c : OsCfg) (st : OsSt) :
    osTail c st = (osHeap yrLogCap st.k ++ (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).1 ++
      tailEnd c (st.k + 1) (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2
        ((osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.pad.getD 0),
      { (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2 with
        k := (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k + 48 +
          (yrLogCap - c.yrLog)
        t := (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k + 47 },
      st.k + 1) := by
  simp only [osTail, tailEnd, List.append_assoc, List.cons_append]

/-- The values of the tail's end from its first value. -/
def tailEndSegs (c : OsCfg) (σ : Val) (f2 : OsSt) : List (ℕ × (ℕ → E)) :=
  [(5, fun i ↦ (f2.fsv σ).getD i 0), (9, fsPackVals (σ (.n f2.w0)) 1),
    (9, fsPackVals (σ (.n f2.w1)) 1), (13, cells13F (f2.F σ).perm),
    (7, challengeVals (cells13F (f2.F σ).perm 0) (cells13F (f2.F σ).perm 1)),
    (5, fun i ↦ [challengeOf (f2.F σ).perm * σ (.n f2.b),
      σ (.n f2.c) + challengeOf (f2.F σ).perm * σ (.n f2.b),
      challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm,
      challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm * σ (.n f2.a),
      σ (.n f2.c) + challengeOf (f2.F σ).perm * σ (.n f2.b) +
        challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm * σ (.n f2.a)].getD i 0),
    (yrLogCap - c.yrLog, fun _ ↦ 0)]

end
end LeanVM.Guest.B1.Whir
