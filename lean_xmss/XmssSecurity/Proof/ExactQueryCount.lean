module

public import XmssSecurity.Proof.IdealStatement

@[expose] public section

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

inductive ExactQueryCount {index : Type} {spec : OracleSpec index} :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactQueryCount (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount (liftM (spec.query input) >>= next) (count + 1)

inductive ExactPredicateQueryCount {index : Type} {spec : OracleSpec index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate] :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactPredicateQueryCount predicate (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat)
      (hnext : ∀ output, ExactPredicateQueryCount predicate (next output) count) :
      ExactPredicateQueryCount predicate
        (liftM (spec.query input) >>= next)
        (count + if predicate input then 1 else 0)

namespace ExactQueryCount

theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactQueryCount.query input (fun output => rest output >>= next)
          (restCount + nextCount) ih

theorem map {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  convert hcomputation.bind
    (fun value => (Pure.pure (f value) : OracleComp spec β)) 0
    (fun value => ExactQueryCount.pure (f value)) using 1
  simp [map_eq_bind_pure_comp]


namespace ExactPredicateQueryCount

variable {index : Type} {spec : OracleSpec index}
variable {predicate : spec.Domain → Prop} [DecidablePred predicate]

theorem of_isQueryBoundP_zero
    {computation : OracleComp spec α}
    (hbound : computation.IsQueryBoundP predicate 0) :
    ExactPredicateQueryCount predicate computation 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hinput : ¬predicate input := hbound.1.resolve_right (by omega)
      simpa [hinput] using ExactPredicateQueryCount.query input next 0
        (fun output => ih output (by simpa [hinput] using hbound.2 output))

end ExactPredicateQueryCount

theorem oracleHash (input : HashInput) :
    ExactQueryCount (Concrete.oracleHash input : OracleComp HashSpec HashOutput) 1 := by
  exact .query input (fun output => (Pure.pure output : OracleComp HashSpec HashOutput)) 0
    (fun output => ExactQueryCount.pure output)

theorem tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    ExactQueryCount
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 := by
  unfold Concrete.tweakableHash
  exact (oracleHash _).map truncateHash

theorem chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest)
    (hposition : position + steps ≤ chainLength - 1) :
    ExactQueryCount
      (Concrete.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain
        position steps value) steps := by
  induction steps generalizing value with
  | zero => exact .pure value
  | succ steps ih =>
      rw [Concrete.chainWalk]
      have hstep : position + steps < chainLength - 1 := by omega
      simp only [hstep, ↓reduceDIte]
      exact (ih value (by omega)).bind
        (fun previous => Concrete.chainHash parameter leafIndex chain
          ⟨position + steps, hstep⟩ previous) 1
        (fun previous => tweakableHash parameter (.chain leafIndex chain
          ⟨position + steps, hstep⟩) (Concrete.digestBytes previous))

theorem sequenceFin {n : Nat} (computation : Fin n → OracleComp spec α)
    (count : Fin n → Nat)
    (hcomputation : ∀ index, ExactQueryCount (computation index) (count index)) :
    ExactQueryCount (Concrete.sequenceFin computation)
      (∑ index, count index) := by
  induction n with
  | zero => exact .pure Fin.elim0
  | succ n ih =>
      rw [Concrete.sequenceFin, Fin.sum_univ_succ]
      exact (hcomputation 0).bind
        (fun head => do
          let tail ← Concrete.sequenceFin fun index : Fin n => computation index.succ
          Pure.pure (show Fin (n + 1) → α from Fin.cases head tail))
        (∑ index : Fin n, count index.succ)
        (fun head => (ih (fun index => computation index.succ)
          (fun index => count index.succ) (fun index => hcomputation index.succ)).bind
            (fun tail => Pure.pure
              (show Fin (n + 1) → α from Fin.cases head tail)) 0
            (fun tail => ExactQueryCount.pure
              (show Fin (n + 1) → α from Fin.cases head tail)))

end ExactQueryCount
end XmssSecurity
