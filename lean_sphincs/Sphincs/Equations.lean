module

public import Statement.LeanSphincs

/-!
# The statement's chains, folds and trees, step by step

`Statement/LeanSphincs.lean` writes the chains and the path folds as instances of `walkChain` and
`foldPath`; their equations here are the guest proofs' (`lean_vm`) unfolding of each, step by step.
The proofs of this project have the same equations for the layered presentation
(`Sphincs/Scheme.lean`).
-/

open OracleComp OracleSpec

namespace Sphincs

@[expose] public section

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)

theorem chainWalk_eq_zero (leaf : Index) (chainIdx : ChainIndex) (start : Nat) (value : Digest) :
    chainWalk (m := m) parameter leaf chainIdx start 0 value = pure value := rfl

theorem chainWalk_eq_succ (leaf : Index) (chainIdx : ChainIndex) (start steps : Nat)
    (value : Digest) :
    chainWalk (m := m) parameter leaf chainIdx start (steps + 1) value = (do
      let previous ← chainWalk parameter leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0) := rfl

theorem forestWalk_eq_zero (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (i : FChain) (start : Nat) (value : Digest) :
    forestWalk (m := m) parameter index c s j a i start 0 value = pure value := rfl

theorem forestWalk_eq_succ (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (i : FChain) (start steps : Nat) (value : Digest) :
    forestWalk (m := m) parameter index c s j a i start (steps + 1) value = (do
      let previous ← forestWalk parameter index c s j a i start steps value
      if hstep : start + steps < chainTop then
        tweakableHash parameter (.fchain index c s j a i ⟨start + steps, hstep⟩) (bytesLE 16 previous)
      else
        pure 0) := rfl

theorem treeFold_eq_zero (leaf : Index) (path : Nat → Digest) (value : Digest) :
    treeFold (m := m) parameter leaf path 0 value = pure value := rfl

theorem treeFold_eq_succ (leaf : Index) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter leaf path (levels + 1) value = (do
      let current ← treeFold parameter leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node (levels + 1) nodeIdx) (nodePayload current sibling)) := by
  show _ >>= _ = _ >>= _
  congr 1
  funext current
  split <;> rfl

theorem subFold_eq_zero (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (path : Fin subHeight → Digest) (value : Digest) :
    subFold (m := m) parameter index c s j a path 0 value = pure value := rfl

theorem subFold_eq_succ (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (path : Fin subHeight → Digest) (levels : Nat) (value : Digest) :
    subFold (m := m) parameter index c s j a path (levels + 1) value = (do
      let current ← subFold parameter index c s j a path levels value
      if hlevel : levels < subHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : ChildIdx := ⟨a.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩
        if a.val.testBit levels then
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0) := by
  show _ >>= _ = _ >>= _
  congr 1
  funext current
  have hnode : a.val / 2 ^ (levels + 1) % 2 ^ subHeight = a.val / 2 ^ (levels + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)
  simp only [subNodeHash, hnode]
  split
  · split <;> rfl
  · rfl

theorem topFold_eq_zero (index : Index) (c : Coord) (s : SuperIdx) (path : Fin topHeight → Digest)
    (value : Digest) : topFold (m := m) parameter index c s path 0 value = pure value := rfl

theorem topFold_eq_succ (index : Index) (c : Coord) (s : SuperIdx) (path : Fin topHeight → Digest)
    (levels : Nat) (value : Digest) :
    topFold (m := m) parameter index c s path (levels + 1) value = (do
      let current ← topFold parameter index c s path levels value
      if hlevel : levels < topHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : SuperIdx := ⟨s.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt⟩
        if s.val.testBit levels then
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0) := by
  show _ >>= _ = _ >>= _
  congr 1
  funext current
  have hnode : s.val / 2 ^ (levels + 1) % 2 ^ topHeight = s.val / 2 ^ (levels + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt)
  simp only [topNodeHash, hnode]
  split
  · split <;> rfl
  · rfl

end Concrete

end

end Sphincs
