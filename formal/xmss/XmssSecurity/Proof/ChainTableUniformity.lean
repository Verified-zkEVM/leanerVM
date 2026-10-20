import XmssSecurity.Proof.ChainHiddenTable
import XmssSecurity.Proof.ChainTrajectoryComposition
import Init.Data.Vector.OfFn

open OracleComp OracleSpec ENNReal

namespace XmssSecurity


theorem fullChainTrajectory_length_eq : chainLength - 1 + 1 = chainLength := by
  decide

def FullChainTrajectory.toDigitTable
    (values : FullChainTrajectory) : Digit → Digest := fun digit =>
  values[digit.val]'(by
    have hdigit := digit.isLt
    omega)

def FullChainTrajectory.ofDigitTable
  (values : Digit → Digest) : FullChainTrajectory :=
  Vector.ofFn fun index => values ⟨index.val, by
    have hindex := index.isLt
    simpa only [fullChainTrajectory_length_eq] using hindex⟩

noncomputable def leafIndexPosition (leafIndex : LeafIndex) : Fin allLeafIndices.length :=
  ⟨allLeafIndices.idxOf leafIndex, List.idxOf_lt_length_iff.mpr (mem_allLeafIndices leafIndex)⟩

@[simp]
theorem allLeafIndices_get_leafIndexPosition (leafIndex : LeafIndex) :
    allLeafIndices.get (leafIndexPosition leafIndex) = leafIndex := by
  exact List.idxOf_get (List.idxOf_lt_length_iff.mpr (mem_allLeafIndices leafIndex))

noncomputable def listOfChainValueTable
    (table : ChainValueIndex → Digest) : List FullChainTrajectory :=
  allLeafIndices.map fun leafIndex =>
    FullChainTrajectory.ofDigitTable fun digit => table (leafIndex, digit)

@[simp]
noncomputable def chainValueTableOfList
    (values : List FullChainTrajectory) : ChainValueIndex → Digest := fun index =>
  if hlength : allLeafIndices.length = values.length then
    (values[(leafIndexPosition index.1).val]'(by
      have hposition := (leafIndexPosition index.1).isLt
      omega)).toDigitTable index.2
  else
    0

@[simp]
theorem listOfChainValueTable_chainValueTableOfList
    (values : List FullChainTrajectory) (hlength : values.length = lifetime) :
    listOfChainValueTable (chainValueTableOfList values) = values := by
  apply List.ext_getElem
  · simp [listOfChainValueTable, allLeafIndices_length, hlength]
  · intro index hleft hright
    simp only [listOfChainValueTable, List.getElem_map]
    apply Vector.ext
    intro digit hdigit
    unfold FullChainTrajectory.ofDigitTable chainValueTableOfList
    rw [Vector.getElem_ofFn]
    split
    · rename_i htableLength
      have hindex : index < allLeafIndices.length := by
        rw [allLeafIndices_length, ← hlength]
        exact hright
      have hposition : (leafIndexPosition allLeafIndices[index]).val = index := by
        exact List.get_idxOf allLeafIndices_nodup ⟨index, hindex⟩
      have hvalue :
          values[(leafIndexPosition allLeafIndices[index]).val] = values[index] := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem,
          ← List.getElem?_eq_getElem, hposition]
      dsimp only
      rw [hvalue]
      unfold FullChainTrajectory.toDigitTable
      rfl
    · rename_i htableLength
      exact (htableLength (allLeafIndices_length.trans hlength.symm)).elim

end XmssSecurity
