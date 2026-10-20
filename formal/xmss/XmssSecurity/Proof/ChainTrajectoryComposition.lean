import XmssSecurity.Proof.ChainTrajectoryUniformity

namespace XmssSecurity

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

noncomputable def allLeafIndices : List LeafIndex :=
  Finset.univ.toList

theorem allLeafIndices_nodup : allLeafIndices.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allLeafIndices (leafIndex : LeafIndex) : leafIndex ∈ allLeafIndices := by
  simp [allLeafIndices]

theorem allLeafIndices_length : allLeafIndices.length = lifetime := by
  simp [allLeafIndices, LeafIndex]

attribute [irreducible] allLeafIndices

end XmssSecurity
