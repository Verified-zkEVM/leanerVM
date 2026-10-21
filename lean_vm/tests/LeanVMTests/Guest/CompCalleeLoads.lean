import LeanVM.Guest.B1.Comp.Digest.SmallLoads
import LeanVM.Guest.B1.Comp.Digest.ChildListLoads

/-!
# Tests: the callees of `main` placed by trees loading their reads, their axioms

`statement_digest`, `cover_da_root` and `child_claim_list_digest` complete over a completeness
model in the uniform placed form by trees loading the words their preconditions name
(`CompleteRelBST` at `SdLoadsQ`, `CoverLoadsQ`, `CclLoadsQ`), the windows, tails and loop
iterations of `child_claim_list_digest` by trees loading their blocks, and the leaf, node and loop
lemmas building such trees, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Digest.sd_completeRelBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sd_completeRelBST

/-- info: 'LeanVM.Guest.B1.Digest.cover_completeRelBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cover_completeRelBST

/-- info: 'LeanVM.Guest.B1.Digest.ccld_completeRelBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_completeRelBST

/-- info: 'LeanVM.Guest.B1.Digest.sd_completeRelBS_of_BST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sd_completeRelBS_of_BST

/-- info: 'LeanVM.Guest.B1.Digest.cover_completeRelBS_of_BST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cover_completeRelBS_of_BST

/-- info: 'LeanVM.Guest.B1.Digest.ccld_completeRelBS_of_BST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccld_completeRelBS_of_BST

/-- info: 'LeanVM.Guest.B1.Digest.sd_tree_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.sd_tree_loads

/-- info: 'LeanVM.Guest.B1.Digest.cct_completeAtBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cct_completeAtBST

/-- info: 'LeanVM.Guest.B1.Digest.ccw_completeAtBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ccw_completeAtBST

/-- info: 'LeanVM.Guest.B1.Digest.l87_completeAtBST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l87_completeAtBST

/-- info: 'LeanVM.Guest.B1.Digest.LoadsAll.childLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.LoadsAll.childLoads

/-- info: 'LeanVM.Guest.B1.completeAtS_leafBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_leafBT

/-- info: 'LeanVM.Guest.B1.completeAtS_nodeBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_nodeBT

/-- info: 'LeanVM.Guest.B1.completeAtS_loopBT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.completeAtS_loopBT

/-- info: 'LeanVM.Guest.B1.CompleteRelBST.toBS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteRelBST.toBS

/-- info: 'LeanVM.Guest.B1.CompleteAtBS.toBST_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.CompleteAtBS.toBST_valid

/-- info: 'LeanVM.Guest.B1.LoadsCells.gpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.LoadsCells.gpow
