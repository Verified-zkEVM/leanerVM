import LeanVM.Guest.B1.Main.CoverUnique

/-!
# Tests: the honest coverage table's marks are distinct, its axioms

The writers' numbers of `main`'s three regions are the numbers below the coverage table's size,
each once (`numsOf_perm`, `numsOf_nodup`), so `gX`, `gS` and `gD` are injective on their writers
with disjoint ranges, and the honest coverage table, over a hash too, has no repeated value
(`honestCov_nodup`, `honestCovC_nodup`). They rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.Main.covOf_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.covOf_perm

/-- info: 'LeanVM.Guest.B1.Main.plan_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.plan_slots

/-- info: 'LeanVM.Guest.B1.Main.numsOf_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.numsOf_cover

/-- info: 'LeanVM.Guest.B1.Main.numsOf_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.numsOf_length

/-- info: 'LeanVM.Guest.B1.Main.numsOf_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.numsOf_perm

/-- info: 'LeanVM.Guest.B1.Main.numsOf_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.numsOf_nodup

/-- info: 'LeanVM.Guest.B1.Main.numsOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.numsOf_lt

/-- info: 'LeanVM.Guest.B1.Main.gX_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gX_injOn

/-- info: 'LeanVM.Guest.B1.Main.gS_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gS_injOn

/-- info: 'LeanVM.Guest.B1.Main.gD_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gD_injOn

/-- info: 'LeanVM.Guest.B1.Main.gX_ne_gS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gX_ne_gS

/-- info: 'LeanVM.Guest.B1.Main.gX_ne_gD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gX_ne_gD

/-- info: 'LeanVM.Guest.B1.Main.gS_ne_gD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.gS_ne_gD

/-- info: 'LeanVM.Guest.B1.Main.honestCov_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestCov_perm

/-- info: 'LeanVM.Guest.B1.Main.honestCov_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestCov_nodup

/-- info: 'LeanVM.Guest.B1.Main.honestWordsC_cov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestWordsC_cov

/-- info: 'LeanVM.Guest.B1.Main.honestCovC_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestCovC_nodup

/-- info: 'LeanVM.Guest.B1.Main.honestWordsC_cov_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.honestWordsC_cov_length
