import LeanVM.Guest.B1.Comp.FsBlocks
import LeanVM.Guest.B1.Comp.FiatShamir
import LeanVM.Guest.B1.Comp.Opening
import LeanVM.Guest.B1.Comp.OpeningOod
import LeanVM.Guest.B1.Comp.Grind
import LeanVM.Guest.B1.Comp.Sumcheck
import LeanVM.Guest.B1.Comp.Whir.Cap
import LeanVM.Guest.B1.Comp.Digest.Statement
import LeanVM.Guest.B1.Comp.Digest.ClaimList
import LeanVM.Guest.B1.Comp.Digest.ChildList
import LeanVM.Guest.B1.Comp.Da.ListDigest
import LeanVM.Guest.B1.Comp.Da.Complete
import LeanVM.Guest.B1.Comp.Sig.Hashing
import LeanVM.Guest.B1.Comp.VerifySub.Seed

/-!
# Tests: the B1 hash sites over a completeness model, their axioms

The backward halves over a `CompModel` of the guest's B1 functions computing a `BLAKE2S`
(`LeanVM.Guest.B1.Comp`), and the deployed completeness lemmas recovered from them at
`CompModel.deployed`, rest on Lean's three standard axioms only.
-/

/-- info: 'LeanVM.Guest.B1.holdsB_fsCompressT_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.holdsB_fsCompressT_comp

/-- info: 'LeanVM.Guest.B1.holdsB_squeezeT_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.holdsB_squeezeT_comp

/-- info: 'LeanVM.Guest.B1.holds_fsCompressT_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.holds_fsCompressT_of_comp

/-- info: 'LeanVM.Guest.B1.holds_squeezeT_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.holds_squeezeT_of_comp

/-- info: 'LeanVM.Guest.B1.sumcheck_round4_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round4_comp

/-- info: 'LeanVM.Guest.B1.sumcheck_round5_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round5_comp

/-- info: 'LeanVM.Guest.B1.opening_fold_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_fold_comp

/-- info: 'LeanVM.Guest.B1.sumcheck_round4_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round4_of_comp

/-- info: 'LeanVM.Guest.B1.sumcheck_round5_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.sumcheck_round5_of_comp

/-- info: 'LeanVM.Guest.B1.opening_fold_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_fold_of_comp

/-- info: 'LeanVM.Guest.B1.opening_final_message_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_comp

/-- info: 'LeanVM.Guest.B1.opening_final_message_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_final_message_of_comp

/-- info: 'LeanVM.Guest.B1.opening_ood_point_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_ood_point_comp

/-- info: 'LeanVM.Guest.B1.opening_ood_point_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_ood_point_completeC

/-- info: 'LeanVM.Guest.B1.opening_ood_point_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.opening_ood_point_of_comp

/-- info: 'LeanVM.Guest.B1.grind_check_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.grind_check_comp

/-- info: 'LeanVM.Guest.B1.grind_check_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.grind_check_of_comp

/-- info: 'LeanVM.Guest.B1.batch_sumcheck_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batch_sumcheck_comp

/-- info: 'LeanVM.Guest.B1.batch_sumcheck_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.batch_sumcheck_of_comp

/-- info: 'LeanVM.Guest.B1.verify_merkle_cap_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_merkle_cap_comp

/-- info: 'LeanVM.Guest.B1.verify_merkle_cap_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_merkle_cap_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.statement_digest_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.statement_digest_comp

/-- info: 'LeanVM.Guest.B1.Digest.statement_digest_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.statement_digest_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.claims_tail_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_tail_compB

/-- info: 'LeanVM.Guest.B1.Digest.claims_window_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_window_compB

/-- info: 'LeanVM.Guest.B1.Digest.claims_tail_of_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_tail_of_compB

/-- info: 'LeanVM.Guest.B1.Digest.claims_window_of_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_window_of_compB

/-- info: 'LeanVM.Guest.B1.Digest.claim_list_digest_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claim_list_digest_comp

/-- info: 'LeanVM.Guest.B1.Digest.claim_list_digest_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claim_list_digest_completeC

/-- info: 'LeanVM.Guest.B1.Digest.claim_list_digest_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claim_list_digest_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.child_claim_list_digest_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_claim_list_digest_comp

/-- info: 'LeanVM.Guest.B1.Digest.child_claim_list_digest_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_claim_list_digest_completeC

/-- info: 'LeanVM.Guest.B1.Digest.child_claim_list_digest_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_claim_list_digest_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_hash_roots_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_hash_roots_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_list_digest_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_list_digest_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_hash_roots_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_hash_roots_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_list_digest_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_list_digest_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_levels_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_levels_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_levels_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_levels_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_cell_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_cell_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_cell_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_cell_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_vector_cell_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_vector_cell_compB

/-- info: 'LeanVM.Guest.B1.Digest.da_vector_dispatch_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_vector_dispatch_compB

/-- info: 'LeanVM.Guest.B1.Digest.da_vector_cell_of_compB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_vector_cell_of_compB

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_column_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_column_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_column_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_column_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_of_factsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_of_factsC

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_of_facts_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_of_facts_of_comp

/-- info: 'LeanVM.Guest.B1.Digest.commitCodewordsWith_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.commitCodewordsWith_inv

/-- info: 'LeanVM.Guest.B1.Digest.vectorDigestWith_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.vectorDigestWith_inv

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_completeC

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_complete_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_complete_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress_final_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_final_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress4_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress4_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress3_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress3_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress_two_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_two_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress_final_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_final_of_comp

/-- info: 'LeanVM.Guest.B1.Sig.compress_two_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Sig.compress_two_of_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.compress_seed_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.compress_seed_comp

/-- info: 'LeanVM.Guest.B1.VerifySub.compress_seed_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.compress_seed_of_comp
