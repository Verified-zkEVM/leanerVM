import LeanerVM.Protocol.VerifierQueries
import LeanerVMTests.Protocol.RustProof

/-!
# The verifier's queries on the Rust proof

The executable verifier on the fixture's Rust proof, every hash counted, accepts after 3936
hashes: the chain walk's 1004 and the openings' 2932. The bound at the fixture's sizes and rate,
`queryCountAt`, is 6162: the chain's count exactly and, for the openings, a query per stored row
and per row and level of the tree, where the pruned openings share their upper nodes.
-/

namespace LeanerVMTests.Protocol.VerifierQueries

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Verify
open LeanerVMTests.Protocol.RustProof

/-- The fixture's verdict and the number of hashes the verifier asks. -/
def queriesAsked : Bool × ℕ :=
  (verifyWith (m := StateM ℕ) (fun t ↦ do modify (· + 1); pure (blake2sBytes t)) fx.prog fx.input
    fx.proof).run 0

#guard queriesAsked == (true, 3936)
#guard queriesAsked.2 ≤ VerifierQueries.queryCountAt fx.prog fx.input sizes.1 sizes.2

end LeanerVMTests.Protocol.VerifierQueries
