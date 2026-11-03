/-
  LeanVM.Prover.Public

  The executable public-input phase (`pubFast`, `Statement/Prover/Prove.lean`) makes the moves of the
  specification's `hPub`, to the same claims.
-/

module

public import Statement.Prover.Prove
public import LeanVM.Prover.BusLeaves
public import LeanVM.Prover.Corr
public import LeanVM.Protocol.EndToEnd.Complete.Public

/-!
# The public-input phase

`corr_pubFast`: from the columns as arrays (`ColsOk`), the public-input phase reading two cells
per memory limb (`pubFast`) makes the moves of `hPub` (it samples `r` and sends nothing) and
returns the same claims: a limb's value on its line is `(1 + r)·m[0] + r·m[1]` (`memLine_eq`),
the verifier's `multilinearEval` of the two cells at `[r]`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol (Column)

@[expose] public section

/-- A memory limb's line, from the arrays. -/
theorem line_memCol {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cols : Array (Array K)} (hcols : ColsOk prog s q cols) (i : Fin 4) (r : E) :
    multilinearEval [ofK ((cols.getD (i : ℕ) #[]).getD 0 0),
      ofK ((cols.getD (i : ℕ) #[]).getD 1 0)] [r] = memLine prog s q i r := by
  rw [memLine_eq, cols_memCol hcols,
    getD_toArray_vec ((inst prog s).column q (memCol i)).values 0 (Nat.two_pow_pos _) 0,
    getD_toArray_vec ((inst prog s).column q (memCol i)).values 1
      (Nat.one_lt_two_pow s.logMem_pos.ne') 0]
  simp only [multilinearEval, List.foldl_cons, List.foldl_nil, foldPairs, List.headD_cons]
  ring

/-- **The public-input phase makes the moves of `hPub`**, to the same claims. -/
theorem corr_pubFast {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cols : Array (Array K)} (hcols : ColsOk prog s q cols) :
    Corr (· = ·) (pubFast (verifierLayout prog s) cols) (hPub prog s q) := by
  unfold pubFast hPub
  refine Corr.bind_same _ fun r ↦ ?_
  have h0 : multilinearEval [ofK ((cols.getD memory0 #[]).getD 0 0),
      ofK ((cols.getD memory0 #[]).getD 1 0)] [r] = memLine prog s q 0 r := line_memCol hcols 0 r
  have h1 : multilinearEval [ofK ((cols.getD memory1 #[]).getD 0 0),
      ofK ((cols.getD memory1 #[]).getD 1 0)] [r] = memLine prog s q 1 r := line_memCol hcols 1 r
  have h2 : multilinearEval [ofK ((cols.getD memory2 #[]).getD 0 0),
      ofK ((cols.getD memory2 #[]).getD 1 0)] [r] = memLine prog s q 2 r := line_memCol hcols 2 r
  show _ = _
  simp only [List.map_cons, List.map_nil]
  rw [h0, h1, h2]
  rfl

end
end LeanVM.Prover
