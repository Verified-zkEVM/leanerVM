/-
  LeanVM.Guest.B1.VerifySub.C.Own

  `verify_sub`'s own buffers: its sixteen allocations, their sizes, and the words of those the
  honest run fixes by itself.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.Hints

/-!
# The own buffers

`vs_allocs` (by the kernel): `verify_sub`'s sixteen allocations, in order, are `claim_pool`
(`7`, 165 words), `claim_cplen_g` (`8`, 165), `stream` (`27`, 8192), `table_rows` (`28`, 6),
`dims_g` (`129`, 7), `kappa_base` (`141`, 8), `block_kappa` (`149`, 153), `zeta` (`523`, `g^μ`
words: the one dynamic allocation, by the bus depth `522`), `bus_alpha` (`559`, 4), `fp_w`
(`640`, 16), `chi` (`848`, 34), `z_vals` (`859`, 78), `slices` (`860`, 64), the ring map's
challenges (`876`, 6), `c_table` (`877`, 64) and `lam_pool` (`1324`, 165). `vsSizes μ`: their
sizes, the bus depth `μ`.

Words fixed by the run alone (`vsStreamW`, `vsDimsW`, `vsKbW`, …): the stream padded to
`childStreamCap` (`Hints.childHints`' `"stream"`), the row counts, `dims_g` (`g^logMem`, then the
tables' heights as `count`, `Hints.childHints`' `"table_logs"`), `kappa_base`, `block_kappa`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The allocations' values, in order. -/
def vsAllocVars : List ℕ := [7, 8, 27, 28, 129, 141, 149, 523, 559, 640, 848, 859, 860, 876, 877, 1324]

/-- **The allocations, by the kernel**: their values and sizes (the dynamic one by `522`). -/
theorem vs_allocs : vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz =
    (vsAllocVars.zip [.inl 165, .inl 165, .inl 8192, .inl 6, .inl 7, .inl 8, .inl 153, .inr (.n 522),
      .inl 4, .inl 16, .inl 34, .inl 78, .inl 64, .inl 6, .inl 64, .inl 165]).map
      (fun x ↦ (V.n x.1, x.2)) := by decide +kernel

/-- The own buffers' sizes, the bus depth `μ`. -/
def vsSizes (μ : ℕ) : List ℕ :=
  [165, 165, 8192, 6, 7, 8, 153, μ, 4, 16, 34, 78, 64, 6, 64, 165]

/-- The stream buffer's words: the stream, padded to `childStreamCap` (`Hints.childHints`' `"stream"`). -/
def vsStreamW (stream : List E) : List E :=
  stream ++ List.replicate (Hints.childStreamCap - stream.length) 0

/-- `dims_g`'s words: `g^logMem`, then the tables' heights as `count` (`"table_logs"`). -/
noncomputable def vsDimsW (logMem : ℕ) (heights : List ℕ) : List E :=
  gen ^ logMem :: heights.map Hints.count

/-- `kappa_base`'s words: `1`, `g^logMem`, the heights' powers. -/
noncomputable def vsKbW (logMem : ℕ) (heights : List ℕ) : List E :=
  1 :: gen ^ logMem :: heights.map Hints.count

/-- `block_kappa`'s words. -/
noncomputable def vsBkW (logMem : ℕ) (heights : List ℕ) : List E :=
  Tables.blockKappaWords (gen ^ logMem) (heights.map Hints.count)

end
end LeanVM.Guest.B1.VerifySub
