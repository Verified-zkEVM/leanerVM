/-
  LeanVM.Guest.B1.Main.MainAtDefs

  `main` placed at a frame pointer: its buffers as the bump allocator places them, its oracle at
  those positions, and its callees as `Kid`s.
-/

module

public import LeanVM.Guest.B1.Main.MainWalkChk
public import LeanVM.Guest.B1.Main.MainCore
public import LeanVM.Guest.B1.Main.ExpTablesAt

/-!
# `main`, placed: the definitions

`MainData`: what `main`'s oracle supplies besides pointers. At `fp`, `main` allocates from
`b0 = fp + fs "main"` the DA table, the two claim tables, the signer set's digest, the coverage
table, the byte table, the children's digests, fresh and carried claims, the running counts and
the deferred claim (`mSizes`); its first callee, `exponent_tables`, sits after them, its tables
after its frame. `MainData.toIn` is the oracle with those pointers. `mKids`: `main`'s other callees
in call order, each reading `main`'s words `Lin`, the conditional blocks' only when they run.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (Kid Returns bufL)

@[expose] public section

/-- **What `main`'s oracle supplies besides pointers.** -/
structure MainData where
  nlx : ℕ
  nxd : ℕ
  nrx : ℕ
  nls : ℕ
  nsd : ℕ
  nrs : ℕ
  nc : ℕ
  nd : ℕ
  nda : ℕ
  ndd : ℕ
  seed : Digest
  dad : Digest
  xd : Digest
  sd : Digest
  sdg : Digest
  daR : List E
  leaf : E

variable (d : MainData)

/-- The DA region's, the leanXMSS region's and the leanSPHINCS region's slots. -/
def MainData.S : ℕ := d.nda + d.ndd
def MainData.X : ℕ := d.nlx + d.nxd
def MainData.Y : ℕ := d.nls + d.nsd
def MainData.T : ℕ := d.X + d.Y + d.S

/-- `main`'s `HeapBuf` sizes, in allocation order. -/
def mSizes : List ℕ :=
  [4 * d.S, 4 * d.X, 4 * d.Y, 2, d.T, 256, 2 * d.nc, 24 * d.nc, 24 * d.nc, d.nc + 1, 24]

/-- The buffers' first words from `b0`. -/
def mPos (b0 : ℕ) : List ℕ := Memory.bases b0 (mSizes d)

/-- `main`'s first callee's frame. -/
def mK0 (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "main" + (mSizes d).sum

/-- **`main`'s oracle at `fp`.** -/
def MainData.toIn (fs : String → ℕ) (fp : ℕ) : MainIn :=
  let p := mPos d (fp + fs "main")
  let e := etB fs (mK0 d fs fp)
  { nlx := d.nlx, nxd := d.nxd, nrx := d.nrx, nls := d.nls, nsd := d.nsd, nrs := d.nrs, nc := d.nc,
    nd := d.nd, nda := d.nda, ndd := d.ndd, seed := d.seed, et1 := gen ^ e, et2 := gen ^ (e + 34),
    a69 := gen ^ p.getD 0 0, a77 := gen ^ p.getD 1 0, a80 := gen ^ p.getD 2 0,
    a116 := gen ^ p.getD 3 0, a117 := gen ^ p.getD 4 0, a119 := gen ^ p.getD 5 0,
    a394 := gen ^ p.getD 6 0, a400 := gen ^ p.getD 7 0, a406 := gen ^ p.getD 8 0,
    a409 := gen ^ p.getD 9 0, a417 := gen ^ p.getD 10 0, dad := d.dad, xd := d.xd, sd := d.sd,
    sdg := d.sdg, daR := d.daR, leaf := d.leaf }

/-- `exponent_tables`' tables, placed. -/
def etL (fs : String → ℕ) (fp : ℕ) : B1.Main.Layout :=
  [(etB fs (mK0 d fs fp), etTabs.getD 0 []), (etB fs (mK0 d fs fp) + 34, etTabs.getD 1 [])]

/-- **`main`'s callees after `exponent_tables`**, in call order, reading `Lin`. -/
def mKids (m : MainIn) (Lin : B1.Main.Layout) : List Kid :=
  let one : E := 1
  let X := m.nlx + m.nxd
  let Y := m.nls + m.nsd
  let S := m.nda + m.ndd
  [⟨"__loop0", decide (S ≠ 0), [one, gen ^ S, m.a69], Lin, Returns []⟩,
    ⟨"da_list_digest", true, [m.a69, gen ^ m.nda], Lin, Returns (digestCells m.dad)⟩,
    ⟨"claim_list_digest", true, [m.a77, gen ^ m.nlx], Lin, Returns (digestCells m.xd)⟩,
    ⟨"claim_list_digest", true, [m.a80, gen ^ m.nls], Lin, Returns (digestCells m.sd)⟩,
    ⟨"__loop1", decide (m.nxd ≠ 0), [one, gen ^ m.nxd, m.a77, gen ^ m.nlx], Lin, Returns []⟩,
    ⟨"__loop2", decide (m.nsd ≠ 0), [one, gen ^ m.nsd, m.a80, gen ^ m.nls], Lin, Returns []⟩,
    ⟨"__loop3", decide (m.nrx ≠ 0), [one, gen ^ m.nrx, gen ^ X, m.a117, m.a77], Lin, Returns []⟩,
    ⟨"__loop4", decide (m.nrs ≠ 0), [one, gen ^ m.nrs, gen ^ Y, m.a117, gen ^ X, gen ^ m.nrx, m.a80,
      m.a119], Lin, Returns []⟩] ++
  (if m.nd = 1 then
    [⟨"da_verify", true, [m.et2], Lin, Returns m.daR⟩,
      ⟨"cover_da_root", true, [m.a69, m.a117 * gen ^ (X + Y), gen ^ S, gen ^ (m.nrx + m.nrs)], Lin,
        Returns m.daR⟩]
  else []) ++
  [⟨"__loop5", decide (m.nc ≠ 0), [one, gen ^ m.nc, m.a409, m.a77, m.a117, gen ^ X, m.a80, gen ^ Y,
    m.a406, m.a69, m.a117 * gen ^ (X + Y), gen ^ S, (digestScalars m.seed).1,
    (digestScalars m.seed).2, m.a394, m.et1, m.et2, m.a400], Lin, Returns []⟩] ++
  (if m.nc = 0 then [] else
    [⟨"aggregate_claims", true, [gen ^ m.nc, m.a394, m.a400, m.a406, m.a417], Lin, Returns []⟩]) ++
  [⟨"statement_digest", true, [(digestScalars m.seed).1, (digestScalars m.seed).2, m.a116,
    (digestScalars m.dad).1, (digestScalars m.dad).2, m.a417], Lin, Returns (digestCells m.sdg)⟩]

end
end LeanVM.Guest.B1.Main
