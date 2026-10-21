/-
  LeanVM.Guest.B1.Main.HonestWordsC

  `main`'s words in an honest run over a total hash `Ht`, from a witness of the node relation:
  the digests over `Ht` (`honestWordsC`).
-/

module

public import LeanVM.Guest.B1.Main.HonestWords
public import LeanVM.Guest.B1.Main.MainAtC

/-!
# `main`'s honest words over a hash

`HonestWords.lean`'s `honestWords` with every digest over the total hash `Ht`: the list digests,
the signer set's, the DA list's and the statements' (`…With` at `Id`, `Ht`). Every other word is
`honestWords`'s: the counts, the regions' slots, the tables, the marks, the running counts, the
deferred cells. `StmtAns Ha Ht seed s`: a statement's digests over `Ht` answered by `Ha`, which an
answered statement digest gives (`stmtAns_of`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)

@[expose] public section

section Node

variable (Ht : List UInt8 → Digest) (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-- The leanXMSS list's digest over `Ht`. -/
abbrev xmssListDigestH (claims : List XmssClaim) : Digest :=
  Id.run (xmssListDigestWith (m := Id) Ht claims)

/-- The leanSPHINCS list's digest over `Ht`. -/
abbrev sphincsListDigestH (claims : List SphincsClaim) : Digest :=
  Id.run (sphincsListDigestWith (m := Id) Ht claims)

/-- The signer set's digest over `Ht`. -/
abbrev signersDigestH (xmss : List XmssClaim) (sphincs : List SphincsClaim) : Digest :=
  Id.run (signersDigestWith (m := Id) Ht xmss sphincs)

/-- The DA list's digest over `Ht`. -/
abbrev daListDigestH (claims : List DaClaim) : Digest :=
  Id.run (daListDigestWith (m := Id) Ht claims)

/-- A statement's digest over `Ht`. -/
abbrev statementDigestH (seed : Digest) (s : NodeStatement) : Digest :=
  Id.run (statementDigestWith (m := Id) Ht seed s)

/-- **A child's iteration in an honest run over `Ht`**, its first writer's number `b`
(`childWordsOf`). -/
def childWordsOfC (c : Child) (b : ℕ) : ChildWords :=
  ⟨gen ^ b, cnx c, cns c, c.statement.claims.da,
    digestScalars (xmssListDigestH Ht c.statement.claims.xmss),
    digestScalars (sphincsListDigestH Ht c.statement.claims.sphincs),
    signersDigestH Ht c.statement.claims.xmss c.statement.claims.sphincs, c.statement.defer.cells,
    statementDigestH Ht seed c.statement⟩

/-- **`main`'s words in an honest run over `Ht`** (`honestWords`). -/
noncomputable def honestWordsC : MainWords where
  dx := s.claims.xmss.length
  ux := (planX s w).2.length
  rx := hrx s w
  ds := s.claims.sphincs.length
  us := (planS s w).2.length
  rs := hrs s w
  nc := w.children.length
  rd := hrd s w
  da := s.claims.da.length
  ud := (planD s w).2.length
  drows := ((direct s.claims.da w.da).map fun p => p.2.rows.length).sum
  seed := seed
  daTab := (s.claims.da ++ (planD s w).2).flatMap daCellsOf
  xTab := (s.claims.xmss ++ (planX s w).2).flatMap xCellsOf
  sTab := (s.claims.sphincs ++ (planS s w).2).flatMap sCellsOf
  cov := covOf (planX s w).1 (gX s w) (s.claims.xmss.length + (planX s w).2.length) ++
    covOf (planS s w).1 (gS s w) (s.claims.sphincs.length + (planS s w).2.length) ++
    covOf (planD s w).1 (gD s w) (s.claims.da.length + (planD s w).2.length)
  cpiTab := w.children.flatMap fun c =>
    [(digestScalars (statementDigestH Ht seed c.statement)).1,
      (digestScalars (statementDigestH Ht seed c.statement)).2]
  frTab := w.children.flatMap fun c => fixedCells c.fresh
  carTab := w.children.flatMap fun c => c.statement.defer.cells
  wTab := (List.range (w.children.length + 1)).map fun c => gen ^ hbase s w c
  dTab := s.defer.cells
  daDig := daListDigestH Ht s.claims.da
  xDig := xmssListDigestH Ht s.claims.xmss
  sDig := sphincsListDigestH Ht s.claims.sphincs
  sigDig := signersDigestH Ht s.claims.xmss s.claims.sphincs
  stDig := statementDigestH Ht seed s
  dr := drOf (direct s.claims.da w.da)
  lbv := s.defer.bytecodeValue
  lmA := s.defer.matrixA
  lmB := s.defer.matrixB
  child := fun c => if h : c < w.children.length then childWordsOfC Ht seed w.children[c] (hbase s w c)
    else childWordsOfC Ht seed ⟨⟨⟨[], [], []⟩, ⟨[], 0, [], 0, 0⟩⟩, ⟨[], 0, 0, 0, [], [], [], 0⟩, ⟨[], []⟩⟩ 0
  slX := fun c => (planX s w).1.getD c 0
  slS := fun c => (planS s w).1.getD c 0

end Node

/-! ## A statement's digests answered -/

/-- **A statement's digests are answered by `Ha`** at their values over `Ht`: its two claim lists',
its signer set's, its DA list's and its own (from the seed `seed`). -/
structure StmtAns (Ha : List UInt8 → Option Digest) (Ht : List UInt8 → Digest) (seed : Digest)
    (s : NodeStatement) : Prop where
  xl : xmssListDigestWith Ha s.claims.xmss = some (xmssListDigestH Ht s.claims.xmss)
  sl : sphincsListDigestWith Ha s.claims.sphincs = some (sphincsListDigestH Ht s.claims.sphincs)
  sg : Ha (digestBytes (xmssListDigestH Ht s.claims.xmss) ++
    digestBytes (sphincsListDigestH Ht s.claims.sphincs)) =
      some (signersDigestH Ht s.claims.xmss s.claims.sphincs)
  dl : daListDigestWith Ha s.claims.da = some (daListDigestH Ht s.claims.da)
  st : Digest.stmtDigestOfWith Ha seed (signersDigestH Ht s.claims.xmss s.claims.sphincs)
    (daListDigestH Ht s.claims.da) s.defer.cells = some (statementDigestH Ht seed s)

/-- **An answered statement digest is answered step by step**, at the values over `Ht`. -/
theorem stmtAns_of {Ha : List UInt8 → Option Digest} {Ht : List UInt8 → Digest}
    (hag : ∀ x d, Ha x = some d → d = Ht x) {seed pi : Digest} {s : NodeStatement}
    (h : statementDigestWith Ha seed s = some pi) :
    StmtAns Ha Ht seed s ∧ pi = statementDigestH Ht seed s := by
  rw [Digest.statementDigestWith_eq] at h
  simp only [signersDigestWith, xmssListDigestWith, sphincsListDigestWith, daListDigestWith,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sd, ⟨x, hx, ⟨y, hy, hsd⟩⟩, dd, hdd, hpi⟩ := h
  obtain rfl := hag _ _ hx
  obtain rfl := hag _ _ hy
  obtain rfl := hag _ _ hsd
  obtain rfl := hag _ _ hdd
  obtain rfl := hag _ _ hpi
  exact ⟨⟨hx, hy, hsd, hdd, hpi⟩, rfl⟩

end
end LeanVM.Guest.B1.Main
