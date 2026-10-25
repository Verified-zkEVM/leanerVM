/-
  LeanVM.Guest.B1.Main.MainHonest

  `main`'s honest run on a node's statement and witness: its oracle (`hData`) and the words it
  leaves in its buffers (`hOwn`), as the honest prover plans them (`Hints.honestPushes`).
-/

module

public import LeanVM.Guest.B1.Main.MainAtDefs
public import LeanVM.Guest.B1.Main.Plan
public import LeanVM.Guest.Hints

/-!
# `main`'s honest run

For a statement `s` held by a witness `w` under the seed `seed`:

* the counts of `meta` and `da_meta` are the declared lists' lengths, their regions' duplicates
  (`xPlan`, `sPlan`, `dPlan`), the raw signatures, the children, the directly held DA claims;
* `hW c`: the running count before child `c`, the raw claims first, then each child's claims
  (its leanXMSS, leanSPHINCS, DA claims);
* the coverage table's word at each slot is `g` to the global index of the claim that takes it
  (`hMarkX`, `hMarkS`, `hMarkD`): the claims are numbered the raw leanXMSS ones, the raw
  leanSPHINCS ones, the direct DA one, then child by child;
* the tables hold the declared claims then the duplicates (`claimCells`, the DA claims' cells),
  the children's buffers their statements' digests, fresh claims and deferred claims.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct claimCells)

@[expose] public section

variable (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-! ## Counts -/

/-- The raw claims, held by witnesses. -/
def hRawX : List (XmssClaim × LeanXmss.Signature) := direct s.claims.xmss w.xmss
def hRawS : List (SphincsClaim × Sphincs.Signature) := direct s.claims.sphincs w.sphincs
def hRawD : List (DaClaim × Da.Witness) := direct s.claims.da w.da

/-- Child `c`'s claims' counts. -/
def hEx (c : ℕ) : ℕ := (w.children.map (·.statement.claims.xmss.length)).getD c 0
def hEs (c : ℕ) : ℕ := (w.children.map (·.statement.claims.sphincs.length)).getD c 0
def hEd (c : ℕ) : ℕ := (w.children.map (·.statement.claims.da.length)).getD c 0

/-- **The running count before child `c`.** -/
def hW : ℕ → ℕ
  | 0 => (hRawX s w).length + (hRawS s w).length + (hRawD s w).length
  | c + 1 => hW c + (hEx w c + hEs w c + hEd w c)

/-! ## Marks -/

/-- The child and the index within it of claim `k` of the children's claims, child by child. -/
def segOf : List ℕ → ℕ → ℕ × ℕ
  | [], k => (0, k)
  | l :: ls, k => if k < l then (0, k) else ((segOf ls (k - l)).1 + 1, (segOf ls (k - l)).2)

/-- The global index of the leanXMSS region's taker `k` (raw first, then the children's). -/
def hMarkX (k : ℕ) : ℕ :=
  if k < (hRawX s w).length then k
  else let p := segOf (w.children.map (·.statement.claims.xmss.length)) (k - (hRawX s w).length)
    hW s w p.1 + p.2

/-- The leanSPHINCS region's. -/
def hMarkS (k : ℕ) : ℕ :=
  if k < (hRawS s w).length then (hRawX s w).length + k
  else let p := segOf (w.children.map (·.statement.claims.sphincs.length)) (k - (hRawS s w).length)
    hW s w p.1 + hEx w p.1 + p.2

/-- The DA region's. -/
def hMarkD (k : ℕ) : ℕ :=
  if k < (hRawD s w).length then (hRawX s w).length + (hRawS s w).length + k
  else let p := segOf (w.children.map (·.statement.claims.da.length)) (k - (hRawD s w).length)
    hW s w p.1 + hEx w p.1 + hEs w p.1 + p.2

/-- **The coverage table's words**: each slot's taker's mark, region by region. -/
def hCover : List E :=
  ((List.range (s.claims.xmss ++ (xPlan s w).dups).length).map fun t =>
      gen ^ hMarkX s w ((slotsOf (xPlan s w)).idxOf t)) ++
    ((List.range (s.claims.sphincs ++ (sPlan s w).dups).length).map fun t =>
      gen ^ hMarkS s w ((slotsOf (sPlan s w)).idxOf t)) ++
    ((List.range (s.claims.da ++ (dPlan s w).dups).length).map fun t =>
      gen ^ hMarkD s w ((slotsOf (dPlan s w)).idxOf t))

/-! ## The oracle and the buffers -/

/-- A DA claim's four cells: its root's, then its membership vector digest's. -/
def daCells (c : DaClaim) : List E :=
  B1.Digest.digestCells c.daRoot ++ B1.Digest.digestCells c.membershipVectorDigest

/-- **`main`'s honest oracle** (besides pointers). -/
def hData : MainData where
  nlx := s.claims.xmss.length
  nxd := (xPlan s w).dups.length
  nrx := (hRawX s w).length
  nls := s.claims.sphincs.length
  nsd := (sPlan s w).dups.length
  nrs := (hRawS s w).length
  nc := w.children.length
  nd := (hRawD s w).length
  nda := s.claims.da.length
  ndd := (dPlan s w).dups.length
  seed := seed
  dad := daListDigest s.claims.da
  xd := xmssListDigest s.claims.xmss
  sd := sphincsListDigest s.claims.sphincs
  sdg := statementDigest seed s
  daR := ((hRawD s w).map fun p => daCells p.1).headD [0, 0, 0, 0]
  leaf := s.defer.bytecodeValue

/-- **`main`'s honest buffers' words**, in allocation order. -/
def hOwn : List (List E) :=
  [(s.claims.da ++ (dPlan s w).dups).flatMap daCells,
    (s.claims.xmss ++ (xPlan s w).dups).flatMap (fun c => claimCells c.1.root c.1.parameter c.2),
    (s.claims.sphincs ++ (sPlan s w).dups).flatMap (fun c => claimCells c.1.root c.1.parameter c.2),
    B1.Digest.digestCells (signersDigest s.claims.xmss s.claims.sphincs),
    hCover s w,
    (List.range 256).map fun v => word v 0 0,
    w.children.flatMap (fun c => B1.Digest.digestCells (statementDigest seed c.statement)),
    w.children.flatMap (fun c => fixedCells c.fresh),
    w.children.flatMap (fun c => c.statement.defer.cells),
    (List.range (w.children.length + 1)).map (fun c => gen ^ hW s w c),
    s.defer.cells]

end
end LeanVM.Guest.B1.Main
