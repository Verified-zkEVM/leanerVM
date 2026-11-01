module

public import LeanVM.Guest.Fast.SphincsTablesCheck
public import LeanVM.Guest.Fast.SphincsN
public import LeanVM.Guest.Fast.Wots
public import LeanVM.Guest.Fast.Common
public import LeanVM.Guest.B1.Sig.SphincsSound

/-!
# leanSPHINCS's signature reader, computable

`sphincsSigOf σ` (`B1/Sig/SphincsSound.lean`) reads the signature `verify_sig_lean_sphincs` checks
off its valuation, at cells the template generators compute (`cSt`, `fkAB`, `foAB`, `cwStart` over
a `WotsT`, `kMsg`, `merkleT`) and through classical exponent searches (`logG`). `sphincsSigOfN σ`
reads the same cells off the literal tables of `Fast/SphincsTables.lean` (and the arithmetic of
`Fast/SphincsN.lean`) and searches the exponents through `logGT`; `sphincsSigOfN_eq`: they are
equal.

* `subOpeningN σ b fold p0 p1`: a sub-tree's opening (`subOpening`), its base, its fold's base and
  its two top cells;
* `coordOpeningN σ r`: a coordinate's opening (`coordOpening`) at its positions `r`.

**Off arrays** (`Fast/Common.lean`): `sphincsSigOfA T σ` reads the same cells off the tables `T`
(`SphincsTabs`: the lanes of `g^k`, the forest keys' chain cells, the coordinates' positions, the
codeword's selectors and tables, the path bases), built once by the caller (`sphincsTabs`); the
exponents each opening's closures read are computed once and passed (`subOpeningAt`,
`coordOpeningAt`); `sphincsSigOfA_tabs`: at `sphincsTabs` it is `sphincsSigOfN`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- **A sub-tree's opening** from its base `b`, its fold's base and its two top cells
(`subOpening`): the chain values of the forest key its dispatch takes, the fold's siblings and the
other top cell. -/
def subOpeningN (σ : Val) (b fold p0 p1 : ℕ) : Sphincs.SubOpening :=
  let t := logGT (σ (.n (b + 6))) 256
  let a := logGT (σ (.n b)) 8
  ⟨fun i ↦ sv (σ (.n (b + 12 + offAt fkOff t i.val))),
    fun l ↦ sv (if l.val < 2 then σ (.n (foldPos 35 32 fold a + 16 * l.val))
      else σ (.n (if a / 4 = 0 then p0 else p1)))⟩

/-- **A coordinate's opening** at its positions `r` (`coordOpening`). -/
def coordOpeningN (σ : Val) (r : SCoord) : Sphincs.CoordOpening :=
  let s := logGT (σ (.n r.b)) 16
  ⟨fun j ↦ if j.val = 0 then subOpeningN σ (r.b + 10) r.f0 r.p00 r.p01
      else subOpeningN σ r.s1 r.f1 r.p10 r.p11,
    fun l ↦ sv (if l.val < 3 then σ (.n (foldPos 54 51 r.top s + 17 * l.val))
      else σ (.n (if s / 8 = 0 then r.q0 else r.q1)))⟩

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, read off its valuation
(`sphincsSigOf`). -/
def sphincsSigOfN (σ : Val) : Sphincs.Signature :=
  ⟨sv (σ (.n 3)), fun c ↦ coordOpeningN σ (sCoordTab.getD c.val sCoord0),
    BitVec.ofNat 32 (cellNat (σ (.n 412448))),
    fun i ↦ sv (σ (.n (cwCell 21 sSel sFirst sRest sLast σ i.val))),
    fun l ↦ sv (sibN σ (30 + l.val) (sPath.getD l.val 0))⟩

/-! ## Equal to the original -/

theorem subOpening_eq (σ : Val) (c j : ℕ) (enc : Option V) {b fold p0 p1 : ℕ}
    (hf : (subE c j enc b).2.2 = fold) (h0 : (subFd c j enc b).2.2.2.1 = .n p0)
    (h1 : (subFd c j enc b).2.2.1 = .n p1) :
    subOpening σ c j enc b = subOpeningN σ b fold p0 p1 := by
  have ht := logG_lt (σ (.n (b + 6))) (bound := 256) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at ht
  have hv (i : Sphincs.FChain) : subVal σ c j b i.val =
      σ (.n (b + 12 + offAt fkOff (logGT (σ (.n (b + 6))) 256) i.val)) := by
    have hi : i.val < 6 := i.isLt
    unfold subVal subT
    rw [fkCB_fkAB, fkOff_eq, offAt_map ht hi, logG_eq_logGT _ (by norm_num)]
  have hs (l : Fin Sphincs.subHeight) : subSib σ c j enc b l.val =
      if l.val < 2 then σ (.n (foldPos 35 32 fold (logGT (σ (.n b)) 8) + 16 * l.val))
      else σ (.n (if logGT (σ (.n b)) 8 / 4 = 0 then p0 else p1)) := by
    unfold subSib subA
    rw [logG_eq_logGT _ (by norm_num), flBase_const (flNext_subAdr _),
      foAB_eq (d := 16) flNext_subAdr, hf, h0, h1, ite_sigma (σ := σ)]
    rfl
  simp only [subOpening, subOpeningN, hv, hs]

theorem coordOpening_eq (σ : Val) {c : ℕ} (hc : c < 8) :
    coordOpening σ c (cSt c).1 (cSt c).2.1 (cSt c).2.2 =
      coordOpeningN σ (sCoordTab.getD c sCoord0) := by
  have hok := List.all_eq_true.mp sCoordTab_ok c (List.mem_range.mpr hc)
  generalize sCoordTab.getD c sCoord0 = r at hok
  simp only [coordCheck, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hf0⟩, hp00⟩, hp01⟩, hs1⟩, hf1⟩, hp10⟩, hp11⟩, htop⟩, hq0⟩, hq1⟩ := hok
  rw [hb]
  have hsub (j : Sphincs.SubIdx) : subOpening σ c j.val
      (if j.val = 0 then (cSt c).1 else some (coordS0 c (cSt c).1 (cSt c).2.1 r.b).2.2.1)
      (if j.val = 0 then r.b + 10 else (coordS0 c (cSt c).1 (cSt c).2.1 r.b).2.1) =
      if j.val = 0 then subOpeningN σ (r.b + 10) r.f0 r.p00 r.p01
      else subOpeningN σ r.s1 r.f1 r.p10 r.p11 := by
    by_cases h : j.val = 0
    · simp only [h, ↓reduceIte]
      exact subOpening_eq σ c 0 _ hf0 hp00 hp01
    · simp only [h, ↓reduceIte]
      have hj : j.val = 1 := by omega
      rw [hj, hs1]
      exact subOpening_eq σ c 1 _ hf1 hp10 hp11
  have htop (l : Fin Sphincs.topHeight) : topSib σ c (cSt c).1 (cSt c).2.1 r.b l.val =
      if l.val < 3 then σ (.n (foldPos 54 51 r.top (logGT (σ (.n r.b)) 16) + 17 * l.val))
      else σ (.n (if logGT (σ (.n r.b)) 16 / 8 = 0 then r.q0 else r.q1)) := by
    unfold topSib coordS
    rw [logG_eq_logGT _ (by norm_num), flBase_const (flNext_coordAdr _),
      foAB_eq (d := 17) flNext_coordAdr, htop, hq0, hq1, ite_sigma (σ := σ)]
    rfl
  simp only [coordOpening, coordOpeningN, hsub, htop]

/-- **The readers are equal.** -/
theorem sphincsSigOfN_eq (σ : Val) : sphincsSigOfN σ = sphincsSigOf σ := by
  obtain ⟨hfb, henc, hleaf⟩ := sStatic
  have hc (c : Sphincs.Coord) : coordOpening σ c.val (cSt c.val).1 (cSt c.val).2.1 (cSt c.val).2.2 =
      coordOpeningN σ (sCoordTab.getD c.val sCoord0) := coordOpening_eq σ c.isLt
  have hw (i : Sphincs.ChainIndex) : cwStart sW 21 (sEnc.2.1 + 10) σ i.val =
      .n (cwCell 21 sSel sFirst sRest sLast σ i.val) := by
    rw [henc]
    exact cwStart_eq_cwCell (W := sW) (G := 21) (b := 412513) sSel_eq sTabs (by norm_num) σ
      (by have := i.isLt; simp only [Sphincs.numChains] at this; omega)
  have hp (l : Fin Sphincs.totalHeight) : mSib σ sBit l.val (mBase sNodeOf 0 l.val sLeaf.2.1) =
      sibN σ (30 + l.val) (sPath.getD l.val 0) := by
    have hl : l.val < 26 := l.isLt
    rw [hleaf, sPath_eq, getD_map_range hl]
    rfl
  simp only [sphincsSigOfN, sphincsSigOf, hc, hw, hp, hfb]

/-! ## Off arrays -/

/-- leanSPHINCS's tables, as arrays: the lanes of `g^k` (`gLanes`), the forest keys' chain cells
(`fkOff`), the coordinates' positions (`sCoordTab`), the codeword's selector cells (`sSel`) and
chain starts' tables (`sFirst`, `sRest`, `sLast`), the path bases (`sPath`). -/
structure SphincsTabs where
  lanes : List ℕ
  fkOff : Array (Array ℕ)
  coords : Array SCoord
  sel : Array ℕ
  first : Array (Array ℕ)
  rest : Array (Array ℕ)
  last : Array (Array ℕ)
  path : Array ℕ

/-- **leanSPHINCS's tables**, built from the literals. -/
def sphincsTabs : SphincsTabs :=
  ⟨gLanes, tabA fkOff, sCoordTab.toArray, sSel.toArray, tabA sFirst, tabA sRest, tabA sLast,
    sPath.toArray⟩

/-- A sub-tree's opening, the forest key `t` its dispatch takes and its fold's arm `a` given
(`subOpeningN`). -/
def subOpeningAt (fk : Array (Array ℕ)) (σ : Val) (b fold p0 p1 t a : ℕ) : Sphincs.SubOpening :=
  ⟨fun i ↦ sv (σ (.n (b + 12 + offAtA fk t i.val))),
    fun l ↦ sv (if l.val < 2 then σ (.n (foldPos 35 32 fold a + 16 * l.val))
      else σ (.n (if a / 4 = 0 then p0 else p1)))⟩

/-- **A sub-tree's opening, off the tables** (`subOpeningN`): its key and arm read once. -/
def subOpeningA (lanes : List ℕ) (fk : Array (Array ℕ)) (σ : Val) (b fold p0 p1 : ℕ) :
    Sphincs.SubOpening :=
  subOpeningAt fk σ b fold p0 p1 (logGTWith lanes (σ (.n (b + 6))) 256)
    (logGTWith lanes (σ (.n b)) 8)

/-- A coordinate's opening at its positions `r`, its top fold's arm `s` given
(`coordOpeningN`). -/
def coordOpeningAt (lanes : List ℕ) (fk : Array (Array ℕ)) (σ : Val) (r : SCoord) (s : ℕ) :
    Sphincs.CoordOpening :=
  ⟨fun j ↦ if j.val = 0 then subOpeningA lanes fk σ (r.b + 10) r.f0 r.p00 r.p01
      else subOpeningA lanes fk σ r.s1 r.f1 r.p10 r.p11,
    fun l ↦ sv (if l.val < 3 then σ (.n (foldPos 54 51 r.top s + 17 * l.val))
      else σ (.n (if s / 8 = 0 then r.q0 else r.q1)))⟩

/-- **A coordinate's opening, off the tables** (`coordOpeningN`): its arm read once. -/
def coordOpeningA (lanes : List ℕ) (fk : Array (Array ℕ)) (σ : Val) (r : SCoord) :
    Sphincs.CoordOpening :=
  coordOpeningAt lanes fk σ r (logGTWith lanes (σ (.n r.b)) 16)

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks, off the tables `T`**
(`sphincsSigOfN`). -/
def sphincsSigOfA (T : SphincsTabs) (σ : Val) : Sphincs.Signature :=
  ⟨sv (σ (.n 3)), fun c ↦ coordOpeningA T.lanes T.fkOff σ (T.coords.getD c.val sCoord0),
    BitVec.ofNat 32 (cellNat (σ (.n 412448))),
    fun i ↦ sv (σ (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last σ i.val))),
    fun l ↦ sv (sibN σ (30 + l.val) (T.path.getD l.val 0))⟩

theorem subOpeningA_tabs (σ : Val) (b fold p0 p1 : ℕ) :
    subOpeningA gLanes (tabA fkOff) σ b fold p0 p1 = subOpeningN σ b fold p0 p1 := by
  simp only [subOpeningA, subOpeningAt, subOpeningN, logGTWith_gLanes, offAtA_tabA]
  rfl

theorem coordOpeningA_tabs (σ : Val) (r : SCoord) :
    coordOpeningA gLanes (tabA fkOff) σ r = coordOpeningN σ r := by
  simp only [coordOpeningA, coordOpeningAt, coordOpeningN, logGTWith_gLanes, subOpeningA_tabs]
  rfl

/-- **Off the tables built, the reader is `sphincsSigOfN`.** -/
theorem sphincsSigOfA_tabs (σ : Val) : sphincsSigOfA sphincsTabs σ = sphincsSigOfN σ := by
  simp only [sphincsSigOfA, sphincsSigOfN, sphincsTabs, coordOpeningA_tabs, cwCellA_eq,
    getD_toArray]

end
end LeanVM.Guest.Fast
