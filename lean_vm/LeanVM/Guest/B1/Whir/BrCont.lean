/-
  LeanVM.Guest.B1.Whir.BrCont

  The honest words of open_stacked's own buffers, from the Spec's honest trace.
-/

module

public import LeanVM.Guest.B1.Whir.BrTail
public import LeanVM.Guest.B1.Whir.BrAt
public import LeanVM.Guest.B1.Whir.InnerEq
public import LeanVM.Guest.B1.Whir.SpecEnd
public import LeanVM.Guest.B1.Whir.CBody

/-!
# The buffers' honest words

`OsTr`: the honest trace (its levels `Ls`, the words after them `xsR`); its last level `Lf`, all
its fold challenges `Fall`, its tail challenges `Tc`, its levels' records `rs` (as the soundness
proof's `OsRec`), its point.

The finish's honest data, as the soundness proof names them (`βof`, `Xof`, `Pof`, `Wof`, `Λof`,
`Zof`, `Yof` of the records): `finD`, `finAcc`, `finPq`, `finW`, `finL`, `finI`.

Each buffer's honest words, a list of its size (`osHeap`'s, the allocation's): the fixed buffers
(`capsC`, `flagsC`, `fmsgC`, `rootsC`, `fchC`, `betasC`, `qwC`, `qposC`, `qbpC` (at the decoders'
frames `bp`), `oodzC`, `oodC`), the tail challenges (`tailC`), the point and one plus it (`ptC`,
`pt1C`), the basis coefficients, scales and inner sums (`bdC`, `lsC`, `ichC`), and each level's
squeeze chain, residual chain and row weights (`sqzC`, `rcC`, `wpC`). A buffer split by levels at
the configuration's offsets (`capOff`, `posOff`) gives each word to its level (`ownerOf`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The honest trace: its levels and the words after them. -/
structure OsTr where
  Ls : List SpLv
  xsR : List E

namespace OsTr

variable (tr : OsTr)

/-- Level `i`. -/
def L (i : ℕ) : SpLv := tr.Ls.getD i default
/-- The last level. -/
def Lf : SpLv := tr.Ls.getLastD default
/-- Every fold challenge. -/
def Fall : List E := tr.Lf.wsEnd.folds
/-- The tail challenges. -/
def Tc : List E := tailChs tr.Lf tr.xsR

end OsTr

/-- A level's record, as the soundness proof names it. -/
def recOf (L : SpLv) : OsRec :=
  ⟨L.lam, L.qs, if L.fin then none else some (oodZ L.F1 L.ra L.rb L.ml), L.ws1.folds.length, L.ml⟩

namespace OsTr

variable (tr : OsTr)

/-- The levels' records. -/
def rs : List OsRec := tr.Ls.map recOf

/-- The terminal point, rotated into witness order. -/
def point (lane : ℕ) : List E := (tr.Fall ++ tr.Tc).drop lane ++ (tr.Fall ++ tr.Tc).take lane

end OsTr

/-! ## The finish's honest data -/

variable (c : OsCfg) (tr : OsTr)

/-- Level `i`'s row. -/
abbrev lvAt (i : ℕ) : OsLv := c.levels.getD i default

/-- Level `i`'s coefficients `d_t`. -/
def finD (i : ℕ) : ℕ → E := dOf (lvAt c i) (Xof tr.rs tr.Fall tr.Tc i)

/-- Level `i`'s query pairs' sum. -/
def finAcc (i : ℕ) : E :=
  ∑ j ∈ Finset.range (2 * ((lvAt c i).queries / 2)),
    Wof tr.rs i j * lvRes (lvAt c i) (finD c tr i) (Pof tr.rs i j)

/-- Level `i`'s last query's position. -/
def finPq (i : ℕ) : E := Pof tr.rs i ((lvAt c i).queries - 1)

/-- Level `i`'s last query's weight. -/
def finW (i : ℕ) : E := Wof tr.rs i ((lvAt c i).queries - 1)

/-- Level `i`'s scale. -/
def finL (i : ℕ) : E :=
  βof c tr.rs i * ∏ t ∈ Finset.range ((lvAt c i).prefixLen + c.yrLog),
    (Xof tr.rs tr.Fall tr.Tc i t * invW (lvAt c i) t)

/-- The inner sum after the levels below `i`. -/
def finI : ℕ → E
  | 0 => 0
  | i + 1 => finI i + finL c tr i * resSum (lvAt c i) (finAcc c tr i) (finW c tr i) (finD c tr i)
      (finPq c tr i)

/-! ## The buffers' words -/

/-- The level owning word `k` of a buffer split at the offsets `off` (the last level whose offset
is at most `k`, level `0` below every offset). -/
def ownerOf (off : ℕ → ℕ) (n k : ℕ) : ℕ := ((List.range n).filter fun i ↦ 1 ≤ i ∧ off i ≤ k).length

/-- `fold_challenges`. -/
def fchC : List E := (List.range c.nFolds).map fun j ↦ tr.Fall.getD j 0

/-- `level_roots`: each level's root's two cells. -/
def rootsC : List E := (List.range (2 * c.levels.length)).map fun k ↦
  if k % 2 = 0 then (digestScalars (tr.L (k / 2)).root).1 else (digestScalars (tr.L (k / 2)).root).2

/-- `level_betas`. -/
def betasC : List E := (List.range c.levels.length).map fun i ↦
  if i = c.yrLevel then (tr.L i).lam else (tr.L i).lam * (tr.L i).lam

/-- `query_weights`: level `i`'s powers of its batching challenge from `i · maxQ`. -/
def qwC : List E := (List.range (c.levels.length * c.maxQ)).map fun k ↦
  if k % c.maxQ < (lvAt c (k / c.maxQ)).queries then (tr.L (k / c.maxQ)).lam ^ (k % c.maxQ) else 0

/-- `ood_z`: from row `i + 1`, the out-of-domain point level `i` samples. -/
def oodzC : List E := (List.range (c.levels.length * ligColsCap)).map fun k ↦
  if 1 ≤ k / ligColsCap then
    (oodZ (tr.L (k / ligColsCap - 1)).F1 (tr.L (k / ligColsCap - 1)).ra
      (tr.L (k / ligColsCap - 1)).rb (tr.L (k / ligColsCap - 1)).ml).getD (k % ligColsCap) 0
  else 0

/-- `ood`: from slot `i + 1`, level `i`'s batching challenge, out-of-domain value and intro. -/
def oodC : List E := (List.range (c.levels.length * oodSlots)).map fun k ↦
  if 1 ≤ k / oodSlots then
    [(tr.L (k / oodSlots - 1)).lam, (tr.L (k / oodSlots - 1)).y, (tr.L (k / oodSlots - 1)).c0,
      (tr.L (k / oodSlots - 1)).c2].getD (k % oodSlots) 0
  else 0

/-- `final_msg`. -/
def fmsgC : List E := (List.range c.yrLen).map fun k ↦ tr.Lf.ms.getD k 0

/-- A level's squeeze challenges' decoded positions, slot `j`. -/
def posAt (i j : ℕ) : E :=
  eOfNat ((eToNat (((tr.L i).F2.squeezeN (tr.L i).nsq).1.getD (j / (192 / (lvAt c i).depth)) 0) >>>
    ((j % (192 / (lvAt c i).depth)) * (lvAt c i).depth)) % 2 ^ (lvAt c i).depth)

/-- `query_positions`: each level's squeezes' decoded positions from its offset. -/
def qposC : List E := (List.range c.posLen).map fun k ↦
  if k - (lvAt c (ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k)).posOff <
      (lvAt c (ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k)).squeezes *
        (192 / (lvAt c (ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k)).depth) then
    posAt c tr (ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k)
      (k - (lvAt c (ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k)).posOff)
  else 0

/-- `query_bit_ptrs`: each level's squeezes' bit runs, squeeze `s` of level `i` decoded at the
frame `bp i s`. -/
def qbpC (bp : ℕ → ℕ → E) : List E := (List.range c.posLen).map fun k ↦
  let i := ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length k
  let j := k - (lvAt c i).posOff
  let per := 192 / (lvAt c i).depth
  if j < (lvAt c i).squeezes * per then bp i (j / per) * gen ^ ((j % per) * (lvAt c i).depth)
  else 0

/-- A level's query step's openings. -/
def SpLv.batch' (L : SpLv) : List (ℕ × Opening) := L.qs.zip L.os

/-- `merkle_caps`: each level's honest cap cells from `4 · capOff`. -/
noncomputable def capsC : List E := (List.range (4 * c.capLen)).map fun k ↦
  let i := ownerOf (fun i ↦ 4 * (lvAt c i).capOff) c.levels.length k
  if k - 4 * (lvAt c i).capOff < 2 ^ ((lvAt c i).capDepth + 2) then
    capCell (tr.L i).height (SpLv.batch' (tr.L i)) (k - 4 * (lvAt c i).capOff)
  else 0

/-- `merkle_cap_active`: each level's honest cap flags from `capOff`. -/
noncomputable def flagsC : List E := (List.range c.capLen).map fun k ↦
  let i := ownerOf (fun i ↦ (lvAt c i).capOff) c.levels.length k
  if k - (lvAt c i).capOff < 2 ^ (lvAt c i).capDepth then
    capFl (tr.L i).height (SpLv.batch' (tr.L i)) (lvAt c i).capDepth (k - (lvAt c i).capOff)
  else 0

/-- The point buffer: the point zero-padded. -/
def ptC (lane : ℕ) : List E := tr.point lane ++ List.replicate (pointCap - (tr.point lane).length) 0

/-- `point1`: one plus each coordinate, one-padded. -/
def pt1C (lane : ℕ) : List E :=
  (tr.point lane).map (1 + ·) ++ List.replicate (pointCap - (tr.point lane).length) 1

/-- `basis_d`: level `i`'s coefficients from `i · 22`. -/
def bdC : List E := (List.range (c.levels.length * ligColsCap)).map fun k ↦
  finD c tr (k / ligColsCap) (k % ligColsCap)

/-- `level_scales`. -/
def lsC : List E := (List.range c.levels.length).map (finL c tr)

/-- `inner`: the inner sums. -/
def ichC : List E := (List.range (c.levels.length + 1)).map (finI c tr)

/-- Level `i`'s squeeze chain: the capacity after each squeeze. -/
def sqzC (i : ℕ) : List E := (List.range ((c.maxSq + 1) * 5)).map fun k ↦
  if k / 5 ≤ (lvAt c i).squeezes then (((tr.L i).F2.squeezeN (k / 5)).2.cap).getD (k % 5) 0 else 0

/-- Level `i`'s residual chain: the query pairs' partial sums. -/
def rcC (i : ℕ) : List E := (List.range (c.maxQ + 1)).map fun m ↦
  if m ≤ (lvAt c i).queries / 2 then
    ∑ j ∈ Finset.range (2 * m), Wof tr.rs i j * lvRes (lvAt c i) (finD c tr i) (Pof tr.rs i j)
  else 0

/-- Level `i`'s row weights. -/
def wpC (i : ℕ) : List E := (List.range c.maxIl).map fun k ↦
  let f := (lvAt c i).folds
  let rev := if i = 0 then 1 else 0
  if k < 2 ^ rwLo f then (eqKernel ((tr.L i).chs.take (rwLo f))).getD (rwSlot (rwLo f) rev k) 0
  else if k < 2 ^ rwLo f + 2 ^ (f - rwLo f) then
    (eqKernel ((tr.L i).chs.drop (rwLo f))).getD (rwSlot (f - rwLo f) rev (k - 2 ^ rwLo f)) 0
  else 0

/-! ## Reading them -/

theorem readsAt_map_range {rd : Reader} {p : E} {n : ℕ} {f : ℕ → E}
    (h : ReadsAt rd p ((List.range n).map f)) {k : ℕ} (hk : k < n) : LoadHolds rd p k (f k) := by
  have := h k (by simpa using hk)
  simpa using this

end
end LeanVM.Guest.B1.Whir
