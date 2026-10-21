/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsCont

  The buffers' honest words over a total hash (`Whir/OsCont.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsCont
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsLayout

/-!
# The buffers' honest words over a total hash (`Whir/OsCont.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public noncomputable section

variable {Ht : Bytes → Digest} {CM : CompModel}

namespace OsData

variable (Ht) (cfg : OsCfg) (d : OsData)

/-- Level `0`'s chain state. -/
def cv0W : Digest := obsCvW Ht (obsCvW Ht d.cv (d.xs.getD 0 0)) (d.xs.getD 1 0)

/-- The levels. -/
def lvsW : List OsLvP := osLvsListW Ht cfg d.xs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs

/-- Level `l`. -/
def lvW (l : ℕ) : OsLvP := (d.lvsW Ht cfg).getD l default

/-- Level `l`'s chain state after its nonce. -/
def cv3W (l : ℕ) : Digest := osHCv3W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1

/-- Level `l`'s batching challenge. -/
def lamW (l : ℕ) : E := osHLamW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1

/-- Level `l`'s positions with their openings. -/
def qsW (l : ℕ) : List (ℕ × Opening) := (osHQsW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1).zip (d.lvW Ht cfg l).osp

/-- Level `l`'s root. -/
def rtW (l : ℕ) : Digest := ((d.lvW Ht cfg l).roots.getD l default).1

/-- Level `l`'s out-of-domain point. -/
def oodPtW (l : ℕ) : List E := (sqAllW Ht (cfg.lv l).logCols (osHCv12W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).1

/-- Level `l`'s scalar. -/
def betaW (l : ℕ) : E := if l = cfg.yrLevel then d.lamW Ht cfg l else d.lamW Ht cfg l * d.lamW Ht cfg l

/-- The tail's closing challenge. -/
def lastW : E := challengeOf (sqCvW Ht d.cv1t)

/-- The tail's challenges. -/
def tfW : List E := d.chst ++ [d.lastW Ht]

def capsCW : List E :=
  osSegC (4 * cfg.capLen) ((List.range cfg.levels.length).map fun l =>
    (4 * (cfg.lv l).capOff, osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)))

def flagsCW : List E :=
  osSegC cfg.capLen ((List.range cfg.levels.length).map fun l =>
    ((cfg.lv l).capOff, osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)))

def fmsgCW : List E := osHMs cfg cfg.yrLevel d.xs (d.lvW Ht cfg cfg.yrLevel).p

def rootsCW : List E :=
  osSegC (2 * cfg.levels.length) ((List.range cfg.levels.length).map fun l =>
    (2 * l, [(digestScalars (d.rtW Ht cfg l)).1, (digestScalars (d.rtW Ht cfg l)).2]))

/-- The fold challenges: the state's after the levels. -/
def fchCW : List E := (osLvsEndW Ht cfg d.xs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs).2.2.folds

def betasCW : List E := (List.range cfg.levels.length).map (d.betaW Ht cfg)

def qwCW : List E :=
  osSegC (cfg.levels.length * cfg.maxQ) ((List.range cfg.levels.length).map fun l =>
    (l * cfg.maxQ, (List.range (cfg.lv l).queries).map fun i => d.lamW Ht cfg l ^ i))

def qposCW : List E :=
  osSegC cfg.posLen ((List.range cfg.levels.length).map fun l =>
    ((cfg.lv l).posOff, (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
      eOfNat (osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) i)))

def oodzCW : List E :=
  osSegC (cfg.levels.length * 22) ((List.range (cfg.levels.length - 1)).map fun l => ((l + 1) * 22, d.oodPtW Ht cfg l))

def oodCW : List E :=
  osSegC (cfg.levels.length * 4) ((List.range (cfg.levels.length - 1)).map fun l =>
    ((l + 1) * 4, [d.lamW Ht cfg l, osHW cfg l d.xs (d.lvW Ht cfg l).p 2, osHW cfg l d.xs (d.lvW Ht cfg l).p 3,
      osHW cfg l d.xs (d.lvW Ht cfg l).p 4]))

def sqzCW (l : ℕ) : List E :=
  (List.range ((cfg.lv l).squeezes + 1)).flatMap fun j =>
    [(digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).1, (digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).2]

def rewCW (l : ℕ) : List E :=
  (List.range (2 ^ (cfg.lv l).folds)).map fun i =>
    (eqKernel (d.lvW Ht cfg l).H.chs).getD (orwSlot (cfg.lv l).folds (if l = 0 then 1 else 0) i) 0

def tchCW : List E := d.tfW Ht ++ List.replicate (5 - cfg.yrLog) 0

/-- A source's word: the fold challenges' or the tail challenges'. -/
def srcValW (q : ℕ × ℕ) : E := if q.1 = osFch then (d.fchCW Ht cfg).getD q.2 0 else (d.tchCW Ht cfg).getD q.2 0

def entW (i : ℕ) : E :=
  match osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i with
  | some q => d.srcValW Ht cfg q
  | none => 0

def ptCW : List E := (List.range 42).map (d.entW Ht cfg)

def cfW (it : ℕ × (ℕ × ℕ) × ℕ) : E := d.srcValW Ht cfg it.2.1

def baCW : List E :=
  osSegC (cfg.levels.length * 22) ((List.range cfg.levels.length).map fun l =>
    (l * 22, (osBasisCoords cfg.yrLog (OsRun.tch cfg) l (cfg.lv l)).map fun it => 1 + d.cfW Ht cfg it))

def bbCW : List E :=
  osSegC (cfg.levels.length * 22) ((List.range cfg.levels.length).map fun l =>
    (l * 22, (osBasisCoords cfg.yrLog (OsRun.tch cfg) l (cfg.lv l)).map fun it => d.cfW Ht cfg it * eOfNat it.2.2))

/-- Level `l`'s basis row's words. -/
def rowAW (l t : ℕ) : E := (d.baCW Ht cfg).getD (l * 22 + t) 0

def rowBW (l t : ℕ) : E := (d.bbCW Ht cfg).getD (l * 22 + t) 0

/-- Level `l`'s (chainW Ht) after `j` queries. -/
def chainW (l j : ℕ) : E :=
  ∑ x ∈ Finset.range j, d.lamW Ht cfg l ^ x * resProd (d.rowAW Ht cfg l) (d.rowBW Ht cfg l) (cfg.lv l).vals
    ((d.qposCW Ht cfg).getD ((cfg.lv l).posOff + x) 0) (cfg.lv l).logCols

def chvCW (l : ℕ) : List E := (List.range ((cfg.lv l).queries + 1)).map (d.chainW Ht cfg l)

/-- The (innerW Ht) sum before level `l`. -/
def innerW (l : ℕ) : E := ∑ i ∈ Finset.range l, d.betaW Ht cfg i * d.chainW Ht cfg i (cfg.lv i).queries

def ichCW : List E := (List.range (cfg.levels.length + 1)).map (d.innerW Ht cfg)

/-- The finish's values, its buffers' pointers from `b`. -/
def finDW (b : ℕ) : OsFinD where
  yat := multilinearEval (d.fmsgCW Ht cfg) (d.tfW Ht)
  pt := osPtrAt cfg b (11 + 2 * cfg.levels.length + 1)
  ent := d.entW Ht cfg
  ba := osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)
  bb := osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)
  cf := d.cfW Ht cfg
  ich := osPtrAt cfg b (11 + 2 * cfg.levels.length + 4)
  chv := fun l => osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l)
  i0 := d.innerW Ht cfg
  b := d.betaW Ht cfg
  r := fun l => d.chainW Ht cfg l (cfg.lv l).queries
  sc := fun i => d.lamW Ht cfg (i - 1)
  z := fun i t => (d.oodzCW Ht cfg).getD (i * 22 + t) 0
  c := fun i t => d.srcValW Ht cfg (osOodSrc (OsRun.tch cfg)
    (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols (i - 1) - cfg.yrLog)
    (cfg.levels.tail.getD (i - 1) default).foldsOff t)
  t := polyEval d.w1t.quad (d.lastW Ht)
  ichN := d.innerW Ht cfg cfg.levels.length

/-- **The run at the allocator's pointers from `b`**, the cursor `cur`. -/
def runOfW (cur : E) (b : ℕ) : OsRun where
  xs := d.xs
  cv := d.cv
  target := d.target
  root := d.root
  os := d.os
  Hs := d.Hs
  w1t := d.w1t
  chst := d.chst
  cv1t := d.cv1t
  D := d.finDW Ht cfg b
  P := osPtrsOf cfg b
  sqz := fun l => osPtrAt cfg b (11 + 2 * l)
  rew := fun l => osPtrAt cfg b (11 + 2 * l + 1)
  tchv := osPtrAt cfg b (11 + 2 * cfg.levels.length)
  cur := cur

variable {Ht} in
theorem runOf_ptrsC (cur : E) (b : ℕ) : OsPtrsFrom cfg b (d.runOfW Ht cfg cur b) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- **The buffers' honest words**, in allocation order, the decoders' pointers `Q`. -/
def ownQW (Q : List E) : List (List E) :=
  [d.capsCW Ht cfg, d.flagsCW Ht cfg, d.fmsgCW Ht cfg, d.rootsCW Ht cfg, d.fchCW Ht cfg, d.betasCW Ht cfg, d.qwCW Ht cfg, d.qposCW Ht cfg,
    Q, d.oodzCW Ht cfg, d.oodCW Ht cfg] ++
    (List.range cfg.levels.length).flatMap (fun l => [d.sqzCW Ht cfg l, d.rewCW Ht cfg l]) ++
    [d.tchCW Ht cfg, d.ptCW Ht cfg, d.baCW Ht cfg, d.bbCW Ht cfg, d.ichCW Ht cfg] ++
    (List.range cfg.levels.length).map (d.chvCW Ht cfg)

end OsData

end
end LeanVM.Guest.B1
