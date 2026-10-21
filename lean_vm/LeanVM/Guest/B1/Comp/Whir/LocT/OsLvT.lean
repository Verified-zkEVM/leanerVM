/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsLvT

  A level's callees of `open_stacked`, bounded, over a completeness model, the queries' trees decoding
  to the level's openings (`Loc/OsKidsLvB.lean` with predicates).
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsKidsT
public import LeanVM.Guest.B1.Comp.Whir.LocT.OqQueriesT
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsLvB
public import LeanVM.Guest.B1.Comp.Whir.LocT.CapSibs
public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsStreamL

/-!
# A level's callees with predicates

`osCBBCT`: `osCBBC` by trees satisfying `QB f args`. `OsLvQ`, `osQB`: level `l`'s `opening_queries`
tree decodes (`OqQueriesQ`) to the level's openings, its leaves, positions and siblings below the cap.
`lvCallQBCT`, `lvsCallHBCT`: `lvCallQBC`, `lvsCallHBC` with the level's later callees in
`osCBBCT … (osQB … l)`, given the queries' tree forms (`OsKidsAtBCT`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Guest.Located (oqLookup)
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- `osCBBC` by trees satisfying `QB f args`. -/
def osCBBCT (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (bd : String → ℕ) (Lk : Main.Layout)
    (W S : ℕ → Main.Layout) (QB : String → List E → ℕ → Reader → Tree → Prop) : CallRel :=
  fun f a r => ∀ p, CompleteAtBST CM.sem fs cert κ f (Lk ++ W p ++ S p) a (Returns r) (bd f) (QB f a)

/-- **Level `l`'s `opening_queries` tree decodes to the level's openings**, at the specialization
`oqLookup` gives its name. -/
def OsLvQ (Ht : Bytes → Digest) (cfg : OsCfg) (d : OsData) (l : ℕ) (a : List E) (t : Tree) : Prop :=
  match oqLookup (cfg.lv l).queriesFn with
  | some (loop, base, I, blocks, pd, cd) => OqQueriesQ base I blocks pd cd loop (cfg.lv l).queries (a.getD 0 0)
      (fun j => ((d.lvW Ht cfg l).osp.getD j ⟨[], []⟩).leaf)
      (fun j => (osHQsW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1).getD j 0)
      (fun j => ((d.lvW Ht cfg l).osp.getD j ⟨[], []⟩).path.take ((cfg.lv l).depth - (cfg.lv l).capDepth)) t
  | none => True

/-- Level `l`'s queries' words at the buffers from `b`. -/
def osQArgs (cfg : OsCfg) (b l : ℕ) : List E :=
  [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff,
    (osPtrsOf cfg b).qw * gen ^ (l * cfg.maxQ), (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff,
    osPtrAt cfg b (11 + 2 * l + 1), osGw (cfg.lv l).queries]

/-- Level `l`'s cap's words at the buffers from `b`. -/
def osCapArgs (cfg : OsCfg) (b l : ℕ) : List E :=
  [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff]

/-- **The tree loads the cells of the children of the cap's root and of its flagged nodes** (at the
cap `a[0]`, the flags `a[1]`, on the memory `rd`). -/
def CapLoadsQ (cd : ℕ) (rd : Reader) (a : List E) (t : Tree) : Prop :=
  ∀ p, 1 ≤ p → p < 2 ^ cd → (p = 1 ∨ memAt rd (a.getD 1 0) p ≠ 0) → ∀ i < 4,
    ((a.getD 0 0).limb 0 * Parameters.gpow (4 * p + i), memAt rd (a.getD 0 0) (4 * p + i)) ∈ t.loadEqns coreProgram

/-- Level `l`'s later callees' predicate: the queries (six words) at their words, decoding to the
level's openings; the cap at its words, loading its flagged nodes' children. -/
def osQB (Ht : Bytes → Digest) (cfg : OsCfg) (d : OsData) (b l : ℕ) :
    String → List E → ℕ → Reader → Tree → Prop :=
  fun f a _ rd t => (a.length = 6 → a = osQArgs cfg b l ∧ OsLvQ Ht cfg d l a t) ∧
    (f = (cfg.lv l).verifyCap → a.length = 2 → a = osCapArgs cfg b l ∧ CapLoadsQ (cfg.lv l).capDepth rd a t)

/-- The levels' caps: depths `4 .. 8`, `verify_merkle_cap` at its depth, distinct from the row
weights. -/
def OsCapNames (cfg : OsCfg) : Prop :=
  ∀ l < cfg.levels.length, 4 ≤ (cfg.lv l).capDepth ∧ (cfg.lv l).capDepth ≤ 8 ∧
    (cfg.lv l).verifyCap = vmcName (cfg.lv l).capDepth ∧ (cfg.lv l).rowWeights ≠ (cfg.lv l).verifyCap

/-- **The levels' `opening_queries`, placed, bounded, by trees decoding to their openings.** -/
def OsKidsAtBCT (CM : CompModel) (Ht : Bytes → Digest) (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (cfg : OsCfg) (bd : String → ℕ) : Prop :=
  ∀ l < cfg.levels.length, ∃ B, OqCompleteAtBCT CM Ht fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds)
    (cfg.lv l).depth (cfg.lv l).capDepth (cfg.lv l).queriesFn B ∧ B (cfg.lv l).queries ≤ bd (cfg.lv l).queriesFn

theorem OqQueriesQ.congr {base I blocks pd cd : ℕ} {loop : String} {n : ℕ} {cap : E} {leaf leaf' : ℕ → List K}
    {pos pos' : ℕ → ℕ} {sibs sibs' : ℕ → List Digest} (hl : ∀ j < n, leaf j = leaf' j) (hp : ∀ j < n, pos j = pos' j)
    (hs : ∀ j < n, sibs j = sibs' j) {t : Tree} (h : OqQueriesQ base I blocks pd cd loop n cap leaf pos sibs t) :
    OqQueriesQ base I blocks pd cd loop n cap leaf' pos' sibs' t := fun rd V σ' h1 h2 h3 => by
  rw [h rd V σ' h1 h2 h3]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  simp only [oqHonest, hl j hj', hp j hj', hs j hj']

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- `os_completeAtB_of_nonemptyC` with predicates. -/
theorem os_completeAtBT_of_nonempty {f : String} {Lin : Main.Layout} {args rets : List E} {B : ℕ}
    {Q : ℕ → Reader → Tree → Prop}
    (h : ∀ rd0, LowDef κ rd0 → MemL rd0 Lin → CompleteAtBST CM.sem fs cert κ f Lin args (Returns rets) B Q) :
    CompleteAtBST CM.sem fs cert κ f Lin args (Returns rets) B Q := by
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  · obtain ⟨rd0, h1, h2⟩ := hex; exact h rd0 h1 h2
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **The queries by trees decoding to their openings**, bounded (`os_kid_queriesBC`). -/
theorem os_kid_queriesBCT {base I depth cd blocks : ℕ} {name loop : String} {B : ℕ → ℕ}
    (hq : ∀ (n : ℕ), n + 1 < ordG → ∀ (Lin : Main.Layout) (cap flags qw qbp rew : E) (leaf : ℕ → List K)
      (pos : ℕ → ℕ) (sibs : ℕ → List Digest) (wts qwV dbpV : ℕ → E),
      (∀ j < n, (leaf j).length = oqR base I) → (∀ j < n, pos j < 2 ^ depth) →
      (∀ j < n, (sibs j).length = depth - cd) → (∀ j < n, OqAns CM Ht (depth - cd) (leaf j) (pos j) (sibs j)) →
      (∀ rd, LowDef κ rd → MemL rd Lin →
        OqTopMemW Ht rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) →
      OqTopReg (RegionL Lin) I (depth - cd) cd rew qw qbp flags cap dbpV pos n →
      CompleteAtBST CM.sem fs cert κ name Lin [cap, flags, qw, qbp, rew, gen ^ n]
        (Returns [oqSum base I wts qwV leaf n]) (B n)
        (fun _ _ t => OqQueriesQ base I blocks (depth - cd) cd loop n cap leaf pos sibs t))
    {Lin : Main.Layout} {cap flags qw qbp rew : E} {n : ℕ}
    (hn : n + 1 < ordG) {leaf : ℕ → List K} {pos : ℕ → ℕ}
    {sibs : ℕ → List Digest} {wts qwV dbpV : ℕ → E} (hleaf : ∀ j < n, (leaf j).length = oqR base I)
    (hpos : ∀ j < n, pos j < 2 ^ depth) (hsl : ∀ j < n, (sibs j).length = depth - cd)
    (hans : ∀ j < n, OqAns CM Ht (depth - cd) (leaf j) (pos j) (sibs j))
    (hlin : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqTopMemW Ht rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) :
    CompleteAtBST CM.sem fs cert κ name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n])
      (B n) (fun _ _ t => OqQueriesQ base I blocks (depth - cd) cd loop n cap leaf pos sibs t) :=
  os_completeAtBT_of_nonempty (CM := CM) fun _ h1 h2 =>
    hq n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hpos hsl hans hlin
      (os_oqTopReg_ofC (Ht := Ht) hlin h1 h2)

namespace OsData

variable {cfg : OsCfg} {d : OsData} {bd : String → ℕ}

/-- A later callee other than the queries (not six words) and the cap, by any tree. -/
theorem osCBBCT_of_other {b l : ℕ} {Lk : Main.Layout} {W S : ℕ → Main.Layout} {f : String} {a r : List E}
    (ha : a.length ≠ 6) (hf : f ≠ (cfg.lv l).verifyCap) (h : osCBBC CM fs cert κ bd Lk W S f a r) :
    osCBBCT CM fs cert κ bd Lk W S (osQB Ht cfg d b l) f a r := fun p =>
  CompleteAtBST.monoT (CompleteAtBS.toBST (h p)) le_rfl le_rfl fun _ _ _ _ =>
    ⟨fun h6 => absurd h6 ha, fun h' => absurd h' hf⟩

/-- **A level's queries, placed, bounded.** -/
theorem lvCallQBCT {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hrun : RunOkW Ht cfg d) (hkT : OsKidsAtBCT CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    osCBBCT CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (osQB Ht cfg d b l)
      (cfg.lv l).queriesFn
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff,
        (osPtrsOf cfg b).qw * gen ^ (l * cfg.maxQ), (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff,
        osPtrAt cfg b (11 + 2 * l + 1), osGw (cfg.lv l).queries]
      [osHEnfW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, hper, hqs, -, -, -, -, hcd1, hcd2, -, -, -, -, hq62, -, -, -, -⟩ := hspec
  set L := d.lvW Ht cfg l with hL
  set rev : ℕ := if l = 0 then 1 else 0
  have hst := hF.step
  rw [hlv] at hst
  have hoa := lv_openC (Ht := Ht) (CM := CM) hF hlv
  have hcap := os_capOk_ofW hoa (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  obtain ⟨os1, hosp, hl1, hrows, hj⟩ := os_openAll_invW _ _ _ _ hoa
  have hqsl : (osHQsW Ht cfg l d.xs L.p L.H.cv1).length = (cfg.lv l).queries := by simp [osHQsW]
  rw [hqsl] at hl1
  set leaf : ℕ → List K := fun j => (os1.getD j ⟨[], []⟩).leaf
  set wts : ℕ → E := fun jw => (eqKernel L.H.chs).getD (orwSlot (cfg.lv l).folds rev jw) 0
  set qwV : ℕ → E := fun j => d.lamW Ht cfg l ^ j
  have hE : osHEnfW Ht cfg l d.xs L.p L.H = oqSum rev (2 ^ (cfg.lv l).folds) wts qwV leaf (cfg.lv l).queries := by
    have h := os_oqSum_eq (l := l) (hrun.chs l hl) (d.lamW Ht cfg l) (os1 := os1) (fun j hj' => by
      rw [(hj j hj').1])
    rw [hl1] at h
    rw [h]
    unfold osHEnfW
    rw [hqsl, hrows]
    rfl
  intro p
  rw [hE, os_gw_eq (by omega)]
  have hmemq : ∀ j < (cfg.lv l).queries, ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0, os1.getD j ⟨[], []⟩) ∈
      (osHQsW Ht cfg l d.xs L.p L.H.cv1).zip L.osp := by
    intro j hj'
    rw [hosp]
    refine List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip, List.length_append, hqsl]; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  obtain ⟨Bq, ⟨loopq, blocksq, hlk, hqB⟩, hqle⟩ := hkT l hl
  refine CompleteAtBST.monoT (os_kid_queriesBCT (Ht := Ht) (CM := CM) hqB (n := (cfg.lv l).queries) (by simp only [ordG]; omega) (leaf := leaf)
    (pos := fun j => (osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0)
    (sibs := fun j => (os1.getD j ⟨[], []⟩).path.take ((cfg.lv l).depth - (cfg.lv l).capDepth)) (wts := wts) (qwV := qwV)
    (dbpV := fun j => (qbpSeg cfg fs cert l p).getD j 0)
    (fun j hj' => by simp only [leaf]; rw [List.getD_eq_getElem _ _ (by omega)]; exact (hj j (by omega)).1)
    (fun j hj' => (hcap.pos _ (hmemq j hj')))
    (fun j hj' => by
      simp only [List.length_take]
      rw [List.getD_eq_getElem _ _ (by omega), (hj j (by omega)).2.1]; omega)
    (fun j hj' => oqAns_of_opening (lv_ansC hHt hF hlv _ (hmemq j hj')) (by omega))
    (fun rd _ hm => ?_)) le_rfl hqle ?_
  rotate_left
  · intro fp rd t ht
    refine ⟨fun _ => ⟨by rw [osQArgs, os_gw_eq (by omega)], ?_⟩, fun _ h2 => absurd h2 (by simp)⟩
    simp only [OsLvQ, hlk]
    refine OqQueriesQ.congr (fun j hj => ?_) (fun j _ => rfl) (fun j hj => ?_) ht
    · show (os1.getD j ⟨[], []⟩).leaf = (L.osp.getD j ⟨[], []⟩).leaf
      rw [hosp, List.getD_append _ _ _ _ (by omega)]
    · show (os1.getD j ⟨[], []⟩).path.take _ = (L.osp.getD j ⟨[], []⟩).path.take _
      rw [hosp, List.getD_append _ _ _ _ (by omega)]
  obtain ⟨hm12, hmS⟩ := Main.memL_append.mp hm
  obtain ⟨hmk, hmW⟩ := Main.memL_append.mp hm12
  have hb := hbuf rd hmk
  have hcells := os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
    (c := fun l => osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.caps
    (fun a c hac hc => by rw [os_capCells_lengthW]; exact hlay.caps a c hac hc)
    (fun a ha => by rw [os_capCells_lengthW]; exact hlay.capsFit a ha) hl
  have hflags := os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
    (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.flags
    (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
    (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl
  have hW := hmW _ (List.mem_singleton.mpr rfl)
  refine ⟨fun jw hjw => ?_, fun j hj' => ?_, fun j hj' => ?_, fun j hj' l' hl' => ?_, fun j hj' => ?_,
    fun j hj' => ?_⟩
  · have := os_readsAt_getD (hb.rew l hl) (k := jw) (by simpa [rewCW] using hjw)
    rw [rewCW, os_getD_map_range _ hjw] at this
    exact this
  · rw [loadHolds_mul_gen_pow]; exact qw_atC (Ht := Ht) hlay hb.qw hl j hj'
  · have e1 : (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff =
        ofK (Parameters.gpow ((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff)) := by
      show osPtrAt cfg b 8 * _ = _
      unfold osPtrAt; rw [ofK_gpow_mul]
    rw [e1]
    have hsq1 : 1 ≤ (cfg.lv l).squeezes := by
      rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
      · rw [h, Nat.zero_mul] at hqs; omega
      · exact h
    have := Nat.mul_le_mul_right (192 / (cfg.lv l).depth) hsq1
    exact os_readsAt_getD hW (by simp only [qbpSeg, List.length_map, List.length_range]; omega)
  · have hjs : j < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) := by omega
    have hdiv : j / (192 / (cfg.lv l).depth) < (cfg.lv l).squeezes := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hjs)
    have hmod : j % (192 / (cfg.lv l).depth) < (192 / (cfg.lv l).depth) := Nat.mod_lt _ hper
    have hpd : (192 / (cfg.lv l).depth) * (cfg.lv l).depth ≤ 192 := Nat.div_mul_le_self 192 (cfg.lv l).depth
    have hl'd : l' < (cfg.lv l).depth := by omega
    have hc : j % (192 / (cfg.lv l).depth) * (cfg.lv l).depth + l' < 192 := by
      have : (j % (192 / (cfg.lv l).depth) + 1) * (cfg.lv l).depth ≤ (192 / (cfg.lv l).depth) * (cfg.lv l).depth := Nat.mul_le_mul_right _ hmod
      rw [Nat.succ_mul] at this; omega
    simp only
    rw [List.getD_eq_getElem _ _ (by simp [qbpSeg]; exact hjs)]
    simp only [qbpSeg, List.getElem_map, List.getElem_range]
    rw [loadHolds_mul_gen_pow]
    have hpos : (osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0 = osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) j := by
      unfold osHQsW; rw [os_getD_map_range _ hj']; rfl
    rw [hpos, osPosOf_testBitC (Ht := Ht) _ _ hl'd]
    exact sqRuns_bitC hmS hdiv hc
  · have := osCap_parentW hcap hflags (hmemq j hj')
    exact this
  · have := osCap_leafW hcap hcells (hmemq j hj')
    exact this


/-- **A level's cap, placed, bounded, by trees loading its flagged nodes' children.** -/
theorem lvCallCapBCT {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l)
    (hL : VmcCapLoads) (h4 : 4 ≤ (cfg.lv l).capDepth) (h8 : (cfg.lv l).capDepth ≤ 8)
    (hvn : (cfg.lv l).verifyCap = vmcName (cfg.lv l).capDepth) :
    osCBBCT CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (osQB Ht cfg d b l)
      (cfg.lv l).verifyCap
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff]
      [(digestScalars (d.rtW Ht cfg l)).1, (digestScalars (d.rtW Ht cfg l)).2] := by
  intro p
  have h := lvCallCapBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hHt hk hbuf hQ hl hF hlv p
  refine CompleteAtBST.monoT ((CompleteAtBS.toBST h).and_of_valid
    (Q' := fun _ rd t => CapLoadsQ (cfg.lv l).capDepth rd (osCapArgs cfg b l) t) fun fp rd _ hm t rets hn hv => ?_)
    le_rfl le_rfl fun _ _ _ ht => ⟨fun h6 => absurd h6 (by simp), fun _ _ => ⟨rfl, ht.1⟩⟩
  obtain ⟨hm12, -⟩ := Main.memL_append.mp hm
  obtain ⟨hmk, -⟩ := Main.memL_append.mp hm12
  have hb := hbuf rd hmk
  have hcells := os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
    (c := fun l => osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.caps
    (fun a c hac hc => by rw [os_capCells_lengthW]; exact hlay.caps a c hac hc)
    (fun a ha => by rw [os_capCells_lengthW]; exact hlay.capsFit a ha) hl
  have hflags := os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
    (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.flags
    (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
    (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl
  exact hL CM.sem _ h4 h8 rd _ _ rets t (hn.trans (hvn.trans (vmcName_eq h4 h8).symm)) hv
    (hcells 0 (by rw [os_capCells_lengthW]; positivity)).1
    (hflags 0 (by simp only [osCapFlags, List.length_map, List.length_range]; positivity)).1

/-- **Every level's callees, placed, bounded.** -/
theorem lvsCallHBCT {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hrun : RunOkW Ht cfg d) (hk : OsKidsAtBC CM Ht fs cert κ cfg bd)
    (hkT : OsKidsAtBCT CM Ht fs cert κ cfg bd) (hcn : OsCapNames cfg) (hVL : VmcCapLoads) {Lin : Main.Layout} {b : ℕ}
    {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2)
    (hch : OsChainC CM.hm Ht cfg μ (cfg.lv 0).folds d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    OsLvsCallHC CM Ht (fun _ => osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b))
      (fun l => osCBBCT CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l)
        (osQB Ht cfg d b l))
      (fun l => osCsqBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l)) cfg d.xs cur
      (osPtrsOf cfg b) (fun l => osPtrAt cfg b (11 + 2 * l)) (fun l => osPtrAt cfg b (11 + 2 * l + 1)) 0 2
      (osW0 d.target d.xs) (d.roots0 cfg) d.Hs := by
  refine os_lvsCallH_memC (Ht := Ht) (CM := CM) d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) fun L hL => ?_
  obtain ⟨hg, hlt⟩ := os_lvs_getC (Ht := Ht) cfg d.xs d.Hs _ _ _ _ _ L hL
  have hl : L.lvl < cfg.levels.length := by rw [os_lvsList_lengthC (Ht := Ht), hrun.len] at hlt; exact hlt
  have hF := os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch L hL
  have e : d.lvW Ht cfg L.lvl = L := hg
  have hF' : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg L.lvl) := by rw [e]; exact hF
  have hlv : (d.lvW Ht cfg L.lvl).lvl = L.lvl := by rw [e]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := lvCallABC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hk hLin hbuf hl hF' hlv
  have hSq := lvCallSqBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) (d := d) hok hlay hk hbuf hl hHt
    (by have h := hF'.ans.sq; rw [hlv] at h; exact h)
  obtain ⟨h4, h8, hvn, hrwc⟩ := hcn L.lvl hl
  have hRw := osCBBCT_of_other (Ht := Ht) (cfg := cfg) (d := d) (b := b) (l := L.lvl) (by simp) hrwc <| lvCallRwBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hlay hrun hk hbuf hl
  have hCap := lvCallCapBCT (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hHt hk hbuf hQ hl hF' hlv
    hVL h4 h8 hvn
  have hQr := lvCallQBCT (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hHt hrun hkT hbuf hQ hl hF' hlv
  have ert : d.rtW Ht cfg L.lvl = (L.roots.getD L.lvl default).1 := by unfold rtW; rw [e]
  rw [e] at hA2 hA3 hA4 hQr
  rw [ert] at hCap
  exact ⟨hA1, hA2, hA3, hA4, hSq, hRw, hCap, hQr⟩

end OsData

end
end LeanVM.Guest.B1