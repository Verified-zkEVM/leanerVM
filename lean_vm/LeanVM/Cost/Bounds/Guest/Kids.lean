module

public import LeanVM.Cost.Bounds.Guest.Search
public import LeanVM.Cost.Bounds.Guest.Stmt

/-!
# Bounds on the guest decoder's prices: the coverage tables and the children

The tables `decWitAt` builds once and the children off them (`Cost/Decoder/Kids.lean`), in the
price `G` of a logarithm (`GLogBound P D G`), `R` of a read of the memory, `S` of `main`'s
valuation and `W` of the child proofs' reader `wV`; every count, mark and slot below `2^34`
(`gLogD_lt`):

* a mark and its slot (`markPair_cost`), **`regionTable_cost`** (`regionTablePrice G R len`: one
  logarithm and one read per slot, the table sorted, `coverTable_cost`), `regionTable_good`;
* a running count (`countAtW_cost`, `countNext_cost`), **`kidMax_cost`** (`kidMaxPrice G R n`),
  `kidMax_good` (`KidMaxGood`: at most `2^34` maxima below `2^34`);
* a child's claim (`xmssKidClaim_cost`, `sphincsKidClaim_cost`: a search, a power in `K`, four
  reads), a child's statement off its claims' counts (`kidStmtAt_cost`), its segment
  (`kidStmtSeg_cost`), **`kidStmt_cost`** (`kidStmtPrice G R S`), `subArgs_cost`,
  **`decKid_cost`** (`decKidPrice G R S W`), each claim of a child's at most `2^35` (every slot
  of both regions, on any memory). The children's list is `Holders.lean`'s `kidsT_cost`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

/-! ## Facts of the tables -/

theorem countIn_le (tm : Array ℕ) (a b : ℕ) : countIn tm a b ≤ tm.size := by
  unfold countIn
  have := lowerBound_le_size tm b
  omega

theorem slotIn_lt {t : Array ℕ × Array ℕ} (ht : TableGood t) (e : ℕ) : slotIn t.1 t.2 e < 2 ^ 34 := by
  unfold slotIn
  dsimp only
  split
  · exact ht.2.2.2 _
  · norm_num

theorem lt64_of_good {t : Array ℕ × Array ℕ} (ht : TableGood t) (i : ℕ) : t.1.getD i 0 < 2 ^ 64 :=
  lt_trans (ht.2.2.1 i) (by norm_num)

/-- **What the holders need of the running maxima**: at most `2^34` of them, below `2^34`. -/
@[expose] def KidMaxGood (M : Array ℕ) : Prop := M.size ≤ 2 ^ 34 ∧ ∀ i, M.getD i 0 < 2 ^ 34

theorem prefixMax_lt {B : ℕ} : ∀ (xs : List ℕ) (acc : ℕ), acc < B → (∀ x ∈ xs, x < B) →
    ∀ y ∈ prefixMax acc xs, y < B
  | [], _, _, _ => by simp [prefixMax]
  | x :: xs, acc, hacc, hx => by
    intro y hy
    simp only [prefixMax, List.mem_cons] at hy
    have hx0 := hx x (by simp)
    rcases hy with rfl | hy
    · split <;> omega
    · exact prefixMax_lt xs _ (by split <;> omega) (fun z hz ↦ hx z (by simp [hz])) y hy

/-! ## The tables -/

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- **A slot's mark and the slot** (`markPairC`), `lo + s < 2^40`: at most `G + R + 21700`. -/
theorem markPair_cost (D : DiscreteLogTables) (hP : Includes P markPairC.costDeps)
    (hG : GLogBound P D G) (cover : E) (lo s : ℕ) (h : lo + s < 2 ^ 40) :
    machineCost P markPairC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo,
      encodeValue s] ≤ G + R + 21700 := by
  rw [markPairC.costEq P hP D rd rdV hrd, markPairOfC.costEq P (by includes)]
  have := cellAt_cost P hrd hR (by includes) cover (lo + s) h
  have := hG (cellAt rd cover (lo + s))
  limbs_one
  omega

/-- The coverage table's price for a region of `len` slots. -/
@[expose] def regionTablePrice (G R len : ℕ) : ℕ := (G + R + 27400) * len + 1100

/-- **The coverage table of the region `[lo, lo + len)`** (`regionTableC`), `lo, len ≤ 2^34`: one
mark per slot, then sorted: at most `regionTablePrice G R len = (G + R + 27400)·len + 1100`. -/
theorem regionTable_cost (D : DiscreteLogTables) (hP : Includes P regionTableC.costDeps)
    (hG : GLogBound P D G) (cover : E) (lo len : ℕ) (hlo : lo ≤ 2 ^ 34) (hlen : len ≤ 2 ^ 34) :
    machineCost P regionTableC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo,
      encodeValue len] ≤ regionTablePrice G R len := by
  rw [regionTableC.costEq P hP D rd rdV hrd]
  have h1 := rangeMap_le P (by includes) (by includes) (markPair D rd cover lo)
    (.closure regionTableC.lam0.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue lo])
    (fun s ↦ RunsApp.of_spec (regionTableC.lam0.costSpec P (by includes) D rd rdV hrd cover lo s))
    (G + R + 21706) len len (le_refl _) (by omega) (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, regionTableC.lam0.costEq P (by includes) D rd rdV hrd]
      have := markPair_cost P hrd hR D (by includes) hG cover lo s (by omega)
      omega)
  have h2 := coverTable_cost P (by includes) ((List.range len).map (markPair D rd cover lo))
    (by simp; omega) (fun p hp ↦ by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
      rw [List.mem_range] at hs
      have := gLogD_lt D (cellAt rd cover (lo + s))
      exact ⟨by simp only [markPair, markPairOf]; omega, by simp only [markPair, markPairOf]; omega⟩)
  simp only [List.length_map, List.length_range] at h2
  unfold regionTablePrice
  unfold coverTablePrice at h2
  nlinarith

omit hrd hR in
/-- **A region's coverage table is good**, `len ≤ 2^34`. -/
theorem regionTable_good (D : DiscreteLogTables) (cover : E) (lo len : ℕ) (hlen : len ≤ 2 ^ 34) :
    TableGood (regionTable D rd cover lo len) :=
  coverTable_good _ (by simp; omega) (fun p hp ↦ by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range] at hs
    exact ⟨gLogD_lt D _, by simp only [markPair, markPairOf]; omega⟩)

/-- A running count (`countAtWC`), `c < 2^40`: at most `G + R + 21684`. -/
theorem countAtW_cost (D : DiscreteLogTables) (hP : Includes P countAtWC.costDeps)
    (hG : GLogBound P D G) (w : E) (c : ℕ) (hc : c < 2 ^ 40) :
    machineCost P countAtWC.costIdx [encodeValue D, rdV, encodeValue w, encodeValue c] ≤
      G + R + 21684 := by
  rw [countAtWC.costEq P hP D rd rdV hrd]
  have := cellAt_cost P hrd hR (by includes) w c hc
  have := hG (cellAt rd w c)
  omega

/-- A segment's end (`countNextC`), `c + 1 < 2^40`: at most `G + R + 21687`. -/
theorem countNext_cost (D : DiscreteLogTables) (hP : Includes P countNextC.costDeps)
    (hG : GLogBound P D G) (w : E) (c : ℕ) (hc : c + 1 < 2 ^ 40) :
    machineCost P countNextC.costIdx [encodeValue D, rdV, encodeValue w, encodeValue c] ≤
      G + R + 21687 := by
  rw [countNextC.costEq P hP D rd rdV hrd]
  have := cellAt_cost P hrd hR (by includes) w (c + 1) hc
  have := hG (cellAt rd w (c + 1))
  limbs_one
  omega

/-- The running maxima's price for `n` children. -/
@[expose] def kidMaxPrice (G R n : ℕ) : ℕ := (G + R + 21800) * n + 30

/-- **The running maxima of the children's segments' ends** (`kidMaxC`), `n ≤ 2^34`: one
logarithm and one read per child: at most `kidMaxPrice G R n = (G + R + 21800)·n + 30`. -/
theorem kidMax_cost (D : DiscreteLogTables) (hP : Includes P kidMaxC.costDeps)
    (hG : GLogBound P D G) (w : E) (n : ℕ) (hn : n ≤ 2 ^ 34) :
    machineCost P kidMaxC.costIdx [encodeValue D, rdV, encodeValue w, encodeValue n] ≤
      kidMaxPrice G R n := by
  rw [kidMaxC.costEq P hP D rd rdV hrd]
  have h1 := rangeMap_le P (by includes) (by includes) (countNext D rd w)
    (.closure kidMaxC.lam0.costIdx [encodeValue D, rdV, encodeValue w])
    (fun c ↦ RunsApp.of_spec (kidMaxC.lam0.costSpec P (by includes) D rd rdV hrd w c))
    (G + R + 21692) n n (le_refl _) (by omega) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        kidMaxC.lam0.costEq P (by includes) D rd rdV hrd]
      have := countNext_cost P hrd hR D (by includes) hG w c (by omega)
      omega)
  have h2 := prefixMax_cost P (by includes) ((List.range n).map (countNext D rd w)) 0 (by norm_num)
    (fun x hx ↦ by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact lt_trans (gLogD_lt D _) (by norm_num))
  rw [length_prefixMax]
  simp only [List.length_map, List.length_range] at h2 ⊢
  unfold kidMaxPrice
  nlinarith

omit hrd hR in
/-- **The running maxima are good**, `n ≤ 2^34`. -/
theorem kidMax_good (D : DiscreteLogTables) (w : E) (n : ℕ) (hn : n ≤ 2 ^ 34) :
    KidMaxGood (kidMax D rd w n) := by
  refine ⟨by simp [kidMax, length_prefixMax]; omega, fun i ↦ ?_⟩
  exact getD_lt_of_mem (prefixMax_lt _ 0 (by norm_num) (fun x hx ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact gLogD_lt D _)) (by norm_num) i

/-! ## A child -/

/-- **A child's leanXMSS claim** (`xmssKidClaimC`) off a good table, `a, j < 2^35`: a search, a
power in `K` and four reads, at most `4·R + 108134`. -/
theorem xmssKidClaim_cost (hP : Includes P xmssKidClaimC.costDeps) (p53 : E)
    (t : Array ℕ × Array ℕ) (ht : TableGood t) (a j : ℕ) (ha : a < 2 ^ 35) (hj : j < 2 ^ 35) :
    machineCost P xmssKidClaimC.costIdx [rdV, encodeValue p53, encodeValue t.1, encodeValue t.2,
      encodeValue a, encodeValue j] ≤ 4 * R + 108134 := by
  rw [xmssKidClaimC.costEq P hP rd rdV hrd]
  have h1 := slotIn_cost P (by includes) t.1 t.2 (lt64_of_good ht) ht.2.1 (a + j) (by omega)
  have hs := slotIn_lt ht (a + j)
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * slotIn t.1 t.2 (a + j)) 36 (by norm_num)
    (by norm_num) (by omega)
  have h3 := xmssAtK_cost P hrd hR (by includes)
    (p53.limb 0 * Parameters.g ^ (4 * slotIn t.1 t.2 (a + j)))
  limbs_one
  omega

/-- **A child's leanSPHINCS claim** (`sphincsKidClaimC`), as `xmssKidClaim_cost`. -/
theorem sphincsKidClaim_cost (hP : Includes P sphincsKidClaimC.costDeps) (p56 : E)
    (t : Array ℕ × Array ℕ) (ht : TableGood t) (a j : ℕ) (ha : a < 2 ^ 35) (hj : j < 2 ^ 35) :
    machineCost P sphincsKidClaimC.costIdx [rdV, encodeValue p56, encodeValue t.1, encodeValue t.2,
      encodeValue a, encodeValue j] ≤ 4 * R + 108134 := by
  rw [sphincsKidClaimC.costEq P hP rd rdV hrd]
  have h1 := slotIn_cost P (by includes) t.1 t.2 (lt64_of_good ht) ht.2.1 (a + j) (by omega)
  have hs := slotIn_lt ht (a + j)
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (4 * slotIn t.1 t.2 (a + j)) 36 (by norm_num)
    (by norm_num) (by omega)
  have h3 := sphincsAtK_cost P hrd hR (by includes)
    (p56.limb 0 * Parameters.g ^ (4 * slotIn t.1 t.2 (a + j)))
  limbs_one
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A child's statement's price off its claims' counts, both at most `2^34`. -/
@[expose] def kidStmtAtPrice (R S : ℕ) : ℕ := (8 * R + 216338) * 2 ^ 34 + 26 * R + 3 * S + 587400

/-- **A child's statement, its claims' counts given** (`kidStmtAtC`), off good tables, `c, a <
2^34`, `nx, ns ≤ 2^34`: at most `kidStmtAtPrice R S ≈ 2^37·R + 2^51.7`. -/
theorem kidStmtAt_cost (hP : Includes P kidStmtAtC.costDeps) (p53 p56 : E)
    (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts) (c a nx ns : ℕ)
    (hc : c < 2 ^ 34) (ha : a < 2 ^ 34) (hnx : nx ≤ 2 ^ 34) (hns : ns ≤ 2 ^ 34) :
    machineCost P kidStmtAtC.costIdx [rdV, σV, encodeValue p53, encodeValue p56, encodeValue tx,
      encodeValue ts, encodeValue c, encodeValue a, encodeValue nx, encodeValue ns] ≤
      kidStmtAtPrice R S := by
  rw [kidStmtAtC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := rangeMap_le P (by includes) (by includes) (xmssKidClaim rd p53 tx.1 tx.2 a)
    (.closure kidStmtAtC.lam0.costIdx [rdV, encodeValue p53, encodeValue a, encodeValue tx.2,
      encodeValue tx.1])
    (fun j ↦ RunsApp.of_spec (kidStmtAtC.lam0.costSpec P (by includes) rd rdV hrd p53 a tx.2 tx.1 j))
    (4 * R + 108141) nx (2 ^ 34) hnx (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, kidStmtAtC.lam0.costEq P (by includes) rd rdV hrd]
      have := xmssKidClaim_cost P hrd hR (by includes) p53 tx htx a j (by omega) (by omega)
      omega)
  have h2 := rangeMap_le P (by includes) (by includes) (sphincsKidClaim rd p56 ts.1 ts.2 (a + nx))
    (.closure kidStmtAtC.lam1.costIdx [rdV, encodeValue p56, encodeValue (a + nx), encodeValue ts.1,
      encodeValue ts.2])
    (fun j ↦ RunsApp.of_spec
      (kidStmtAtC.lam1.costSpec P (by includes) rd rdV hrd p56 (a + nx) ts.1 ts.2 j))
    (4 * R + 108141) ns (2 ^ 34) hns (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append, kidStmtAtC.lam1.costEq P (by includes) rd rdV hrd]
      have := sphincsKidClaim_cost P hrd hR (by includes) p56 ts hts (a + nx) j (by omega)
        (by omega)
      omega)
  have h3 := daDigestAt_cost P hrd hR hσ hS (by includes) c (by omega)
  have h4 := hS (.n 377)
  have h5 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h6 := readCellsK_cost P hrd hR (by includes) ((σ (.n 377)).limb 0 * Parameters.g ^ (24 * c)) 24
    (by norm_num)
  have h7 := deferOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 377)).limb 0 * Parameters.g ^ (24 * c)) 24)
  limbs_one
  unfold kidStmtAtPrice
  omega

/-- **A child's statement, its segment `[a, b)` given** (`kidStmtSegC`): the claims counted by two
searches each, then `kidStmtAt_cost`. -/
theorem kidStmtSeg_cost (hP : Includes P kidStmtSegC.costDeps) (p53 p56 : E)
    (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts) (c a b : ℕ)
    (hc : c < 2 ^ 34) (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) :
    machineCost P kidStmtSegC.costIdx [rdV, σV, encodeValue p53, encodeValue p56, encodeValue tx,
      encodeValue ts, encodeValue c, encodeValue a, encodeValue b] ≤
      kidStmtAtPrice R S + 5671 := by
  rw [kidStmtSegC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := countIn_cost P (by includes) tx.1 (lt64_of_good htx) htx.2.1 a b (by omega) (by omega)
  have h2 := countIn_cost P (by includes) ts.1 (lt64_of_good hts) hts.2.1 a b (by omega) (by omega)
  have h3 := kidStmtAt_cost P hrd hR hσ hS (by includes) p53 p56 tx ts htx hts c a
    (countIn tx.1 a b) (countIn ts.1 a b) hc ha
    ((countIn_le tx.1 a b).trans htx.2.1) ((countIn_le ts.1 a b).trans hts.2.1)
  omega

/-- A child's statement's price. -/
@[expose] def kidStmtPrice (G R S : ℕ) : ℕ := 2 * G + 2 * R + kidStmtAtPrice R S + 49100

/-- **Child `c`'s statement** (`kidStmtC`), off good tables, `c < 2^34`: its segment's ends (two
logarithms), then `kidStmtSeg_cost`: at most `kidStmtPrice G R S`. -/
theorem kidStmt_cost (D : DiscreteLogTables) (hP : Includes P kidStmtC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P kidStmtC.costIdx [encodeValue D, rdV, σV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ kidStmtPrice G R S := by
  rw [kidStmtC.costEq P hP D rd rdV hrd σ σV hσ]
  have h1 := countAtW_cost P hrd hR D (by includes) hG w380 c (by omega)
  have h2 := countAtW_cost P hrd hR D (by includes) hG w380 (c + 1) (by omega)
  have h3 := kidStmtSeg_cost P hrd hR hσ hS (by includes) p53 p56 tx ts htx hts c
    (countAtW D rd w380 c) (countAtW D rd w380 (c + 1)) hc (gLogD_lt D _) (gLogD_lt D _)
  limbs_one
  unfold kidStmtPrice
  omega

/-- **Child `c`'s `verify_sub` words** (`subArgsC`), `c < 2^34`: at most `7·S + 2·R + 65120`. -/
theorem subArgs_cost (hP : Includes P subArgsC.costDeps) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P subArgsC.costIdx [rdV, σV, encodeValue c] ≤ 7 * S + 2 * R + 65120 := by
  rw [subArgsC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := cellAt_cost P hrd hR (by includes) (σ (.n 365)) (2 * c) (by omega)
  have h2 := cellAt_cost P hrd hR (by includes) (σ (.n 365)) (2 * c + 1) (by omega)
  have h3 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h4 := mulK_cost P (by includes) (σ (.n 371)) (Parameters.g ^ (24 * c))
  have := hS (.n 365); have := hS (.n 47); have := hS (.n 48); have := hS (.n 49)
  have := hS (.n 50); have := hS (.n 371)
  limbs_one
  omega

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
  {W : ℕ} (hW : ∀ a : List E, appCost P wVV [encodeValue a] ≤ W)
include hwV hW

/-- A child's price. -/
@[expose] def decKidPrice (G R S W : ℕ) : ℕ := kidStmtPrice G R S + W + 8 * S + 26 * R + 608200

/-- **Child `c`** (`decKidC`), off good tables, `c < 2^34`: its statement, its proof's claim (24
reads), its proof (`wV` at its `verify_sub` words): at most `decKidPrice G R S W`. -/
theorem decKid_cost (D : DiscreteLogTables) (hP : Includes P decKidC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P decKidC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ decKidPrice G R S W := by
  rw [decKidC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := kidStmt_cost P hrd hR hσ hS D (by includes) hG w380 p53 p56 tx ts htx hts c hc
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h3 := readCellsK_cost P hrd hR (by includes) ((σ (.n 371)).limb 0 * Parameters.g ^ (24 * c)) 24
    (by norm_num)
  have h4 := fixedOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 371)).limb 0 * Parameters.g ^ (24 * c)) 24)
  have h5 := subArgs_cost P hrd hR hσ hS (by includes) c hc
  have := hS (.n 371)
  have := hW (subArgsK rd σ c)
  limbs_one
  unfold decKidPrice
  omega

end Proof

end Val

end Reader

end

end LeanVM.Cost.Bounds.Guest
