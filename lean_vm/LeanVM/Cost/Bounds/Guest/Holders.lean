module

public import LeanVM.Cost.Bounds.Guest.Kids
public import LeanVM.Cost.Decoder.Staged

/-!
# Bounds on the guest decoder's prices: the children's list and the claims' holders

Off the tables `decWitAt` builds (`Cost/Decoder/Staged.lean`, `Holders.lean`), in the price `G`
of a logarithm, `R` of a read of the memory, `S` of `main`'s valuation and the prices `W`, `WX`,
`WS` of the witness closures `wV`, `wX`, `wS`; every count below `2^34`:

* **`kidsT_cost`** (`kidsTPrice G R S W N K`): the children, at most `K ≤ 2^34`, the regions'
  tables of at most `N ≤ 2^34` marks (`decKid_cost`, `Kids.lean`);
* the holder of a declared claim at its mark (`xmssHolderM_cost`, `sphincsHolderM_cost`: a raw
  signature at its slot's address, or the child the mark falls in, one search in the running
  maxima), the holder (`xmssHolder_cost`, `sphincsHolder_cost`: the mark one logarithm and one
  read), **`xmssHoldersT_cost`**, **`sphincsHoldersT_cost`** (`xmssHoldersTPrice G R WX X`, …): at
  most `X ≤ 2^34` holders.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

/-! ## The holders at their marks -/

section XmssM

variable {wX : E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : E, appCost P wXV [encodeValue a] ≤ WX)
include hwX hWX

/-- **The holder of declared leanXMSS claim `k` at its mark `e`** (`xmssHolderMC`), `k, e < 2^34`,
the maxima good: at most `WX + 20100`. -/
theorem xmssHolderM_cost (hP : Includes P xmssHolderMC.costDeps) (p53 : E) (M : Array ℕ)
    (hM : KidMaxGood M) (k e n : ℕ) (hk : k < 2 ^ 34) (he : e < 2 ^ 34) (hn : n < 2 ^ 64) :
    machineCost P xmssHolderMC.costIdx [encodeValue p53, wXV, encodeValue M, encodeValue k,
      encodeValue e, encodeValue n] ≤ WX + 20100 := by
  rw [xmssHolderMC.costEq P hP p53 wX wXV hwX]
  have h1 := powSqK_cost_lt P (by includes) Parameters.g (4 * k) 36 (by norm_num) (by norm_num)
    (by omega)
  have h2 := mulK_cost P (by includes) p53 (Parameters.g ^ (4 * k))
  have h3 := hWX (mulK p53 (Parameters.g ^ (4 * k)))
  have h4 := kidIn_cost P (by includes) M (fun i ↦ lt_trans (hM.2 i) (by norm_num)) hM.1 e
    (by omega)
  limbs_one
  split <;> omega

end XmssM

section SphincsM

variable {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
include hwS hWS

/-- **The holder of declared leanSPHINCS claim `k` at its mark `e`** (`sphincsHolderMC`), as
`xmssHolderM_cost`: at most `WS + 20100`. -/
theorem sphincsHolderM_cost (hP : Includes P sphincsHolderMC.costDeps) (p56 : E) (M : Array ℕ)
    (hM : KidMaxGood M) (k e n : ℕ) (hk : k < 2 ^ 34) (he : e < 2 ^ 34) (hn : n < 2 ^ 64) :
    machineCost P sphincsHolderMC.costIdx [encodeValue p56, wSV, encodeValue M, encodeValue k,
      encodeValue e, encodeValue n] ≤ WS + 20100 := by
  rw [sphincsHolderMC.costEq P hP p56 wS wSV hwS]
  have h1 := powSqK_cost_lt P (by includes) Parameters.g (4 * k) 36 (by norm_num) (by norm_num)
    (by omega)
  have h2 := mulK_cost P (by includes) p56 (Parameters.g ^ (4 * k))
  have h3 := hWS (mulK p56 (Parameters.g ^ (4 * k)))
  have h4 := kidIn_cost P (by includes) M (fun i ↦ lt_trans (hM.2 i) (by norm_num)) hM.1 e
    (by omega)
  limbs_one
  split <;> omega

end SphincsM

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

section Xmss

variable {wX : E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : E, appCost P wXV [encodeValue a] ≤ WX)
include hwX hWX

/-- **The holder of declared leanXMSS claim `k`** (`xmssHolderC`), `k < 2^34`, the raw count
`n < 2^64`: its mark (a read and a logarithm), then `xmssHolderM_cost`: at most
`G + R + WX + 41800`. -/
theorem xmssHolder_cost (D : DiscreteLogTables) (hP : Includes P xmssHolderC.costDeps)
    (hG : GLogBound P D G) (cover p53 : E) (M : Array ℕ) (hM : KidMaxGood M) (n k : ℕ)
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 34) :
    machineCost P xmssHolderC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p53, wXV,
      encodeValue M, encodeValue n, encodeValue k] ≤ G + R + WX + 41800 := by
  rw [xmssHolderC.costEq P hP D rd rdV hrd cover p53 wX wXV hwX]
  have h1 := cellAt_cost P hrd hR (by includes) cover k (by omega)
  have h2 := hG (cellAt rd cover k)
  have h3 := xmssHolderM_cost P hwX hWX (by includes) p53 M hM k (gLogD D (cellAt rd cover k)) n hk
    (gLogD_lt D _) hn
  omega

/-- The leanXMSS holders' price, at most `X` of them. -/
@[expose] def xmssHoldersTPrice (G R WX X : ℕ) : ℕ := (G + R + WX + 41850) * X + 30

/-- **The holders of the declared leanXMSS claims** (`xmssHoldersTC`), `n ≤ X ≤ 2^34`, the
maxima good, the raw count `nr < 2^64`: at most `xmssHoldersTPrice G R WX X`. -/
theorem xmssHoldersT_cost (D : DiscreteLogTables) (hP : Includes P xmssHoldersTC.costDeps)
    (hG : GLogBound P D G) (cover p53 : E) (M : Array ℕ) (hM : KidMaxGood M) (nr n : ℕ)
    (hnr : nr < 2 ^ 64) (X : ℕ) (hX : X ≤ 2 ^ 34) (hn : n ≤ X) :
    machineCost P xmssHoldersTC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p53,
      wXV, encodeValue M, encodeValue nr, encodeValue n] ≤ xmssHoldersTPrice G R WX X := by
  rw [xmssHoldersTC.costEq P hP D rd rdV hrd cover p53 wX wXV hwX]
  have h1 := rangeMap_le P (by includes) (by includes) (xmssHolderT D rd cover p53 wX M nr)
    (.closure xmssHoldersTC.lam0.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p53,
      wXV, encodeValue M, encodeValue nr])
    (fun k ↦ RunsApp.of_spec (xmssHoldersTC.lam0.costSpec P (by includes) D rd rdV hrd cover p53 wX
      wXV hwX M nr k))
    (G + R + WX + 41822) n X hn (by omega) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        xmssHoldersTC.lam0.costEq P (by includes) D rd rdV hrd cover p53 wX wXV hwX]
      have := xmssHolder_cost P hrd hR hwX hWX D (by includes) hG cover p53 M hM nr k hnr
        (by omega)
      omega)
  unfold xmssHoldersTPrice
  have : (G + R + WX + 41822 + 28) * X = (G + R + WX + 41850) * X := by ring
  omega

end Xmss

section Sphincs

variable {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
include hwS hWS

/-- **The holder of declared leanSPHINCS claim `k`** (`sphincsHolderC`), `lx, k < 2^34`, the raw
count `n < 2^64`: its mark at slot `lx + k`, then `sphincsHolderM_cost`: at most
`G + R + WS + 41800`. -/
theorem sphincsHolder_cost (D : DiscreteLogTables) (hP : Includes P sphincsHolderC.costDeps)
    (hG : GLogBound P D G) (cover p56 : E) (M : Array ℕ) (hM : KidMaxGood M) (lx n k : ℕ)
    (hlx : lx < 2 ^ 34) (hn : n < 2 ^ 64) (hk : k < 2 ^ 34) :
    machineCost P sphincsHolderC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p56,
      wSV, encodeValue M, encodeValue lx, encodeValue n, encodeValue k] ≤ G + R + WS + 41800 := by
  rw [sphincsHolderC.costEq P hP D rd rdV hrd cover p56 wS wSV hwS]
  have h1 := cellAt_cost P hrd hR (by includes) cover (lx + k) (by omega)
  have h2 := hG (cellAt rd cover (lx + k))
  have h3 := sphincsHolderM_cost P hwS hWS (by includes) p56 M hM k
    (gLogD D (cellAt rd cover (lx + k))) n hk (gLogD_lt D _) hn
  limbs_one
  omega

/-- The leanSPHINCS holders' price, at most `X` of them. -/
@[expose] def sphincsHoldersTPrice (G R WS X : ℕ) : ℕ := (G + R + WS + 41850) * X + 30

/-- **The holders of the declared leanSPHINCS claims** (`sphincsHoldersTC`), `n ≤ 2^34`, `lx <
2^34`, the maxima good, the raw count `nr < 2^64`: at most `sphincsHoldersTPrice G R WS X`. -/
theorem sphincsHoldersT_cost (D : DiscreteLogTables) (hP : Includes P sphincsHoldersTC.costDeps)
    (hG : GLogBound P D G) (cover p56 : E) (M : Array ℕ) (hM : KidMaxGood M) (lx nr n : ℕ)
    (hlx : lx < 2 ^ 34) (hnr : nr < 2 ^ 64) (X : ℕ) (hX : X ≤ 2 ^ 34) (hn : n ≤ X) :
    machineCost P sphincsHoldersTC.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p56,
      wSV, encodeValue M, encodeValue lx, encodeValue nr, encodeValue n] ≤
      sphincsHoldersTPrice G R WS X := by
  rw [sphincsHoldersTC.costEq P hP D rd rdV hrd cover p56 wS wSV hwS]
  have h1 := rangeMap_le P (by includes) (by includes) (sphincsHolderT D rd cover p56 wS M lx nr)
    (.closure sphincsHoldersTC.lam0.costIdx [encodeValue D, rdV, encodeValue cover, encodeValue p56,
      wSV, encodeValue M, encodeValue lx, encodeValue nr])
    (fun k ↦ RunsApp.of_spec (sphincsHoldersTC.lam0.costSpec P (by includes) D rd rdV hrd cover p56
      wS wSV hwS M lx nr k))
    (G + R + WS + 41822) n X hn (by omega) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        sphincsHoldersTC.lam0.costEq P (by includes) D rd rdV hrd cover p56 wS wSV hwS]
      have := sphincsHolder_cost P hrd hR hwS hWS D (by includes) hG cover p56 M hM lx nr k hlx hnr
        (by omega)
      omega)
  unfold sphincsHoldersTPrice
  have : (G + R + WS + 41822 + 28) * X = (G + R + WS + 41850) * X := by ring
  omega

end Sphincs

/-! ## The children -/

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
include hwV

/-- The children's price, at most `K` of them, the tables of at most `N` marks. -/
@[expose] def kidsTPrice (G R S W N K : ℕ) : ℕ := (decKidPrice G R S W N + 39) * K + 32

/-- **The children** (`kidsTC`), off good tables of at most `N ≤ 2^34` marks, `n ≤ K ≤ 2^34`, each
child's proof at most `W` (`wV` at its arguments, `subArgsK`): at most
`kidsTPrice G R S W N K = K·(decKidPrice G R S W N + 39) + 32`. -/
theorem kidsT_cost (D : DiscreteLogTables) (hP : Includes P kidsTC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (K : ℕ) (hK : K ≤ 2 ^ 34) (n : ℕ) (hn : n ≤ K) {W : ℕ}
    (hW : ∀ c < n, appCost P wVV [encodeValue (subArgsK rd σ c)] ≤ W) :
    machineCost P kidsTC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue n] ≤ kidsTPrice G R S W N K := by
  rw [kidsTC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := rangeMap_le P (by includes) (by includes) (decKidT D rd σ wV w380 p53 p56 tx ts)
    (.closure kidsTC.lam0.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts])
    (fun c ↦ RunsApp.of_spec (kidsTC.lam0.costSpec P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV
      w380 p53 p56 tx ts c))
    (decKidPrice G R S W N + 11) n K hn (by omega) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, kidsTC.lam0.costEq P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV]
      have := decKid_cost P hrd hR hσ hS hwV D (by includes) hG w380 p53 p56 tx ts htx hts N hN
        htxN htsN c (by omega) (hW c hc)
      omega)
  unfold kidsTPrice
  have : (decKidPrice G R S W N + 11 + 28) * K = (decKidPrice G R S W N + 39) * K := by ring
  omega

end Proof

end Val

end Reader

end

end LeanVM.Cost.Bounds.Guest
