module

public import LeanVM.Cost.Bounds.Guest.Holders
public import LeanVM.Cost.Bounds.Guest.Frames
public import LeanVM.Cost.Bounds.Guest.Da
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Decoder.Witness

/-!
# Bounds on the guest decoder's prices: the witness

`Cost/Decoder/{Holders,Staged,Witness}.lean`: the witness off the tables (`decWitTabC`), the tables
built once (`decWitAtC`), the counts read (`decWitC`), and `decWitNC`, the callees' witnesses off
their frames; `main`'s valuation (`mainValC`). In the prices of a memory read `R`, of `main`'s
valuation `S`, of the frame map `F`, of a logarithm `G` (`GLogBound`), of the cursor's length `C`
(its value at most `L ≤ 2^32`), and of `da_verify`'s witness at its frame `DW` (`Bounds/Guest/Da.lean`):

* `nDirect_cost`, `dvClaim_cost`, `daWitness_cost`, `aggArgs_cost`, `nodeWitnessOf_cost`;
* `decWitTab_cost` (`decWitTabPrice`), `decWitAt_cost` (`decWitAtPrice`), **`decWitC_cost`**
  (`decWitPrice G R S WX WS WD WV WA`, the callees' witness functions' prices given);
* **`decWitN_cost`**: `decWitNC` at most `decWitNPrice G R S F C L DW`;
* `mainVal_cost`: `main`'s valuation, at most `R + 10990`, for every value.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : MachineProgram) {G : ℕ}

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A count read off `main`'s valuation (`nKidsC`, `lxSlotsC`, …): `S + G + 11`. -/
theorem nDirect_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nDirectC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nDirectC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nDirectC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 7)); have := hS (.n 7); omega

theorem nKids_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nKidsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nKidsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nKidsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 6)); have := hS (.n 6); omega

theorem lxSlots_cost (D : DiscreteLogTables) (hP : Includes P Decoder.lxSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lxSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lxSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 40)); have := hS (.n 40); omega

theorem lsSlots_cost (D : DiscreteLogTables) (hP : Includes P Decoder.lsSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lsSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lsSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 41)); have := hS (.n 41); omega

theorem nRawX_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nRawXC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawXC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawXC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 2)); have := hS (.n 2); omega

theorem nRawS_cost (D : DiscreteLogTables) (hP : Includes P Decoder.nRawSC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawSC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawSC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 5)); have := hS (.n 5); omega

/-- The DA claim (`dvClaimC`): `4·S + 93`. -/
theorem dvClaim_cost (hP : Includes P Decoder.dvClaimC.costDeps) :
    machineCost P Decoder.dvClaimC.costIdx [σV] ≤ 4 * S + 93 := by
  rw [Decoder.dvClaimC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes),
    digestOfCells_cost P (by includes)]
  cost_facts [hS]
  omega

/-- The words of `aggregate_claims`' call (`aggArgsC`): `5·S + 61`. -/
theorem aggArgs_cost (hP : Includes P Decoder.aggArgsC.costDeps) :
    machineCost P Decoder.aggArgsC.costIdx [σV] ≤ 5 * S + 61 := by
  rw [Decoder.aggArgsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- **The DA claim and matrix** (`daWitnessC`), the DA witness function's price at most `WD`:
`10·S + G + WD + 183`. -/
theorem daWitness_cost (D : DiscreteLogTables) (hP : Includes P Decoder.daWitnessC.costDeps)
    (hG : GLogBound P D G) {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
    (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
    {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD) :
    machineCost P Decoder.daWitnessC.costIdx [encodeValue D, σV, wDV] ≤ 10 * S + G + WD + 183 := by
  rw [Decoder.daWitnessC.costEq P hP D σ σV hσ wD wDV hwD]
  have := nDirect_cost P hσ hS D (by includes) hG
  have := dvClaim_cost P hσ hS (by includes)
  have := hWD [σ (.n 50)] [σ (.n 339), σ (.n 340), σ (.n 341), σ (.n 342)] (by simp)
  have : Decoder.nDirectD D σ < 2 ^ 34 := gLogD_lt D _
  cost_facts [hS]
  limbs_one
  split_ifs <;> omega

end Val

/-- A witness of its fields (`nodeWitnessOfC`): `11`. -/
theorem nodeWitnessOf_cost (hP : Includes P Decoder.nodeWitnessOfC.costDeps) (c : List LeanVM.Node.Child)
    (x : List (LeanVM.Node.ClaimHolder LeanXmss.Signature))
    (s : List (LeanVM.Node.ClaimHolder Sphincs.Signature))
    (d : Option (LeanVM.Node.DaClaim × LeanVM.Da.MatrixWitness)) (h : LeanVM.Node.BatchingHints) :
    machineCost P Decoder.nodeWitnessOfC.costIdx
      [encodeValue c, encodeValue x, encodeValue s, encodeValue d, encodeValue h] = 11 := by
  rw [Decoder.nodeWitnessOfC.costEq P hP]

/-! ## The witness, the callees' witness functions given -/

section Witness

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {wX : E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : E, appCost P wXV [encodeValue a] ≤ WX)
  {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
  {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
  (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
  {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD)
  {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
  {WV : ℕ} (hWV : ∀ a : List E, a.length ≤ 16 → appCost P wVV [encodeValue a] ≤ WV)
  {wA : List E → LeanVM.Node.BatchingHints} {wAV : MachineValue}
  (hwA : ∀ a : List E, RunsApp P wAV [encodeValue a] (encodeValue (wA a)))
  {WA : ℕ} (hWA : ∀ a : List E, a.length ≤ 16 → appCost P wAV [encodeValue a] ≤ WA)
include hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hWV hwA hWA

/-- The witness's price off the tables. -/
@[expose] def decWitTabPrice (G R S WX WS WD WV WA : ℕ) : ℕ :=
  kidsTPrice G R S WV + xmssHoldersTPrice G R WX + 1 + sphincsHoldersTPrice G R WS +
    (10 * S + G + WD + 183) + (5 * S + 61) + WA + 11 + 41

/-- **The witness off the tables** (`decWitTabC`), the tables good, the counts below `2^34`:
at most `decWitTabPrice G R S WX WS WD WV WA`. -/
theorem decWitTab_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitTabC.costDeps)
    (hG : GLogBound P D G) (nk nx ns lx nrx nrs : ℕ) (hnk : nk ≤ 2 ^ 34) (hnx : nx ≤ 2 ^ 34)
    (hns : ns ≤ 2 ^ 34) (hlx : lx < 2 ^ 34) (hnrx : nrx < 2 ^ 34) (hnrs : nrs < 2 ^ 34)
    (cover w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts)
    (M : Array ℕ) (hM : KidMaxGood M) :
    machineCost P Decoder.decWitTabC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue nx, encodeValue ns, encodeValue lx, encodeValue nrx,
      encodeValue nrs, encodeValue cover, encodeValue w380, encodeValue p53, encodeValue p56,
      encodeValue tx, encodeValue ts, encodeValue M] ≤ decWitTabPrice G R S WX WS WD WV WA := by
  rw [Decoder.decWitTabC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := kidsT_cost P hrd hR hσ hS hwV hWV D (by includes) hG w380 p53 p56 tx ts htx hts nk hnk
  have := xmssHoldersT_cost P hrd hR hwX hWX D (by includes) hG cover p53 M hM nrx nx (by omega)
    hnx
  have := sphincsHoldersT_cost P hrd hR hwS hWS D (by includes) hG cover p56 M hM lx (nrx + nrs) ns
    hlx (by omega) hns
  have := daWitness_cost P hσ hS D (by includes) hG hwD hWD
  have := aggArgs_cost P hσ hS (by includes)
  have := hWA (Decoder.aggArgs σ) (by simp [Decoder.aggArgs])
  rw [nodeWitnessOf_cost P (by includes)]
  unfold decWitTabPrice
  limbs_one
  omega

/-- The witness's price, the tables built. -/
@[expose] def decWitAtPrice (G R S WX WS WD WV WA : ℕ) : ℕ :=
  7 * S + 2 * regionTablePrice G R (2 ^ 34) + kidMaxPrice G R (2 ^ 34) +
    decWitTabPrice G R S WX WS WD WV WA + 92

/-- **The witness, the counts given** (`decWitAtC`): the two regions' tables and the running maxima
built once, then `decWitTabC`: at most `decWitAtPrice G R S WX WS WD WV WA`. -/
theorem decWitAt_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitAtC.costDeps)
    (hG : GLogBound P D G) (nk nx ns lx ls nrx nrs : ℕ) (hnk : nk ≤ 2 ^ 34) (hnx : nx ≤ 2 ^ 34)
    (hns : ns ≤ 2 ^ 34) (hlx : lx < 2 ^ 34) (hls : ls ≤ 2 ^ 34) (hnrx : nrx < 2 ^ 34)
    (hnrs : nrs < 2 ^ 34) :
    machineCost P Decoder.decWitAtC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue nx, encodeValue ns, encodeValue lx, encodeValue ls,
      encodeValue nrx, encodeValue nrs] ≤ decWitAtPrice G R S WX WS WD WV WA := by
  rw [Decoder.decWitAtC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have h1 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 67)) 0 lx (by norm_num) hlx.le
  have h2 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 67)) lx ls hlx.le hls
  have h3 := kidMax_cost P hrd hR D (by includes) hG (σ (.n 380)) nk hnk
  have := decWitTab_cost P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hWV hwA hWA D (by includes) hG
    nk nx ns lx nrx nrs hnk hnx hns hlx hnrx hnrs (σ (.n 67)) (σ (.n 380)) (σ (.n 53)) (σ (.n 56))
    _ _ (regionTable_good (rd := rd) D (σ (.n 67)) 0 lx hlx.le)
    (regionTable_good (rd := rd) D (σ (.n 67)) lx ls hls) _
    (kidMax_good (rd := rd) D (σ (.n 380)) nk hnk)
  have e1 : regionTablePrice G R lx ≤ regionTablePrice G R (2 ^ 34) := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlx.le) _
  have e2 : regionTablePrice G R ls ≤ regionTablePrice G R (2 ^ 34) := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hls) _
  have e3 : kidMaxPrice G R nk ≤ kidMaxPrice G R (2 ^ 34) := by
    unfold kidMaxPrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hnk) _
  cost_facts [hS]
  unfold decWitAtPrice
  omega

/-- The witness's price. -/
@[expose] def decWitPrice (G R S WX WS WD WV WA : ℕ) : ℕ :=
  7 * (S + G + 11) + decWitAtPrice G R S WX WS WD WV WA + 46

/-- **The witness** (`decWitC`), the logarithm's tables `D` given, the callees' witness functions'
prices given: the counts (seven logarithms), then `decWitAtC`: at most
`decWitPrice G R S WX WS WD WV WA`. -/
theorem decWitC_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.decWitC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV] ≤
      decWitPrice G R S WX WS WD WV WA := by
  rw [Decoder.decWitC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := nKids_cost P hσ hS D (by includes) hG
  have := lxSlots_cost P hσ hS D (by includes) hG
  have := lsSlots_cost P hσ hS D (by includes) hG
  have := nRawX_cost P hσ hS D (by includes) hG
  have := nRawS_cost P hσ hS D (by includes) hG
  have := hG (σ (.n 0)); have := hG (σ (.n 3))
  have := decWitAt_cost P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hWV hwA hWA D (by includes) hG
    (Decoder.nKidsD D σ) (Decoder.gLogD D (σ (.n 0))) (Decoder.gLogD D (σ (.n 3)))
    (Decoder.lxSlotsD D σ) (Decoder.lsSlotsD D σ) (Decoder.nRawXD D σ) (Decoder.nRawSD D σ)
    (gLogD_lt D _).le (gLogD_lt D _).le (gLogD_lt D _).le (gLogD_lt D _) (gLogD_lt D _).le
    (gLogD_lt D _) (gLogD_lt D _)
  cost_facts [hS]
  unfold decWitPrice
  omega

end Witness

/-! ## `decWitNC` -/

section Top

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32)
include hrd hR hσ hS hVn hF hcl hC hL hL32

/-- **The guest decoder's witness's price**: `decWitC` at the five callees' witness functions'
prices. -/
@[expose] def decWitNPrice (G R S F C L DW : ℕ) : ℕ :=
  decWitPrice G R S (458 * F + 214110) (S + 450 * F + 244110) (DW + 15)
    (vsPiPrice R (F + 6) F C L + 30) (47 * F + 46 * R + 998988) + 35

/-- **The guest decoder's witness** (`decWitNC`), the logarithm's tables `D` and the readers'
tables `Tb` given, `da_verify`'s witness at its frame at most `DW` (`dvWitN_cost` at `S = F + 6`):
at most `decWitNPrice G R S F C L DW`. -/
theorem decWitN_cost (D : DiscreteLogTables) (Tb : ReaderTabs) (hTb : ReaderTabsOK Tb)
    (hP : Includes P Decoder.decWitNC.costDeps) (hG : GLogBound P D G) (DW : ℕ)
    (hDW : ∀ args rets : List E, args.length + rets.length ≤ 16 → machineCost P Decoder.dvWitNC.costIdx
      [encodeValue D, .closure Decoder.daAtFrameC.lam0.costIdx [VnV, encodeValue args, encodeValue rets],
        VnV] ≤ DW) :
    machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Tb, σV, rdV, VnV, clV] ≤
      decWitNPrice G R S F C L DW := by
  rw [Decoder.decWitNC.costEq P hP D Tb σ σV hσ rd rdV hrd Vn VnV hVn cl clV hcl]
  have h := decWitC_cost P hrd hR hσ hS
    (fun p ↦ RunsApp.of_spec (Decoder.decWitNC.lam0.costSpec P (by includes) Tb Vn VnV hVn p))
    (wX_cost P hVn hF (by includes) Tb hTb)
    (fun p ↦ RunsApp.of_spec (Decoder.decWitNC.lam1.costSpec P (by includes) Tb σ σV hσ Vn VnV hVn
      p))
    (wS_cost P hVn hF hσ hS (by includes) Tb hTb)
    (fun a b ↦ RunsApp.of_spec (Decoder.decWitNC.lam2.costSpec P (by includes) D Vn VnV hVn a b))
    (wD_cost P hVn D (by includes) DW hDW)
    (fun a ↦ RunsApp.of_spec (Decoder.decWitNC.lam3.costSpec P (by includes) Tb rd rdV hrd Vn VnV
      hVn cl clV hcl a))
    (wV_cost P hVn hF hrd hR hcl hC hL hL32 (by includes) Tb hTb)
    (fun a ↦ RunsApp.of_spec (Decoder.decWitNC.lam4.costSpec P (by includes) rd rdV hrd Vn VnV hVn a))
    (wA_cost P hVn hF hrd hR (by includes)) D (by includes) hG
  unfold decWitNPrice
  omega

end Top

/-! ## `main`'s valuation -/

theorem mainLocs_lt : ∀ x ∈ (Decoder.guestLocs.getD 1 #[]).toList, x < 2 ^ 20 := by
  decide +kernel

theorem mainLoc_lt (i : ℕ) : (Decoder.guestLocs.getD 1 #[]).getD i 0 < 2 ^ 20 := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : (Decoder.guestLocs.getD 1 #[])[i]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact mainLocs_lt x (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))

/-- **`main`'s valuation** (`mainValC`, the cells' locations a literal of the program): a word of
`main`'s frame, for every value, at most `R + 10990`. -/
theorem mainVal_cost (hP : Includes P Decoder.mainValC.costDeps) {rd : Reader} {rdV : MachineValue}
    (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) (v : V) :
    machineCost P Decoder.mainValC.costIdx [rdV, encodeValue v] ≤ R + 10990 := by
  rw [Decoder.mainValC.costEq P hP rd rdV hrd]
  have := wordWith_cost (P := P) (rd := rd) (rdVal := rdV) (hrd := hrd) (R := R) (hR := hR)
    (hW := (by norm_num : 0 < 20)) (hW64 := (by norm_num : 20 < 64)) (by includes) 1
    ((Decoder.guestLocs.getD 1 #[]).getD v.idx 0) (mainLoc_lt _)
  unfold psAt at this
  have hT := Decoder.guestLocsTableC.costEq P (by includes)
  omega

end

end LeanVM.Cost.Bounds.Guest
