module

public import LeanVM.Cost.Bounds.Guest.Top
public import LeanVM.Cost.Bounds.Decoder.DecoderEnds
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Bounds.GuestReplay
public import LeanVM.Cost.Decoder.Top

/-!
# Bounds on the guest decoder's prices: the top

`Cost/Decoder/Top.lean`'s stages, each bounded in the next one's and the replay's prices, the
witness's (`decWitNC` at the frames stage's closures, at most `Wn`) a parameter:

* `discreteLogTables_cost`: the logarithm's baby-step tables, once: at most `103846725`;
* the frames stage's closures: the frame map (`frameClosure_runs`, `frameClosure_cost`: `frameAtAC`'s
  price and `7`), the cursor's length (`cursorClosure_runs`, `cursorClosure_cost`: `cursorLengthC`'s
  and `4`), for `decWitN_cost`;
* **`decTopFrames_cost`**: the witness (at most `Wn`) and the decoding: `framesPrice G R S X Wn`;
* **`decTopStates_cost`**, **`decTopTables_cost`**, **`decTop_cost`**: the entry table (at most `E`),
  `main`'s valuation, the reader (`1472` at `κ ≤ 32`), the replay (`replayStatesOf_cost`), the
  tables built once (the preconditions' at most `Kpre`, the entries' at most `Kpc`, the readers'
  `44537`): at most `(runnerStepPrice κ ℓ + 48)·|states| + E + Kpre + Kpc +
  addressTablesPrice κ ℓ + topConstPrice X Wn`, the address tables
  `(70κ + 374)·2^κ + (70ℓ + 374)·2^ℓ + 48` (`decoderTables_cost`);
* `frameWit_cost`: the witness at the frames stage's closures, `Wn` from the frame map's price `F`
  and the cursor's length's `C`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

variable (P : MachineProgram) {G : ℕ}

/-! ## The baby-step tables -/

/-- The pairs `(lane of b^j, j)` (`powPairsByC`): `284` per pair, `6` at the end. -/
theorem powPairsBy_cost (hP : Includes P Decoder.powPairsByC.costDeps) (b : K) :
    ∀ (n j : ℕ) (y : K), n + j < 2 ^ 64 →
      machineCost P Decoder.powPairsByC.costIdx
        [encodeValue b, encodeValue n, encodeValue j, encodeValue y] ≤ 284 * n + 6
  | 0, j, y, _ => by rw [Decoder.powPairsByC.costEq_zero P hP]
  | n + 1, j, y, h => by
    rw [Decoder.powPairsByC.costEq_succ P hP,
      limbs_of_lt (by omega : n + 1 < 2 ^ 64), limbs_of_lt (by omega : j < 2 ^ 64)]
    have := powPairsBy_cost hP b n (j + 1) (y * b) (by omega)
    omega

open Auto.LeanVM.Extraction.Fast in
/-- **A baby-step table** (`babyTableC`) of `s` steps: at most `70·s·⌈log₂ s⌉ + 374·s + 17`. -/
theorem babyTable_cost (hP : Includes P Decoder.babyTableC.costDeps) (b : K) (s : ℕ)
    (hs : s < 2 ^ 62) :
    machineCost P Decoder.babyTableC.costIdx [encodeValue b, encodeValue s] ≤
      70 * (s * Nat.clog 2 s) + 374 * s + 17 := by
  rw [Decoder.babyTableC.costEq P hP, List.length_mergeSort, length_powPairsBy]
  have h1 := powPairsBy_cost P (by includes) b s 0 1 (by omega)
  have h2 := mergeSortList_cost P (by includes) _ (.closure powTable.c369.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (powTable.c369.lam0.costSpec P (by includes) a b)) 6
    (fun e ↦ e.1 < 2 ^ 64)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [powTable.c369.lam0.costEq P (by includes), limbs_of_lt ha, limbs_of_lt hb]
      omega)
    (powPairsBy b s 0 1) (by rw [length_powPairsBy]; omega)
    (fun e he ↦ (mem_powPairsBy_lt b s 0 1 e he).1)
  rw [length_powPairsBy] at h2
  omega

theorem mul_clog_le {s k : ℕ} (h : s ≤ 2 ^ k) : s * Nat.clog 2 s ≤ s * k :=
  Nat.mul_le_mul_left s (Nat.clog_le_of_le_pow h)

/-- **The seven baby-step tables** (`discreteLogTablesC`), built once: at most `103846725`. -/
theorem discreteLogTables_cost (hP : Includes P Decoder.discreteLogTablesC.costDeps) :
    machineCost P Decoder.discreteLogTablesC.costIdx [] ≤ 103846725 := by
  rw [Decoder.discreteLogTablesC.costEq P hP]
  have h3 := babyTable_cost P (by includes) phBase3 3 (by norm_num)
  have h5 := babyTable_cost P (by includes) phBase5 5 (by norm_num)
  have h17 := babyTable_cost P (by includes) phBase17 17 (by norm_num)
  have h257 := babyTable_cost P (by includes) phBase257 257 (by norm_num)
  have h641 := babyTable_cost P (by includes) phBase641 641 (by norm_num)
  have h4096 := babyTable_cost P (by includes) phBase65537 4096 (by norm_num)
  have h65536 := babyTable_cost P (by includes) phBase6700417 65536 (by norm_num)
  have c3 := mul_clog_le (s := 3) (k := 2) (by norm_num)
  have c5 := mul_clog_le (s := 5) (k := 3) (by norm_num)
  have c17 := mul_clog_le (s := 17) (k := 5) (by norm_num)
  have c257 := mul_clog_le (s := 257) (k := 9) (by norm_num)
  have c641 := mul_clog_le (s := 641) (k := 10) (by norm_num)
  have c4096 := mul_clog_le (s := 4096) (k := 12) (by norm_num)
  have c65536 := mul_clog_le (s := 65536) (k := 16) (by norm_num)
  omega

/-! ## The frames stage's closures -/

section Closures

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
include hrd

/-- The frame map the frames stage passes (`decTopFramesC.lam0`): its spec. -/
theorem frameClosure_runs (hP : Includes P Decoder.decTopFramesC.lam0.costDeps)
    (table : Array (CallKey × K)) (k : ℕ) (a r : List E) (v : V) :
    RunsApp P (.closure Decoder.decTopFramesC.lam0.costIdx [rdV, encodeValue table])
      [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Decoder.frameAtA table rd k a r v)) :=
  RunsApp.of_spec (Decoder.decTopFramesC.lam0.costSpec P hP rd rdV hrd table k a r v)

/-- The frame map the frames stage passes: `frameAtAC`'s price and `7`. -/
theorem frameClosure_cost (hP : Includes P Decoder.decTopFramesC.lam0.costDeps)
    (table : Array (CallKey × K)) (F : ℕ)
    (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
      machineCost P Decoder.frameAtAC.costIdx
      [encodeValue table, rdV, encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
    (k : ℕ) (a r : List E) (v : V) (hk : k < 2 ^ 64) (hlen : a.length + r.length ≤ 16) :
    appCost P (.closure Decoder.decTopFramesC.lam0.costIdx [rdV, encodeValue table])
      [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F + 7 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decTopFramesC.lam0.costEq P hP rd rdV hrd]
  have := hF k a r v hk hlen; omega

end Closures

/-- The cursor's length the frames stage passes (`decTopFramesC.lam1`): its spec. -/
theorem cursorClosure_runs (hP : Includes P Decoder.decTopFramesC.lam1.costDeps)
    (D : DiscreteLogTables) (p q : E) :
    RunsApp P (.closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D])
      [encodeValue p, encodeValue q] (encodeValue (Decoder.cursorLength D p q)) :=
  RunsApp.of_spec (Decoder.decTopFramesC.lam1.costSpec P hP D p q)

/-- The cursor's length the frames stage passes: `cursorLengthC`'s price and `4`. -/
theorem cursorClosure_cost (hP : Includes P Decoder.decTopFramesC.lam1.costDeps)
    (D : DiscreteLogTables) (C : ℕ)
    (hC : ∀ p q : E, machineCost P Decoder.cursorLengthC.costIdx
      [encodeValue D, encodeValue p, encodeValue q] ≤ C) (p q : E) :
    appCost P (.closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D])
      [encodeValue p, encodeValue q] ≤ C + 4 := by
  rw [appCost_fn, List.cons_append, List.nil_append,
    Decoder.decTopFramesC.lam1.costEq P hP]
  have := hC p q; omega


/-- `da_verify`'s witness's price at a frame of the frame map of price `F`: its rows at most
`1024 = 2^10` (`dvWitN_cost_1024`). -/
@[expose] def dvFramePrice (G F : ℕ) : ℕ := (F + 6) + G + dvWitNRowsPrice 10 F (F + 6) + 21

/-- **The witness at the frames stage's closures** (`decWitNC`): the frame map's price at most
`F` (`frameAtAC` on `table`), the cursor's length's at most `C`, its value at most `L ≤ 2^32` at
each child's `verify_sub` frame: at most `decWitNPrice G R S (F + 7) (C + 4) L (dvFramePrice G
(F + 7))`. -/
theorem frameWit_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decWitNC.costDeps)
    (hL0 : Includes P Decoder.decTopFramesC.lam0.costDeps)
    (hL1 : Includes P Decoder.decTopFramesC.lam1.costDeps) (hG : GLogBound P D G) (Tb : ReaderTabs)
    (hTb : ReaderTabsOK Tb) {rd : Reader} {rdV : MachineValue}
    (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) {σ : Val} {σV : MachineValue}
    (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
    {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
    (table : Array (CallKey × K)) (F : ℕ)
    (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
      machineCost P Decoder.frameAtAC.costIdx
      [encodeValue table, rdV, encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
    (C : ℕ) (hC : ∀ p q : E, machineCost P Decoder.cursorLengthC.costIdx
      [encodeValue D, encodeValue p, encodeValue q] ≤ C)
    {Kc N X : ℕ} (hc : CountsWithin D σ Kc N X) (L : ℕ) (hL32 : L ≤ 2 ^ 32)
    (hLk : ∀ c < Decoder.nKidsD D σ,
      Decoder.cursorLength D (Decoder.frameAtA table rd 19 (Decoder.subArgsK rd σ c) [] (.n 27))
        (Decoder.frameAtA table rd 19 (Decoder.subArgsK rd σ c) [] (.n 868)) ≤ L) :
    machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Tb, σV, rdV,
      .closure Decoder.decTopFramesC.lam0.costIdx [rdV, encodeValue table],
      .closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D]] ≤
        decWitNPrice G R S (F + 7) (C + 4) L (dvFramePrice G (F + 7)) Kc N X := by
  have hVn := frameClosure_runs P hrd hL0 table
  have hF' := frameClosure_cost P hrd hL0 table F hF
  have hcl := cursorClosure_runs P hL1 D
  have hC' := cursorClosure_cost P hL1 D C hC
  exact decWitN_cost P hrd hR hσ hS hVn hF' hcl hC' hL32 D Tb hTb hP hG
    (dvFramePrice G (F + 7)) (fun args rets hlen ↦ by
      have := dvWitN_cost_1024 P hVn hF' (daFrame_runs P hVn (by includes) args rets)
        (daFrame_cost P hVn hF' (by includes) args rets hlen) D (by includes) hG
      unfold dvFramePrice; omega) hc hLk

/-! ## The stages -/

/-- The frames stage's price: the witness (at most `Wn`) and the decoding (at most `X` declared
claims a scheme). -/
@[expose] def framesPrice (G R S X Wn : ℕ) : ℕ :=
  Wn + (2 * S + 45) + decStmtPrice G R S X + 15 + 17

/-- **The frames stage** (`decTopFramesC`): the witness at its closures (at most `Wn`), then the
decoding (the seed, the statement), the counts within `K N X`: at most `framesPrice G R S X Wn`. -/
theorem decTopFrames_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decTopFramesC.costDeps)
    (hG : GLogBound P D G) (Rt : ReaderTabs) {rd : Reader} {rdV : MachineValue}
    (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R) {σ : Val} {σV : MachineValue}
    (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
    {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
    (table : Array (CallKey × K)) (Wn : ℕ)
    (hW : machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Rt, σV, rdV,
      .closure Decoder.decTopFramesC.lam0.costIdx [rdV, encodeValue table],
      .closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D]] ≤ Wn) {Kc N X : ℕ}
    (hc : CountsWithin D σ Kc N X) :
    machineCost P Decoder.decTopFramesC.costIdx [encodeValue D, encodeValue Rt, rdV, σV,
      encodeValue table] ≤ framesPrice G R S X Wn := by
  rw [Decoder.decTopFramesC.costEq P hP D Rt rd rdV hrd σ σV hσ table]
  have hO := decoderOutput_cost P (by includes) D σ σV hσ rd rdV hrd
    (Decoder.decWitNStaged D Rt σ rd (Decoder.frameAtA table rd) (Decoder.cursorLength D))
    (2 * S + 45) (decStmtPrice G R S X) (decSeed_cost P hσ hS (by includes))
    (decStmt_cost P hσ hS hrd hR D (by includes) hG X hc.xmssClaims hc.sphincsClaims)
  unfold framesPrice
  omega

/-- **The states stage** (`decTopStatesC`): the entry table (at most `E`), `main`'s valuation
(`R + 10993`), the frames stage (the witness at most `Wn`), the counts within `K N X`: at most
`E + framesPrice G R (R + 10993) X Wn + 20`. -/
theorem decTopStates_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decTopStatesC.costDeps)
    (hG : GLogBound P D G) (T : Array (Option FnPre)) (Pw : Array E) (Rt : ReaderTabs)
    (pcT : SortedMap ℕ (List ℕ)) {rd : Reader} {rdV : MachineValue}
    (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
    {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
    (states : List (Registers K)) (E' Wn : ℕ)
    (hE : machineCost P Decoder.entryArrayTC.costIdx [encodeValue pcT,
      .closure Decoder.decTopStatesC.lam1.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdV],
      encodeValue states, rdV] ≤ E')
    (hW : machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Rt,
      .closure Decoder.decTopStatesC.lam0.costIdx [rdV], rdV,
      .closure Decoder.decTopFramesC.lam0.costIdx
        [rdV, encodeValue (Decoder.entryArrayT pcT (preTestAt D T Pw rd) states rd)],
      .closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D]] ≤ Wn) {Kc N X : ℕ}
    (hc : CountsWithin D (Decoder.mainVal rd) Kc N X) :
    machineCost P Decoder.decTopStatesC.costIdx [encodeValue D, encodeValue T, encodeValue Pw,
      encodeValue Rt, encodeValue pcT, rdV, encodeValue states] ≤
        E' + framesPrice G R (R + 10993) X Wn + 20 := by
  rw [Decoder.decTopStatesC.costEq P hP D T Pw Rt pcT rd rdV hrd states]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.decTopStatesC.lam0.costIdx [rdV])
      [encodeValue v] (encodeValue (Decoder.mainVal rd v)) := fun v ↦
    RunsApp.of_spec (Decoder.decTopStatesC.lam0.costSpec P (by includes) rd rdV hrd v)
  have hS : ∀ v : V, appCost P (.closure Decoder.decTopStatesC.lam0.costIdx [rdV])
      [encodeValue v] ≤ R + 10993 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.decTopStatesC.lam0.costEq P (by includes) rd rdV hrd]
    have := mainVal_cost P (by includes) hrd hR v; omega
  have := decTopFrames_cost P D (by includes) hG Rt hrd hR hσ hS _ Wn hW hc
  omega

/-- The reader closure the tables stage passes (`decTopTablesC.lam0`) at the address table
`powTable κ`, `κ ≤ 32`: its spec. -/
theorem readerClosure_runs (hP : Includes P Decoder.decTopTablesC.lam0.costDeps) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) (a : K) :
    RunsApp P (.closure Decoder.decTopTablesC.lam0.costIdx [encodeValue κ, encodeValue mem,
      encodeValue (powTable κ)]) [encodeValue a]
      (encodeValue (Decoder.memReader (powTable κ) mem a)) :=
  RunsApp.of_spec (Decoder.decTopTablesC.lam0.costSpec P hP mem (powTable κ) a)

/-- The reader closure: at most `1472`. -/
theorem readerClosure_cost (hP : Includes P Decoder.decTopTablesC.lam0.costDeps) {κ : ℕ}
    (hκ : κ ≤ 32) (mem : Vector E (2 ^ κ)) (a : K) :
    appCost P (.closure Decoder.decTopTablesC.lam0.costIdx [encodeValue κ, encodeValue mem,
      encodeValue (powTable κ)]) [encodeValue a] ≤ 1472 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    Decoder.decTopTablesC.lam0.costEq P hP]
  have := memReader_cost_deployed P (by includes) hκ mem a
  omega

/-- The reader closure's value (for the stages' hypotheses). -/
abbrev readerV (κ : ℕ) (mem : Vector E (2 ^ κ)) : MachineValue :=
  .closure Decoder.decTopTablesC.lam0.costIdx [encodeValue κ, encodeValue mem,
    encodeValue (powTable κ)]

/-- **The tables stage** (`decTopTablesC`) at the address tables `decoderTables prog κ`,
`κ ≤ 32`: the replay, then the states stage at the reader's price `1472`. -/
theorem decTopTables_cost (D : DiscreteLogTables) (hP : Includes P Decoder.decTopTablesC.costDeps)
    (hG : GLogBound P D G) (T : Array (Option FnPre)) (Pw : Array E) (Rt : ReaderTabs)
    (pcT : SortedMap ℕ (List ℕ)) (prog : Semantics.Program) {κ : ℕ} (hκ : κ ≤ 32)
    (mem : Vector E (2 ^ κ)) (E' Wn : ℕ)
    (hE : machineCost P Decoder.entryArrayTC.costIdx [encodeValue pcT,
      .closure Decoder.decTopStatesC.lam1.costIdx [encodeValue D, encodeValue T, encodeValue Pw,
        readerV κ mem],
      encodeValue (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem),
      readerV κ mem] ≤ E')
    (hW : machineCost P Decoder.decWitNC.costIdx [encodeValue D, encodeValue Rt,
      .closure Decoder.decTopStatesC.lam0.costIdx [readerV κ mem], readerV κ mem,
      .closure Decoder.decTopFramesC.lam0.costIdx
        [readerV κ mem, encodeValue (Decoder.entryArrayT pcT
          (preTestAt D T Pw (Decoder.memReader (powTable κ) mem))
          (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem)
          (Decoder.memReader (powTable κ) mem))],
      .closure Decoder.decTopFramesC.lam1.costIdx [encodeValue D]] ≤ Wn) {Kc N X : ℕ}
    (hc : CountsWithin D (Decoder.mainVal (Decoder.memReader (powTable κ) mem)) Kc N X) :
    machineCost P Decoder.decTopTablesC.costIdx [encodeValue D, encodeValue T, encodeValue Pw,
      encodeValue Rt, encodeValue pcT, encodeValue (Decoder.decoderTables prog κ),
      encodeValue prog, encodeValue κ, encodeValue mem] ≤
        (runnerStepPrice κ prog.logSize + 48) *
          (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem).length + 18000 +
        E' + framesPrice G 1472 (1472 + 10993) X Wn + 42 := by
  have e : Decoder.decoderTables prog κ = (powTable κ, powTable prog.logSize) := rfl
  rw [e, Decoder.decTopTablesC.costEq P hP D T Pw Rt pcT (powTable κ, powTable prog.logSize) prog
    mem]
  dsimp only
  have h1 := replayStatesOf_cost P (by includes) prog (by omega : κ ≤ 62) mem
  have h2 := decTopStates_cost P D (by includes) hG T Pw Rt pcT
    (readerClosure_runs P (by includes) mem) (readerClosure_cost P (by includes) hκ mem) _ E' Wn
    hE hW hc
  omega

/-- The address tables' price (`decoderTables_cost`): the memory's of `2^κ` words and the
program's of `2^ℓ` instructions, each sorted. -/
@[expose] def addressTablesPrice (κ ℓ : ℕ) : ℕ :=
  (70 * κ + 374) * 2 ^ κ + (70 * ℓ + 374) * 2 ^ ℓ + 48

/-- The top's constant, the address tables apart: the witness (at most `Wn`), the decoding, the
replay's and the other tables' constants. -/
@[expose] def topConstPrice (X Wn : ℕ) : ℕ :=
  framesPrice gLogPrice 1472 (1472 + 10993) X Wn + 42 + 18000 + 103846725 + 117080 +
    44537 + 20000

/-- **The decoder's top** (`decTopC`) on a program of `ℓ` and a memory of `2^κ` words, `κ ≤ 32`:
the tables built once (the logarithm's, the preconditions' at most `Kpre`, the powers, the readers'
`44537`, the entries' at most `Kpc`, the address tables), the replay, the entry table (at most
`E`), the witness (at most `Wn`), the counts within `K N X`: at most `(runnerStepPrice κ ℓ +
48)·|states| + E + Kpre + Kpc + addressTablesPrice κ ℓ + topConstPrice X Wn`. -/
theorem decTop_cost (hP : Includes P Decoder.decTopC.costDeps) (prog : Semantics.Program) {κ : ℕ}
    (hκ : κ ≤ 32) (mem : Vector E (2 ^ κ)) (Kpre Kpc E' Wn : ℕ)
    (hPre : machineCost P Decoder.preTableC.costIdx [] ≤ Kpre)
    (hPc : machineCost P Decoder.pcTableTC.costIdx [] ≤ Kpc)
    (hE : machineCost P Decoder.entryArrayTC.costIdx [encodeValue Decoder.pcTableT,
      .closure Decoder.decTopStatesC.lam1.costIdx [encodeValue discreteLogTables,
        encodeValue preTable, encodeValue genPows, readerV κ mem],
      encodeValue (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem),
      readerV κ mem] ≤ E')
    (hW : machineCost P Decoder.decWitNC.costIdx [encodeValue discreteLogTables,
      encodeValue readerTabs, .closure Decoder.decTopStatesC.lam0.costIdx [readerV κ mem],
      readerV κ mem,
      .closure Decoder.decTopFramesC.lam0.costIdx
        [readerV κ mem, encodeValue (Decoder.entryArrayT Decoder.pcTableT
          (preTestAt discreteLogTables preTable genPows (Decoder.memReader (powTable κ) mem))
          (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem)
          (Decoder.memReader (powTable κ) mem))],
      .closure Decoder.decTopFramesC.lam1.costIdx [encodeValue discreteLogTables]] ≤ Wn)
    {Kc N X : ℕ}
    (hc : CountsWithin discreteLogTables (Decoder.mainVal (Decoder.memReader (powTable κ) mem)) Kc
      N X) :
    machineCost P Decoder.decTopC.costIdx [encodeValue prog, encodeValue κ, encodeValue mem] ≤
      (runnerStepPrice κ prog.logSize + 48) *
          (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem).length +
        E' + Kpre + Kpc + addressTablesPrice κ prog.logSize + topConstPrice X Wn := by
  rw [Decoder.decTopC.costEq P hP]
  have h1 := discreteLogTables_cost P (by includes)
  have h2 := genPows_cost P (by includes)
  have h3 := readerTabs_cost P (by includes)
  have h4 := decoderTables_cost P (by includes) prog κ (by omega)
  have h5 := decTopTables_cost P discreteLogTables (by includes) (gLog_bound P (by includes))
    preTable genPows readerTabs Decoder.pcTableT prog hκ mem E' Wn hE hW hc
  unfold topConstPrice addressTablesPrice
  omega

end

end LeanVM.Cost.Bounds.Guest
