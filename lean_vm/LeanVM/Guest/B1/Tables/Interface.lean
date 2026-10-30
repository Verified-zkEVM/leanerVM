/-
  LeanVM.Guest.B1.Tables.Interface

  B1 of `verify_tables` and `padding_weight`: the specification's programs `verify_tables` runs
  (`busRest`, `tablesSeg`), the layout of the announced sizes (`layoutOf`), what it hands
  `check_opening_terminal` (`TCtx`), and the statements of their relations.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Gkr.Fs
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.Selectors.Interface

/-!
# `verify_tables` (TRIAGE G #51, #52): the interface

`verify_tables(fs0, …, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, block_kappa,
g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count)`
(G:1936-2310) settles the bus against the six tables: it certifies each side's blocks' offsets
(`busLayout`, V:548), certifies every table's log-height to be `max (log2Ceil rows) floor`
(V:1294, by `padding_weight`), decomposes the three GKR leaf values (`accumulateSide`, V:1452),
reads the framework's five column claims, runs the one table sumcheck (`tableSumcheck`, V:1552)
and the public input's binding (`publicInputPhase`, V:2198), and pools every column claim's value.

What it runs is `tablesSeg`: `verifyBusBalance` after the GKR walk (`busRest`), `tablePhase`,
`publicInputPhase`. The bytecode's value is the hinted `bytecode_val` (`FixedClaims`, exported by
`verify_sub`): for every `ev` taking that value at the bus's bytecode point, the run is the
specification's.

* `padding_weight_Spec`: `padding_weight__L{τ}(rows, zeta)` (G:1902-1933) holds exactly when
  `rows` is an integer word `n ≤ 2^τ`; it returns `paddingWeight (zeta[..τ]) n` (V:679) and the
  two words whose `lead = 1 ∧ rest ≠ 0` says `τ = log2Ceil n` (`PadLead`, `PadRest`).
* `verify_tables_Spec`: under `TablesPre` (what `verify_sub` establishes before the call), the
  relation gives `TablesOut`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `padding_weight` -/

/-- `lead` of `padding_weight` at `τ`: `1` at `τ = 0`, else bit `τ` of `n` plus bit `τ - 1`. -/
def PadLead (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + bitE (n.testBit (τ - 1))

/-- `rest` of `padding_weight` at `τ`: `1` at `τ = 0`, else bit `τ` of `n` plus the word of its
bits below `τ - 1`. -/
def PadRest (τ n : ℕ) : E := if τ = 0 then 1 else bitE (n.testBit τ) + eOfNat (n % 2 ^ (τ - 1))

/-- `padding_weight__L{τ}(rows, zeta)`: `rows` is the word of `n ≤ 2^τ`, and the function returns
`pad_n` at the first `τ` words at `zeta`, `lead` and `rest`. -/
def PadWeightOut (τ : ℕ) (rd : Reader) : List E → List E → Prop
  | [rows, zeta], [pad, lead, rest] =>
      ∃ (n : ℕ) (zs : List E), n ≤ 2 ^ τ ∧ rows = eOfNat n ∧ zs.length = τ ∧
        TbReadsAt rd zeta zs ∧ pad = paddingWeight zs n ∧ lead = PadLead τ n ∧
        rest = PadRest τ n
  | _, _ => False

/-- **`padding_weight`** (G:1902-1933; TRIAGE #51) computes `paddingWeight`: soundness. -/
def padding_weight_Spec : Prop :=
  ∀ n < 29, ∀ rd args rets,
    coreProgram.Rel rd (lName "padding_weight" n) args rets → PadWeightOut n rd args rets

/-- The converse, for completeness: every outcome is a relation's. -/
def padding_weight_complete_Spec : Prop :=
  ∀ n < 29, ∀ rd args rets,
    PadWeightOut n rd args rets → coreProgram.Rel rd (lName "padding_weight" n) args rets

/-! ## The layout -/

/-- The tables' log-heights of the row counts (V:1294): `max (log2Ceil rows) floor`. -/
def tableHeightsOf (rows : List ℕ) : List ℕ :=
  List.zipWith (fun r f ↦ max (log2Ceil r) f) rows tableLogFloors

/-- `buildLayout`'s layout (V:1288), its checks left out: the memory's log-size and the tables'
row counts. -/
def layoutOf (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Layout :=
  let logBytecode := Nat.log2 bytecode.length - busBits
  let tableLogHeights := tableHeightsOf tableRows
  let (push, pull, count) := busBlocks tableLogHeights tableRows
  let (placements, stackLog) := placementsOf (columnKappas logMemory logBytecode tableLogHeights)
  ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog, tableLogHeights⟩

/-! ## The programs -/

/-- `verifyBusBalance` after the GKR walk (V:1492-1513), from its challenges, point and values. -/
def busRest (ev : (List K → List E → Prog E)) (layout : Layout) (alphas : List E) (beta : E)
    (point treeValues : List E) : Prog BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← Prog.readN 3
  let memoryFinal ← Prog.readE
  let bytecodeFinal ← Prog.readE
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← ev layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let pcFinal := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- What `verify_tables` runs: the bus after GKR, the table sumcheck and the public input's
binding (V:2307-2311); the bus result and every column claim, the public input's last. -/
def tablesSeg (ev : (List K → List E → Prog E)) (layout : Layout) (publicInput : Digest) (alphas : List E)
    (beta : E) (point treeValues : List E) : Prog (BusResult × List ColumnClaim) := do
  let bus ← busRest ev layout alphas beta point treeValues
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  return (bus, claims ++ publicClaims)

/-! ## The claims -/

/-- `N_CLAIMS`: the column claims the pool holds. -/
abbrev nClaims : ℕ := 165

/-- The claims before the public input's: `N_CLAIMS - 3`. -/
abbrev nPooled : ℕ := nClaims - 3

/-- The claims' global columns, in `tablesSeg`'s order: the bus's, each table's columns, the
public input's. -/
def claimColumns : List ℕ :=
  [memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters] ++
    tables.flatMap (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·)) ++
    [memory0, memory1, memory2]

/-- **`TCtx`**, what `verify_tables` hands `check_opening_terminal` and `verify_keccak`, over
`[zeta, chi, rm, g_bus_mu, g_zc_n, claim_cplen_g]`: the claims are `claimColumns`'s; the bus's lie
on a prefix of the bus point at `zeta`, the tables' on a prefix of the table sumcheck's point
`chis` at `chi`, the public input's at `(rm, 0, …, 0)`; and the first `162` have `g^|point|` in
`claim_cplen_g`. -/
def TCtx (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) :
    List E → Prop
  | [zeta, chi, rm, gmu, gzcn, cplen] =>
      ∃ chis : List E, TbReadsAt rd zeta bus.point ∧ gmu = gen ^ bus.point.length ∧
        TbReadsAt rd chi chis ∧ gzcn = gen ^ chis.length ∧ chis.length ≤ bus.point.length ∧
        claims.length = nClaims ∧ claims.map (·.column) = claimColumns ∧
        ∀ j (p : List E), (claims.map (·.point))[j]? = some p →
          (j < nPooled → LoadHolds rd cplen j (gen ^ p.length)) ∧
          (j < 5 → p = bus.point.take p.length) ∧
          (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
          (nPooled ≤ j → p = rm :: List.replicate ((layout.placement memory0).vars - 1) 0)
  | _ => False

/-! ## `verify_tables` -/

/-- `BLOCK_KAPPA_SRC` (G:118): a bus block's log-height is source `s` of
`[0, log_mem, τ_0, …, τ_5]` … -/
def blockKappaSrc : List ℕ :=
  [0, 1, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 1, 0, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6,
    6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]

/-- … plus `BLOCK_KAPPA_ADJ` (G:119): the bytecode blocks' `19`. -/
def blockKappaAdj (b : ℕ) : ℕ := if b = 2 ∨ b = 56 then 19 else 0

/-- `N_BLOCKS`. -/
abbrev nBlocks : ℕ := 153

/-- `block_kappa` (G:3201-3203): block `b`'s `g^κ` over `kappa_base = [1, g^log_mem, dims…]`. -/
def blockKappaWords (gLogMem : E) (dims : List E) : List E :=
  (List.range nBlocks).map fun b ↦
    (1 :: gLogMem :: dims).getD (blockKappaSrc.getD b 0) 0 * gen ^ blockKappaAdj b

/-- **What `verify_sub` establishes before `verify_tables`**, for the public input `pi`, the
memory's log-size `logMem`, the bus challenges `alphas`, the GKR point and values: the public
input's cells; the point at `zeta`, `g_bus_mu = g^|point|`; `dims_g = [g^log_mem, …]` and
`block_kappa` derived from it; the squares table; `fp_w` the equality weights of `alphas`; the
three GKR values. -/
def TablesPre (pi : Digest) (logMem : ℕ) (alphas point values : List E) (rd : Reader) :
    List E → Prop
  | [_, _, _, _, _, _, pi0, pi1, zeta, gmu, dims, _, bk, sq, fpw, _, _, _, _, cpush, cpull,
      ccount] =>
      (pi0, pi1) = digestScalars pi ∧ TbReadsAt rd zeta point ∧ gmu = gen ^ point.length ∧
      point.length < 33 ∧ 16 ≤ logMem ∧ logMem ≤ 32 ∧
      (∃ ds : List E, ds.length = 6 ∧ TbReadsAt rd dims (gen ^ logMem :: ds) ∧
        TbReadsAt rd bk (blockKappaWords (gen ^ logMem) ds)) ∧
      TbReadsAt rd sq gSquaresList ∧ alphas.length = 4 ∧ TbReadsAt rd fpw (eqKernel alphas) ∧
      values = [cpush, cpull, ccount]
  | _ => False

/-- **`verify_tables`' outcome**: the row counts `rows` are integer words in `table_rows`, and
their log-heights, below `29`, in `dims_g`; for the layout they give and every `ev` taking `bv`
for the bytecode at `(point[..logBytecode], alphas)`, from the carried capacity the words `xs`
at the cursor run `tablesSeg` to the bus result and the `165` column claims, whose values are in
`claim_pool`; `TCtx` holds of them; and the function returns the new capacity, the cursor past
`xs`, `g^n` (the table sumcheck's rounds), `bv` and the public input's challenge. -/
def TablesOut (bytecode : List K) (pi : Digest) (logMem : ℕ) (alphas point values : List E)
    (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, _, _, zeta, gmu, dims, rows, _, _, _, beta, pool, cplen, chi, _, _,
      _], [f0', f1', f2', f3', f4', cur', gzcn, bv, rm] =>
      ∃ (xs cap' : List E) (rowsN : List ℕ) (bus : BusResult) (claims : List ColumnClaim),
        rowsN.length = 6 ∧ TbReadsAt rd rows (rowsN.map eOfNat) ∧
        TbReadsAt rd dims (gen ^ logMem :: (tableHeightsOf rowsN).map (gen ^ ·)) ∧
        (∀ h ∈ tableHeightsOf rowsN, h < 29) ∧ TbReadsAt rd cur xs ∧
        (∀ ev, BytecodeAt ev bytecode
            (point.take (layoutOf bytecode logMem rowsN).logBytecode ++ alphas) bv →
          RunsTo (tablesSeg ev (layoutOf bytecode logMem rowsN) pi alphas beta point values)
            ⟨[f0, f1, f2, f3, f4], []⟩ xs (bus, claims) ⟨cap', []⟩) ∧
        claims.length = nClaims ∧ TbReadsAt rd pool (claims.map (·.value)) ∧
        TCtx rd (layoutOf bytecode logMem rowsN) bus claims [zeta, chi, rm, gmu, gzcn, cplen] ∧
        [f0', f1', f2', f3', f4'] = cap' ∧ cur' = cur * gen ^ xs.length
  | _, _ => False

/-- **`verify_tables` is sound** (G:1936-2312; TRIAGE #52), for the guest's own bytecode words
`bytecode`. Proved for every memory of at most `2^32` words (`verify_tables_holds`). -/
def verify_tables_Spec (bytecode : List K) (rd : Reader) : Prop :=
  ∀ pi logMem alphas point values args rets,
    TablesPre pi logMem alphas point values rd args →
    coreProgram.Rel rd "verify_tables" args rets →
      TablesOut bytecode pi logMem alphas point values rd args rets

end
end LeanVM.Guest.B1.Tables
