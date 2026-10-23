/-
  LeanVM.Guest.B1.Selectors.Interface

  B1 of the selector gadgets: the index MLE, the eq and g-power nibble tables, the bus blocks'
  selectors and the committed columns' selectors. Their mirrors and the statements of their
  relations.
-/

module

public import LeanVM.Guest.B1.Tables.Base

/-!
# The selectors (TRIAGE G #44-50, #68, #69): the interface

A selector is the equality weight of a placement's coordinates above its window
(`Placement.eqAbove`, V:823), together with `g^offset` rebuilt from the same bits, which pins the
bits to the certified offset. The guest computes both a nibble (four coordinates) at a time from
tables (`sel_eq_nibble`, `sel_g_nibble`, `selector_tables`), or a bit at a time
(`block_selector`). Mirrors:

* `eqTable zs zs1`: entry `u < 2^|zs|` is `Π_t (bit t of u ? zs_t : zs1_t)`, the coordinates
  `zs` with their complements `zs1` (the guest holds `1 + z` in a buffer of its own); at
  `zs1 = 1 + zs` it is `eqKernel zs` (V:642).
* `eqLevels zs zs1`: the tables over the first `1, 2, …, |zs|` coordinates, end to end
  (`sel_eq_nibble`, G:1801-1816: level `t` at `2^(t+1) - 2`).
* `gTable gs`: entry `u` is `Π_t gs_t^(bit t of u)` (`sel_g_nibble`, G:1819-1829).
* `nib l j`: the `j`-th nibble of a run, `l[4j .. 4j+4]`.

Statements (`…_Spec`, proved as `…_holds`):

* `index_mle_Spec`: `index_mle__L{n}(zeta)` (G:1788-1797) is `indexMle` (V:692) of the first `n`
  words at `zeta`, `n < 34`;
* `sel_partial_nibble_Spec`: `sel_partial_nibble__L{w}` (G:1832-1837) writes the nibble tables of
  width `w < 4`;
* `shared_selector_tables_Spec`: `shared_selector_tables` (G:1840-1863) writes, for `len_g = g^n`
  (`n < 64`), every nibble's tables of the run of `n` coordinates;
* `block_selector_tab_Spec`: `block_selector_tab__L{n}` (G:1866-1883) reads `n` pinned bits and,
  from those tables, returns their eq weight and `g`-power product;
* `block_selector_Spec`: `block_selector__L{n}` (G:1886-1901) does the same a bit at a time;
* `selector_tables_Spec`, `column_selector_Spec`: `selector_tables(point, point1)` (G:3051-3075)
  writes the opening point's nibble tables over the top coordinates (coordinate `4j + 3 - t` is
  index bit `t`), and `column_selector__L{κ}(offset, sel_eq, sel_g)` (G:3025-3049) certifies
  `offset = g^o` with `o < 2^28` a multiple of `2^κ` and returns the eq weight of `o`'s bits above
  `κ` against the point's coordinates there.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Names of specializations -/

/-- The decimal numerals `0, …, 40`, as literals (so the kernel reads a specialization's name
without `Nat.repr`). -/
def tbDecimals : List String :=
  ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16",
    "17", "18", "19", "20", "21", "22", "23", "24", "25", "26", "27", "28", "29", "30", "31", "32",
    "33", "34", "35", "36", "37", "38", "39", "40"]

/-- The compiler's name of the specialization of `base` at the constant `j ≤ 40`. -/
def lName (base : String) (j : ℕ) : String := base ++ "__L" ++ tbDecimals.getD j (toString j)

/-! ## Mirrors -/

/-- The eq table over coordinates `zs` with complements `zs1`, the first coordinate the lowest
bit. -/
def eqTable (zs zs1 : List E) : List E :=
  (List.zip zs zs1).foldl (fun out p ↦ out.map (· * p.2) ++ out.map (· * p.1)) [1]

/-- The eq tables over the first `1, …, |zs|` coordinates, end to end. -/
def eqLevels (zs zs1 : List E) : List E :=
  (List.range zs.length).flatMap fun t ↦ eqTable (zs.take (t + 1)) (zs1.take (t + 1))

/-- The `g`-power table: entry `u` is the product of the `gs_t` at the bits `t` of `u`. -/
def gTable (gs : List E) : List E := gs.foldl (fun out g ↦ out ++ out.map (· * g)) [1]

/-- Nibble `j` of a run: its words `4j .. 4j + 3`. -/
def nib (l : List E) (j : ℕ) : List E := (l.drop (4 * j)).take 4

/-- Bit `i` of `o`, as a `0/1` word. -/
def bitOf (o i : ℕ) : E := bitE (o.testBit i)

/-! ## `index_mle` -/

/-- `index_mle__L{n}(zeta)`: the index MLE of the first `n` words at `zeta`. -/
def IndexMleOut (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [zeta], [v] => ∃ zs : List E, zs.length = n ∧ TbReadsAt rd zeta zs ∧ v = indexMle zs
  | _, _ => False

/-- **`index_mle`** (G:1788-1797; TRIAGE #44) computes `indexMle`: soundness. -/
def index_mle_Spec : Prop :=
  ∀ n < 34, ∀ rd args rets,
    coreProgram.Rel rd (lName "index_mle" n) args rets → IndexMleOut n rd args rets

/-- The converse, for completeness: every outcome is a relation's. -/
def index_mle_complete_Spec : Prop :=
  ∀ n < 34, ∀ rd args rets,
    IndexMleOut n rd args rets → coreProgram.Rel rd (lName "index_mle" n) args rets

/-! ## The nibble tables -/

/-- `sel_partial_nibble__L{w}(eq_out, g_out, z, z1, gs)`: the `w` coordinates at `z`, their
complements at `z1` and the `w` shares at `gs`; their eq levels at `eq_out` and, for `w > 0`,
their `g`-power table at `g_out`; the return word `0`. -/
def SelPartialOut (w : ℕ) (rd : Reader) : List E → List E → Prop
  | [eqo, go, z, z1, gs], [r] =>
      r = 0 ∧ ∃ zs zs1 gl : List E, zs.length = w ∧ zs1.length = w ∧ gl.length = w ∧
        TbReadsAt rd z zs ∧ TbReadsAt rd z1 zs1 ∧ TbReadsAt rd gs gl ∧
        TbReadsAt rd eqo (eqLevels zs zs1) ∧ TbReadsAt rd go (if w = 0 then [] else gTable gl)
  | _, _ => False

/-- **`sel_partial_nibble`** (G:1801-1837; TRIAGE #45-47) writes its nibble's tables: soundness. -/
def sel_partial_nibble_Spec : Prop :=
  ∀ n < 4, ∀ rd args rets,
    coreProgram.Rel rd (lName "sel_partial_nibble" n) args rets → SelPartialOut n rd args rets

/-- The converse, for completeness: every outcome is a relation's. -/
def sel_partial_nibble_complete_Spec : Prop :=
  ∀ n < 4, ∀ rd args rets,
    SelPartialOut n rd args rets → coreProgram.Rel rd (lName "sel_partial_nibble" n) args rets

/-- The nibble tables of a run of `n` coordinates `zs` (complements `zs1`, shares `gs`): nibble
`j`'s eq levels at `eq_tab·g^(32j)` and its `g`-power table at `g_tab·g^(16j)`
(`SEL_TAB_EQ_STRIDE = 32`). -/
def RunTables (rd : Reader) (eqt gt : E) (n : ℕ) (zs zs1 gs : List E) : Prop :=
  ∀ j < (n + 3) / 4, TbReadsAt rd (eqt * gen ^ (32 * j)) (eqLevels (nib zs j) (nib zs1 j)) ∧
    TbReadsAt rd (gt * gen ^ (16 * j)) (gTable (nib gs j))

/-- `shared_selector_tables(eq_tab, g_tab, zeta_hi, zeta1_hi, gsq_hi, len_g)`: `len_g = g^n`,
`n < 64`, and for the `n` coordinates, complements and shares read at `zeta_hi`, `zeta1_hi`,
`gsq_hi`, their nibble tables are written. -/
def SharedSelOut (rd : Reader) : List E → List E → Prop
  | [eqt, gt, z, z1, gsq, lenG], [] =>
      ∃ n < 64, lenG = gen ^ n ∧ ∀ zs zs1 gs : List E, zs.length = n → zs1.length = n →
        gs.length = n → TbReadsAt rd z zs → TbReadsAt rd z1 zs1 → TbReadsAt rd gsq gs →
        RunTables rd eqt gt n zs zs1 gs
  | _, _ => False

/-- **`shared_selector_tables`** (G:1840-1863; TRIAGE #48) is sound. -/
def shared_selector_tables_Spec : Prop :=
  ∀ rd args rets, coreProgram.Rel rd "shared_selector_tables" args rets → SharedSelOut rd args rets

/-- The converse, for completeness: `n < 64` coordinates, complements and shares at `zeta_hi`,
`zeta1_hi`, `gsq_hi`, with their nibble tables at `eq_tab`, `g_tab`, give the relation. -/
def shared_selector_tables_complete_Spec : Prop :=
  ∀ (rd : Reader) (eqt gt z z1 gsq : E) (n : ℕ) (zs zs1 gs : List E), n < 64 →
    zs.length = n → zs1.length = n → gs.length = n →
    TbReadsAt rd z zs → TbReadsAt rd z1 zs1 → TbReadsAt rd gsq gs →
    RunTables rd eqt gt n zs zs1 gs →
    coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ n] []

/-! ## The bus blocks' selectors -/

/-- The eq weight of bits against coordinates with their complements: `Π (b ? z : z1)`. -/
def bitsEq (bs : List Bool) (zs zs1 : List E) : E :=
  ((List.zip bs (List.zip zs zs1)).map fun p ↦ if p.1 then p.2.1 else p.2.2).prod

/-- The `g`-power product of bits: `Π gs_t^(b_t)`. -/
def bitsPow (bs : List Bool) (gs : List E) : E :=
  ((List.zip bs gs).map fun p ↦ if p.1 then p.2 else 1).prod

/-- `block_selector_tab__L{n}(sel_bits, eq_tab, g_tab)`: `n` bits pinned at `sel_bits`; for any run
whose tables are at `eq_tab`, `g_tab`, the function returns their eq weight and `g`-power
product. -/
def BlockSelTabOut (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [sb, eqt, gt], [eq, rb] =>
      ∃ bs : List Bool, bs.length = n ∧ TbReadsAt rd sb (bs.map bitE) ∧
        ∀ zs zs1 gs : List E, zs.length = n → zs1.length = n → gs.length = n →
          RunTables rd eqt gt n zs zs1 gs → eq = bitsEq bs zs zs1 ∧ rb = bitsPow bs gs
  | _, _ => False

/-- **`block_selector_tab`** (G:1866-1883; TRIAGE #49) is sound. -/
def block_selector_tab_Spec : Prop :=
  ∀ n < 34, ∀ rd args rets,
    coreProgram.Rel rd (lName "block_selector_tab" n) args rets → BlockSelTabOut n rd args rets

/-- The converse, for completeness: `n` bits pinned at `sel_bits` and the nibble tables of a run
of `n` coordinates, complements and shares at `eq_tab`, `g_tab` give the relation, returning the
bits' eq weight and `g`-power product. -/
def block_selector_tab_complete_Spec : Prop :=
  ∀ n < 34, ∀ (rd : Reader) (sb eqt gt : E) (bs : List Bool) (zs zs1 gs : List E),
    bs.length = n → zs.length = n → zs1.length = n → gs.length = n →
    TbReadsAt rd sb (bs.map bitE) → RunTables rd eqt gt n zs zs1 gs →
    coreProgram.Rel rd (lName "block_selector_tab" n) [sb, eqt, gt]
      [bitsEq bs zs zs1, bitsPow bs gs]

/-- `block_selector__L{n}(sel_bits, zeta1_hi, idxc_hi)`: `n` bits pinned at `sel_bits`, the
complements `zs1` at `zeta1_hi` and the weights `cs` at `idxc_hi`; the function returns
`Π (b + z1)` and `Π (1 + b·c)`. -/
def BlockSelOut (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [sb, z1, ic], [eq, rb] =>
      ∃ (bs : List Bool) (zs1 cs : List E), bs.length = n ∧ zs1.length = n ∧ cs.length = n ∧
        TbReadsAt rd sb (bs.map bitE) ∧ TbReadsAt rd z1 zs1 ∧ TbReadsAt rd ic cs ∧
        eq = ((List.zip bs zs1).map fun p ↦ bitE p.1 + p.2).prod ∧
        rb = ((List.zip bs cs).map fun p ↦ 1 + bitE p.1 * p.2).prod
  | _, _ => False

/-- **`block_selector`** (G:1886-1901; TRIAGE #50) computes its selector: soundness. -/
def block_selector_Spec : Prop :=
  ∀ n < 34, ∀ rd args rets,
    coreProgram.Rel rd (lName "block_selector" n) args rets → BlockSelOut n rd args rets

/-- The converse, for completeness: every outcome is a relation's. -/
def block_selector_complete_Spec : Prop :=
  ∀ n < 34, ∀ rd args rets,
    BlockSelOut n rd args rets → coreProgram.Rel rd (lName "block_selector" n) args rets

/-! ## The committed columns' selectors -/

/-- `SEL_NIBBLES`: the opening point's `28 = MAX_STACK_LOG` coordinates, four to a nibble. -/
abbrev selNibbles : ℕ := 7

/-- Nibble `j` of the opening point read from its top: coordinates `4j + 3, 4j + 2, 4j + 1, 4j`. -/
def topNib (p : List E) (j : ℕ) : List E := (nib p j).reverse

/-- `g^(2^(4j + 3 - t))`, `t < 4`: the shares of nibble `j`'s index bits. -/
def topShares (j : ℕ) : List E := (List.range 4).map fun t ↦ gen ^ 2 ^ (4 * j + 3 - t)

/-- The opening point's eq tables (`selector_tables`): nibble `j`'s eq levels over its top
coordinates at `sel_eq·g^(30j)` (`SEL_EQ_STRIDE = 30`). -/
def EqTabsAt (rd : Reader) (se : E) (p p1 : List E) : Prop :=
  ∀ j < selNibbles, TbReadsAt rd (se * gen ^ (30 * j)) (eqLevels (topNib p j) (topNib p1 j))

/-- The `g`-power tables (`selector_tables`): nibble `j`'s at `sel_g·g^(16j)`. -/
def GTabsAt (rd : Reader) (sg : E) : Prop :=
  ∀ j < selNibbles, TbReadsAt rd (sg * gen ^ (16 * j)) (gTable (topShares j))

/-- The opening point's tables: both. -/
def SelTabsAt (rd : Reader) (se sg : E) (p p1 : List E) : Prop :=
  EqTabsAt rd se p p1 ∧ GTabsAt rd sg

/-- `selector_tables(point, point1)`: for the point and its complements read at `point`,
`point1` (`28` coordinates), the returned buffers hold their tables. -/
def SelTablesOut (rd : Reader) : List E → List E → Prop
  | [pt, pt1], [se, sg] =>
      ∀ p p1 : List E, p.length = 28 → p1.length = 28 → TbReadsAt rd pt p → TbReadsAt rd pt1 p1 →
        SelTabsAt rd se sg p p1
  | _, _ => False

/-- **`selector_tables`** (G:3051-3075; TRIAGE #69) is sound. -/
def selector_tables_Spec : Prop :=
  ∀ rd args rets, coreProgram.Rel rd "selector_tables" args rets → SelTablesOut rd args rets

/-- `column_selector__L{κ}(offset, sel_eq, sel_g)`: with the `g`-power tables at `sel_g`,
`offset = g^o` with `o < 2^28` a multiple of `2^κ`, and for any point whose eq tables are at
`sel_eq` the selector is the eq weight of `o`'s bits `κ .. 27` against the point's coordinates
there. -/
def ColSelOut (κ : ℕ) (rd : Reader) : List E → List E → Prop
  | [off, se, sg], [sel] =>
      GTabsAt rd sg → ∃ o : ℕ, o < 2 ^ 28 ∧ 2 ^ κ ∣ o ∧ off = gen ^ o ∧
        ∀ p p1 : List E, p.length = 28 → p1.length = 28 → EqTabsAt rd se p p1 →
          sel = bitsEq ((List.range (28 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ)
            (p1.drop κ)
  | _, _ => False

/-- **`column_selector`** (G:3025-3049; TRIAGE #68) is sound, `κ ≤ 28`. -/
def column_selector_Spec : Prop :=
  ∀ κ < 29, ∀ rd args rets,
    coreProgram.Rel rd (lName "column_selector" κ) args rets → ColSelOut κ rd args rets

/-- The converse, for completeness: an offset `g^o`, `o < 2^28` a multiple of `2^κ`, and the opening
point's tables at `sel_eq`, `sel_g` give the relation, returning the eq weight of `o`'s bits above
`κ`. -/
def column_selector_complete_Spec : Prop :=
  ∀ κ < 29, ∀ (rd : Reader) (o : ℕ) (se sg : E) (p p1 : List E), o < 2 ^ 28 → 2 ^ κ ∣ o →
    p.length = 28 → p1.length = 28 → EqTabsAt rd se p p1 → GTabsAt rd sg →
    coreProgram.Rel rd (lName "column_selector" κ) [gen ^ o, se, sg]
      [bitsEq ((List.range (28 - κ)).map fun i ↦ o.testBit (κ + i)) (p.drop κ) (p1.drop κ)]

end
end LeanVM.Guest.B1.Tables
