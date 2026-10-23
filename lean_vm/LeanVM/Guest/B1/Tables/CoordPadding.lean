/-
  LeanVM.Guest.B1.Tables.CoordPadding

  The guest's baked `COORD_PADDING` is the value of each table block's coordinate on its table's
  padding row (`Table.padding`), the `KECCAK` table's through `keccakF_zero`.
-/

module

public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.Data.Source
public import LeanVM.Guest.Value.KeccakConst

/-!
# `COORD_PADDING` (G:2140-2158)

`verify_tables` weighs a table block's padding rows by `β + 1 + Σ_i w_i · COORD_PADDING[c_i]`,
where the specification's `accumulateSide` takes `form.evaluate padding + 1` (V:634): the two agree
when every baked `COORD_PADDING` is its coordinate's value on the table's padding row. That row is
zero but for the `KECCAK` table's output lanes, `keccakF` of the zero state (`keccakF_zero`), so
the check is a kernel evaluation once `keccakF` of zeros is replaced by its value.

* `pushBlockCoords`, `countBlockCoords`: the specification's table blocks of the push and count
  sides, in block order (`busBlocks`, V:1240): their owners and coordinates;
* `padding_eq`: `Table.padding` with `keccakF` of zeros replaced by its value (`keccakF_zero`);
* `coordPadding_Spec`: for every table block `b` of the side (global index `3 + j`, resp.
  `108 + j`), `BLOCK_TABLE[b]` is its owner, `BLOCK_COORD_COUNT[b]` its arity, and
  `COORD_PADDING[BLOCK_COORD_OFF[b] + i]` the value of coordinate `i` on the owner's padding row.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Entry `i` of a baked constant array (its low word). -/
def bakedAt (a : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (a.getD i (0, 0, 0)).1

/-- The push side's table blocks: owner and coordinates, in block order. -/
def pushBlockCoords : List (ℕ × List Form) :=
  tables.flatMap fun t ↦ t.flushes.push.map fun c ↦ (t.opcode, c)

/-- The count side's blocks: owner and coordinates, in block order. -/
def countBlockCoords : List (ℕ × List Form) :=
  tables.flatMap fun t ↦ t.countColumns.map fun l ↦ (t.opcode, [Form.col l])

/-- `Table.padding` with `keccakF` of zeros evaluated. -/
def paddingRow (t : Table) : List E :=
  if t.opcode = opKeccak then
    t.columns.map fun name ↦
      if name ∈ keccakOutputs then
        eOfNat (Keccak.lane Keccak.keccakFZero (keccakOutputs.idxOf name)).toNat
      else 0
  else t.columns.map fun _ ↦ 0

theorem padding_eq (t : Table) : t.padding = paddingRow t := by
  unfold Table.padding paddingRow
  rw [show (Vector.replicate 25 0 : KState) = Keccak.zeroState from rfl, Keccak.keccakF_zero]

/-- What the baked arrays say of a side's table blocks, against the specification's blocks
`blocks` from global index `start`. -/
def CoordPaddingOk (start : ℕ) (blocks : List (ℕ × List Form)) : Prop :=
  ∀ j < blocks.length,
    bakedAt Data.arr_BLOCK_TABLE (start + j) = (blocks.getD j default).1 ∧
    bakedAt Data.arr_BLOCK_COORD_COUNT (start + j) = (blocks.getD j default).2.length ∧
    ∀ i < (blocks.getD j default).2.length,
      eOfNat (bakedAt Data.arr_COORD_PADDING
          (bakedAt Data.arr_BLOCK_COORD_OFF (start + j) + i)) =
        ((blocks.getD j default).2.getD i default).evaluate
          ((paddingRow (tables.getD (blocks.getD j default).1 default)).getD · 0)

/-- **The `COORD_PADDING` tie**, on the push side (global blocks `3 .. 53`) and the count side
(`108 .. 152`). Not a kernel evaluation: `E`'s products do not reduce in the kernel, so the proof
goes through `ofK` (every value here is in `K`); it lands with `verify_tables_holds`. -/
def coordPadding_Spec : Prop := CoordPaddingOk 3 pushBlockCoords ∧ CoordPaddingOk 108 countBlockCoords

end
end LeanVM.Guest.B1.Tables
