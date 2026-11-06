import LeanerVMTests.Arithmetization.Statement

/-!
# Fixture: a program with a `JUMP` in its sentinel slot

The program, the rows and the witness of the sentinel tests
(`LeanerVMTests.Arithmetization.Sentinel`), without their proofs, so that an executable can prove
the witness without elaborating the tests.

**The program** `sentProg` is the statement tests' fixture rearranged. Its run pins two cells by
`SET_CONSTANT` (slots `0`, `1`), multiplies (slot `2`), then jumps (slot `3`) on the public word
`input₀` to the pinned destination `g^31`, the sentinel counter, and the pinned frame `g^5`. The
`XOR` and `DEREF` fill blocks share one closing `JUMP` (slots `4`, `5`, `6`), so that the `JUMP`
table keeps four rows, and the sentinel slot `31` holds a `JUMP` in frame `g^5` to `(g^31, 1)`.
The image and the data are the fixture's, the `BLAKE2S` fill rows too.

**The witness** `sentW` has a row for every step, the sentinel's among them; the state pair
balances with the walk `(1, 1) → (g, 1) → (g^2, 1) → (g^3, 1) → (g^31, g^5) → (g^31, 1)`.
-/

namespace LeanerVMTests.Arithmetization.Sentinel

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVMTests.Arithmetization.Statement
open Air.Flat (Component EnsembleWitness)

/-! ## The program -/

/-- The fixture's program with its run pinned to the sentinel at frame `g^5` and a `JUMP` in its
sentinel slot. -/
def sentProg : Program :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (gpow 11) (cellK (gpow 5))
    | 1 => .setConstant (gpow 27) (cellK (gpow 31))
    | 2 => .mulNative (gpow 2) (gpow 3) (gpow 4)
    | 3 => .jump 1 (gpow 27) (gpow 11)
    | 4 => .xor 1 1 1
    | 5 => .deref (gpow 6) 1 1 .cell
    | 6 => .jump g (gpow 2) (gpow 6)
    | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      .blake2s ![gpow 2, gpow 3, gpow 4, gpow 5] 1 (gpow 6) (gpow 8)
    | 16 => .jump (gpow 9) (gpow 10) (gpow 11)
    | 31 => .jump g (gpow 22) g
    | _ => .xor 1 1 1⟩

/-! ## The rows -/

/-- Slot `0`, `SET_CONSTANT g^11 ← g^5`: the fourth read of cell `g^11`. -/
def setRowS0 : SetRow K :=
  ⟨gpow 0, 1, gpow 11,
    #v[(cellK (gpow 5)).limb 0, (cellK (gpow 5)).limb 1, (cellK (gpow 5)).limb 2], g ^ 3, 1⟩

/-- Slot `1`, `SET_CONSTANT g^27 ← g^31`: the third read of cell `g^27`. -/
def setRowS1 : SetRow K :=
  ⟨gpow 1, 1, gpow 27,
    #v[(cellK (gpow 31)).limb 0, (cellK (gpow 31)).limb 1, (cellK (gpow 31)).limb 2], g ^ 2, 1⟩

/-- Slot `2`, `MUL_NATIVE`: the first read of each of its three cells. -/
def mulRowS : MulRow K :=
  ⟨gpow 2, 1, gpow 2, gpow 3, gpow 4, #v[mulX.limb 0, mulX.limb 1, mulX.limb 2],
    #v[mulY.limb 0, mulY.limb 1, mulY.limb 2], 1, 1, 1, 1⟩

/-- Slot `3`, the run's `JUMP` to `(g^31, g^5)`: the condition `1` at `g^0`, the destination at
`g^27`, the frame word `g^5` at `g^11` (its third read). -/
def jumpRowA : JumpRow K :=
  ⟨gpow 3, 1, 1, gpow 27, gpow 11, 1, gpow 31, gpow 5, 1, 1, g ^ 2, 1⟩

/-- Slot `5`, the fixture's `DEREF` fill row one slot earlier. -/
def derefRowS : DerefRow K :=
  ⟨gpow 5, gpow 5, gpow 6, 1, 1, 0, 0, gpow 5, #v[0, 0, 0], g, g ^ 4, g ^ 3, 1⟩

/-- Slot `6`, the `JUMP` back to slot `4` closing both fill blocks. -/
def jumpRowB : JumpRow K :=
  ⟨gpow 6, gpow 5, g, gpow 2, gpow 6, 1, gpow 4, gpow 5, 1, 1, 1, 1⟩

/-- Slot `31`, the sentinel's `JUMP` in frame `g^5` to `(g^31, 1)`: the condition and the frame
word `1` at `g^6`, the destination `g^31` at `g^27`. -/
def jumpRowS : JumpRow K :=
  ⟨gpow 31, gpow 5, g, gpow 22, g, 1, gpow 31, 1, g, g, g ^ 2, 1⟩

/-- The finalize counts: cells `0`, `2` and `3` read once, cell `6` three times, cell `11` four
times, cell `27` three times, cells `8`, `26` and `28` never; the rest as in the fixture. -/
def sentCnt (i : ℕ) : K :=
  if i = 0 ∨ i = 2 ∨ i = 3 then g else if i = 6 ∨ i = 27 then g ^ 3 else if i = 11 then g ^ 4
  else if i = 8 ∨ i = 26 ∨ i = 28 then 1 else memCnt i

theorem sentCnt_of_ge {i : ℕ} (h : touched ≤ i) : sentCnt i = 1 := by
  have h29 : 29 ≤ i := h
  unfold sentCnt
  split_ifs <;> first | omega | exact memCnt_of_ge h29

/-- The bytecode finalize counts: slots `0` to `6`, `8` to `16` and `31` executed once. -/
def sentBcCnt (i : Fin (2 ^ sentProg.logSize)) : K :=
  if (i : ℕ) = 7 then 1 else if (i : ℕ) = 31 then g else bcCnt i

/-! ## The witness -/

def setTS : Air.Flat.Table K :=
  mkT setTable (size SetRow) ([setRowS0, setRowS1].map rawRow) (rows_size [setRowS0, setRowS1])

def mulTS : Air.Flat.Table K :=
  mkT mulTable (size MulRow) ([mulRowS].map rawRow) (rows_size [mulRowS])

def derefTS : Air.Flat.Table K :=
  mkT derefTable (size DerefRow) ([derefRowS].map rawRow) (rows_size [derefRowS])

def jumpTS : Air.Flat.Table K :=
  mkT jumpTable (size JumpRow + 2) ([jumpRowA, jumpRowB, jumpRow16, jumpRowS].map jumpRaw)
    (jumpRaw_size [jumpRowA, jumpRowB, jumpRow16, jumpRowS])

def bcTS : Air.Flat.Table K :=
  mkT bytecodeTable (size BytecodeRow)
    (List.ofFn fun i ↦ (toElements (bytecodeRowOf sentProg i (sentBcCnt i))).toArray)
    fun r hr ↦ by
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact Vector.size_toArray _

/-- A witness of the ensemble of `sentProg` over the fixture's data and input. -/
def mkWS (ts : List (Air.Flat.Table K))
    (hlen : (leanIsaEnsemble sentProg).tables.length = ts.length := by rfl)
    (hc : ∀ i (hi : i < (leanIsaEnsemble sentProg).tables.length),
      (leanIsaEnsemble sentProg).tables[i] = (ts[i]'(hlen ▸ hi)).component := by
        intro i hi
        have hi' : i < 8 := hi
        interval_cases i <;> rfl)
    (hd : ∀ t ∈ ts, t.data = fillData := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) :
    EnsembleWitness (leanIsaEnsemble sentProg) :=
  ⟨ts, fillData, PublicIO.ofInput mulInput, hlen, hc, hd⟩

/-- The witness: a row for every step of the walk to the sentinel and back to `(g^31, 1)`. -/
def sentW : EnsembleWitness (leanIsaEnsemble sentProg) :=
  mkWS [xorT, mulTS, setTS, derefTS, jumpTS, blakeT, memT sentCnt, bcTS]

end LeanerVMTests.Arithmetization.Sentinel
