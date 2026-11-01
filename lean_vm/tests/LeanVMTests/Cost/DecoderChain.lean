import LeanVM.Cost.Decoder.Memory

/-!
# Tests: the guest decoder's compiled chain on small inputs

Each compiled reader run on a small input, its output the statement's encoding of the Lean
function's value: the cells' digests and claims, a signature claim's bit vectors, the memory's
cells through a reader (a compiled closure), `main`'s valuation, the seed.
-/

namespace LeanVMTests.Cost.DecoderChain

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Main LeanVM.Protocol.Verifier

/-- A compiled function's value on `vs`, in the program of the bodies `deps`. -/
def runOn (deps : List (ℕ × Term)) (i : ℕ) (vs : List MachineValue) : Option MachineValue :=
  (evaluateFunctionBody (MachineProgram.ofList deps) 100000 i vs).map (·.1)

/-- The discrete logarithm's baby-step tables, built in Lean and passed in as a value. -/
def dlTables : MachineValue := encodeValue LeanVM.Extraction.Fast.discreteLogTables

def cA : E := E.ofLimbs (K.ofLane 0x0123456789abcdef) (K.ofLane 0xfedcba9876543210) 0
def cB : E := E.ofLimbs (K.ofLane 7) (K.ofLane 0xffffffffffffffff) (K.ofLane 3)

#guard runOn digestOfCellsC.costDeps digestOfCellsC.costIdx [encodeValue cA, encodeValue cB] ==
  some (encodeValue (Main.digestOfCells cA cB))

def cells : List E := (List.range 24).map fun i ↦ (gen ^ i : E)
#guard runOn deferOfCellsC.costDeps deferOfCellsC.costIdx [encodeValue cells] ==
  some (encodeValue (deferOfCells cells))
#guard runOn fixedOfCellsC.costDeps fixedOfCellsC.costIdx [encodeValue cells] ==
  some (encodeValue (fixedOfCells cells))

#guard runOn xmssClaimOfC.costDeps xmssClaimOfC.costIdx
  [encodeValue cA, encodeValue cB, encodeValue cB, encodeValue cA] ==
  some (encodeValue (Sig.xmssClaimOf cA cB cB cA))
#guard runOn sphincsClaimOfC.costDeps sphincsClaimOfC.costIdx
  [encodeValue cB, encodeValue cA, encodeValue cA, encodeValue cB] ==
  some (encodeValue (Sig.sphincsClaimOf cB cA cA cB))

/-- A small memory: the word at `g^i` is `g^(i+1)` (as `E`) for `i < 64`. -/
def smallReader (a : K) : Option E :=
  ((List.range 64).find? fun i ↦ a == LeanVM.Parameters.gpow i).map fun i ↦ (gen ^ (i + 1) : E)
cost_compile smallReaderC := smallReader

/-- The reader as a closure value. -/
def rdVal : MachineValue := .closure smallReaderC.costIdx []

-- (`cellAt` and the readers are `noncomputable` in Lean: their values are written out.)
#guard runOn (cellAtC.costDeps ++ smallReaderC.costDeps) cellAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (3 : ℕ)] == some (encodeValue (gen ^ 4 : E))
#guard runOn (cellAtC.costDeps ++ smallReaderC.costDeps) cellAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (70 : ℕ)] == some (encodeValue (0 : E))
#guard runOn (readCellsC.costDeps ++ smallReaderC.costDeps) readCellsC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (5 : ℕ)] ==
  some (encodeValue ((List.range 5).map fun i ↦ (gen ^ (i + 1) : E)))
#guard runOn (xmssAtC.costDeps ++ smallReaderC.costDeps) xmssAtC.costIdx
  [rdVal, encodeValue (1 : E), encodeValue (2 : ℕ)] ==
  some (encodeValue (Sig.xmssClaimOf (gen ^ 9) (gen ^ 10) (gen ^ 11) (gen ^ 12)))

#guard runOn (mainValC.costDeps ++ smallReaderC.costDeps) mainValC.costIdx
  [rdVal, encodeValue (V.n 47)] == some (encodeValue (mainVal smallReader (V.n 47)))

/-- A valuation of `main`: every value `1`. -/
def oneSigma (_ : V) : E := 1
cost_compile oneSigmaC := oneSigma

def sigmaVal : MachineValue := .closure oneSigmaC.costIdx []

#guard runOn (decSeedC.costDeps ++ oneSigmaC.costDeps) decSeedC.costIdx [sigmaVal] ==
  some (encodeValue (decSeed oneSigma))

-- The batching's hints: the rounds at `bc_sumcheck_msgs = 1`, the cells `g^0, g^1, …`.
#guard runOn (aggHintsC.costDeps ++ oneSigmaC.costDeps ++ smallReaderC.costDeps) aggHintsC.costIdx
  [rdVal, sigmaVal] == some (encodeValue (⟨(List.range 23).map fun k ↦
    ((gen ^ (2 * k + 1) : E), (gen ^ (2 * k + 2) : E)), 1⟩ : LeanVM.Node.BatchingHints))

-- The statement off `main`'s frame: no declared claim (`gLog 1 = 0`), the DA digest at slot `0`
-- of `da_digests = 1`, the deferred claim at `defer_stmt = 1`. (`decStmt` is `noncomputable` in
-- Lean: its value is written out.)
#guard runOn (decStmtC.costDeps ++ oneSigmaC.costDeps ++ smallReaderC.costDeps) decStmtC.costIdx
  [dlTables, sigmaVal, rdVal] == some (encodeValue (⟨⟨[], [], Main.digestOfCells (gen ^ 1) (gen ^ 2)⟩,
    deferOfCells ((List.range 24).map fun i ↦ (gen ^ (i + 1) : E))⟩ : LeanVM.Node.NodeStatement))

/-- A valuation of `main` whose every value is `g^7`. -/
def sevenSigma (_ : V) : E := LeanVM.Parameters.ofK (LeanVM.Parameters.gpow 7)
cost_compile sevenSigmaC := sevenSigma

-- The number of children, `gLog (g^7)`, by the compiled discrete logarithm, its tables given.
#guard runOn (nKidsC.costDeps ++ sevenSigmaC.costDeps) nKidsC.costIdx
  [dlTables, .closure sevenSigmaC.costIdx []] == some (encodeValue (7 : ℕ))

/-- A memory of `2^3` words, word `i` at address `g^i` being `g^i` (as `E`). -/
def mem8 : LeanVM.Semantics.MemoryImage 3 := fun i ↦ LeanVM.Parameters.ofK (LeanVM.Parameters.gpow i.val)
cost_compile mem8C := mem8

-- The reader through the extractor's address table: the table, `κ`, the memory (a closure), the
-- address.
#guard runOn (readTableC.costDeps ++ mem8C.costDeps) readTableC.costIdx
  [encodeValue (LeanVM.Extraction.Fast.powTable 3), encodeValue (3 : ℕ), .closure mem8C.costIdx [],
    encodeValue (LeanVM.Parameters.gpow 5)] ==
  some (encodeValue (some (LeanVM.Parameters.ofK (LeanVM.Parameters.gpow 5))))
#guard runOn (readTableC.costDeps ++ mem8C.costDeps) readTableC.costIdx
  [encodeValue (LeanVM.Extraction.Fast.powTable 3), encodeValue (3 : ℕ), .closure mem8C.costIdx [],
    encodeValue (LeanVM.Parameters.gpow 9)] == some (encodeValue (none : Option E))

-- The cursor's length: `q = p · g^9` limb by limb.
#guard runOn cursorLengthC.costDeps cursorLengthC.costIdx
  [dlTables, encodeValue (1 : E), encodeValue (LeanVM.Parameters.ofK (LeanVM.Parameters.gpow 9))] ==
  some (encodeValue (9 : ℕ))

end LeanVMTests.Cost.DecoderChain
