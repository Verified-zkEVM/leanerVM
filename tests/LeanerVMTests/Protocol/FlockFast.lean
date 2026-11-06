import LeanerVM.Protocol.FlockWalks
import LeanerVM.Protocol.ToArkLib.Flock.Cached
import LeanerVMTests.Protocol.Flock
import LeanerVMTests.Protocol.FlockCircuit

/-!
# Differential tests of the Flock phase's compiled prover

The walks on words (`ProductCircuit.toBlockR1CSE`) are proved to be the circuit's R1CS
(`toBlockR1CSE_eq`) and the cached Flock prover to run as the honest one
(`Component.Cached.run_eq`); these `#guard`s check the compiled code at small sizes, against the
definitions it stands for.

* **The walks.** On the tiny argument's four-wire circuit, a circuit on `2 ^ 3` positions with
  forms of several terms, and the word circuit of the circuit tests on `2 ^ 8`: the forward walk
  on a block of `0`s and `1`s (the packed path) and on blocks of `E` (the gathered path), and the
  backward walk, against `toBlockR1CS`'s sums.
* **The tables.** The walked products, the skip tables, the skip message, the column weights, the
  folded witness and the slices from the cache's tables, against the definitions, on the tiny
  argument's batch and on tables of `E` that are not `0`s and `1`s; `dotSparse` against the dot
  product on entries `0`, `1` and others; the skip message a byte of tables at a time against the
  dot products on `2 ^ 3` tables of `0`s and `1`s, and the byte sums at an entry's bytes on
  `2 ^ 4`.
* **Runs.** ArkLib's `Prover.run` of the cached Flock prover and of the honest one, at fixed
  challenge sequences, output the same weighted claim's value, on the tiny argument's batch and on
  a batch of `E` tables, and with the circuit's R1CS on words in place of the matrices'.
* **Mutations.** The skip message with the witness tables in place of the left products, a
  backward walk with the two matrices swapped, and the byte sums at another entry's bytes differ
  from the honest values.
-/

namespace LeanerVMTests.Protocol.FlockFast

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Flock CompPoly CMlPolynomialEval
  ProductCircuit
open OracleComp OracleSpec ProtocolSpec
open LeanerVMTests.Protocol.Flock (toyP toyC toyZ side0 noO)

/-- A xorshift step. -/
private def xs (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A `K` word from a seed. -/
private def kOf (s : UInt64) : K := BF64.ofBitVec (xs s).toBitVec

/-- An `E` element from a seed. -/
private def eOf (s : UInt64) : E := E.ofLimbs (kOf s) (kOf (s + 1)) (kOf (s + 2))

/-- A table over `E` from a seed. -/
private def tabE (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ eOf (seed + 5 * i.val.toUInt64)

/-- A block of `0`s and `1`s from a seed. -/
private def tabBool (n : ℕ) (seed : UInt64) : CMlPolynomialEval E n :=
  Vector.ofFn fun i ↦ if (xs (seed + i.val.toUInt64)) % 2 = 0 then 0 else 1

/-! ## The walks -/

/-- The tiny argument's circuit: the constant at `0`, inputs at `1, 2`, the gate `x ∧ y` at `3`. -/
private def tinyCirc : ProductCircuit 2 where
  cpos := 0
  inputs := BitVec.ofNat _ 0b0110
  gates := #[(3, ⟨Form.var 1, Form.var 2⟩)]

/-- A circuit on `2 ^ 3` positions: the constant at `0`, inputs at `1, 2, 3`, three gates
reading forms of several terms. -/
private def toy3 : ProductCircuit 3 where
  cpos := 0
  inputs := BitVec.ofNat _ 0b1110
  gates := #[(4, ⟨BitVec.ofNat _ 0b0110, BitVec.ofNat _ 0b1001⟩),
    (5, ⟨BitVec.ofNat _ 0b10010, BitVec.ofNat _ 0b1100⟩),
    (6, ⟨BitVec.ofNat _ 0b110111, BitVec.ofNat _ 0b100001⟩)]

/-- The walks on words agree with the circuit's sums on a block. -/
private def walksAgree {m : ℕ} (c : ProductCircuit m) (W : CMlPolynomialEval E m) : Bool :=
  decide (c.toBlockR1CSE.rows W = (c.toBlockR1CS E).rows W) &&
    decide (c.toBlockR1CSE.cols W = (c.toBlockR1CS E).cols W)

#guard [1, 2, 3].all fun seed ↦ walksAgree tinyCirc (tabE 2 seed) && walksAgree tinyCirc (tabBool 2 seed)
#guard [1, 2, 3].all fun seed ↦ walksAgree toy3 (tabE 3 seed) && walksAgree toy3 (tabBool 3 seed)

/-- The word circuit's trace on an input, as a block of `E`. -/
private def traceBlock (x : ℕ) : CMlPolynomialEval E 8 :=
  Vector.ofFn fun j ↦
    if (FlockCircuit.toyCircuit.trace (BitVec.ofNat _ x)).getLsbD j then 1 else 0

#guard decide (FlockCircuit.toyCircuit.toBlockR1CSE.rows (traceBlock 0x1234567) =
  (FlockCircuit.toyCircuit.toBlockR1CS E).rows (traceBlock 0x1234567))
#guard decide (FlockCircuit.toyCircuit.toBlockR1CSE.rows (tabE 8 9) =
  (FlockCircuit.toyCircuit.toBlockR1CS E).rows (tabE 8 9))
#guard decide (FlockCircuit.toyCircuit.toBlockR1CSE.cols (tabE 8 11) =
  (FlockCircuit.toyCircuit.toBlockR1CS E).cols (tabE 8 11))

/-! ## The tables -/

-- `dotSparse` on entries `0`, `1` and others.
#guard decide (dotSparse (tabE 3 5) (fun i ↦ #v[0, 1, eOf 3, 1, 0, eOf 4, 0, 1][i]) =
  ∑ i : Fin 8, (tabE 3 5)[i] * #v[0, 1, eOf 3, 1, 0, eOf 4, 0, 1][i])

/-- A batch of `E` tables. -/
private def zE (_ : ∀ i, NoOracle i) (i : Fin (2 ^ toyP.s)) :
    CMlPolynomialEval E (toyP.m + toyP.κ) :=
  tabE 2 (31 + 7 * i.val.toUInt64)

/-- The cache's tables against the definitions, for a batch. -/
private def tablesAgree (z : (∀ i, NoOracle i) → Fin (2 ^ toyP.s) →
    CMlPolynomialEval E (toyP.m + toyP.κ)) : Bool :=
  let zt := Vector.ofFn (z noO)
  let lr := walkedTables toyC zt
  let r : Vector E 2 := #v[eOf 41, eOf 43]
  let Y := eOf 47
  decide (lr.1 = Vector.ofFn (leftTable toyC (z noO))) &&
  decide (lr.2 = Vector.ofFn (rightTable toyC (z noO))) &&
  decide (skipTableOf toyP.nodes lr.1 Y = zcA toyP toyC z noO Y) &&
  decide (skipMessageOf toyP.nodes lr.1 lr.2 zt r = skipMessage toyP.nodes toyC (z noO) r) &&
  decide (mTableOf toyC toyP.cpos (tabE 2 53) Y = mTable toyC toyP.cpos (tabE 2 53) Y) &&
  decide (zTableOf zt #v[eOf 59] = zTable (z noO) #v[eOf 59]) &&
  decide (evalsOf zt r = Vector.ofFn fun i ↦ evalMle (z noO i) r)

#guard tablesAgree toyZ
#guard tablesAgree zE

/-- A family of `2 ^ s` tables of `0`s and `1`s on two variables, from a seed. -/
private def boolFam (s : ℕ) (seed : UInt64) : Vector (CMlPolynomialEval E (1 + 1)) (2 ^ s) :=
  Vector.ofFn fun i ↦ tabBool 2 (seed + 11 * i.val.toUInt64)

/-- Skip nodes for `2 ^ 3` tables. -/
private def nodes3 : SkipDomain E 3 :=
  SkipDomain.ofPts (Vector.ofFn fun j ↦ eOf (67 + 3 * j.val.toUInt64))

-- The skip message a byte of tables at a time (`2 ^ 3` tables of `0`s and `1`s, the byte path)
-- and with a table of other entries (the dot products), against the dot products.
#guard famBool (boolFam 3 71) && famBool (boolFam 3 73) && famBool (boolFam 3 79)
#guard decide (skipMessageOf (m := 1) (κ := 1) nodes3 (boolFam 3 71) (boolFam 3 73) (boolFam 3 79)
    #v[eOf 83, eOf 89] =
  skipMessageDot nodes3 (boolFam 3 71) (boolFam 3 73) (boolFam 3 79) #v[eOf 83, eOf 89])
#guard decide (skipMessageOf (m := 1) (κ := 1) nodes3 (boolFam 3 71) (boolFam 3 73)
    ((boolFam 3 79).set 5 (tabE 2 97)) #v[eOf 83, eOf 89] =
  skipMessageDot nodes3 (boolFam 3 71) (boolFam 3 73) ((boolFam 3 79).set 5 (tabE 2 97))
    #v[eOf 83, eOf 89])

-- Two bytes of tables: the byte sums at every entry's bytes are the dot products, and the
-- bytes of another entry give another value.
#guard (List.finRange 4).all fun u ↦
  decide (combBytes (Array.ofFn fun b : Fin (2 ^ 4 / 8) ↦ byteSums (tabE 4 101) b)
      (famBytes (boolFam 4 103) u) (2 ^ 4 / 8) =
    ∑ i : Fin (2 ^ 4), (tabE 4 101)[i] * (boolFam 4 103)[i][u])
#guard !decide (combBytes (Array.ofFn fun b : Fin (2 ^ 4 / 8) ↦ byteSums (tabE 4 101) b)
    (famBytes (boolFam 4 103) 1) (2 ^ 4 / 8) =
  ∑ i : Fin (2 ^ 4), (tabE 4 101)[i] * (boolFam 4 103)[i][0])

/-! ## Runs -/

/-- Uniform samples read off the words of a xorshift. -/
private def xsImpl : QueryImpl unifSpec (StateM UInt64) :=
  fun n st ↦ (Fin.ofNat (n + 1) st.toNat, xs st)

/-- Run a prover at the challenges a xorshift draws from `seed`. -/
private def runAt {S W S' W' : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (P : Prover []ₒ S W S' W' pSpec) (s : S) (w : W)
    (seed : UInt64) : pSpec.FullTranscript × S' × W' :=
  (simulateQ xsImpl
    (simulateQ (QueryImpl.add (fun t ↦ isEmptyElim t) challengeQueryImpl) (P.run s w))).run' seed

/-- The weighted claim's value handed on. -/
private def finishT : Unit → Weight E 2 → E → E := fun _ _ T ↦ T

/-- The value of the weighted claim an honest run of a Flock prover hands on. -/
private def runValue (C : BlockR1CS E (toyP.s + toyP.m))
    (z : (∀ i, NoOracle i) → Fin (2 ^ toyP.s) → CMlPolynomialEval E (toyP.m + toyP.κ))
    (cached : Bool) (seed : UInt64) : E :=
  if cached then
    (runAt (flockCached toyP C z side0 0 (RingHom.id E) y id finishT (W := Unit)).toProver
      ((), noO) () seed).2.1.1
  else
    (runAt (flock toyP C z side0 0 (RingHom.id E) y id finishT (W := Unit)).red.prover
      ((), noO) () seed).2.1.1

#guard [3, 5, 8].all fun seed ↦ decide (runValue toyC toyZ true seed = runValue toyC toyZ false seed)
#guard [3, 5].all fun seed ↦ decide (runValue toyC zE true seed = runValue toyC zE false seed)

-- The circuit's R1CS on words in place of the matrices': the same runs.
#guard [3, 5].all fun seed ↦
  decide (runValue tinyCirc.toBlockR1CSE toyZ true seed = runValue toyC toyZ false seed)
#guard [3, 5].all fun seed ↦
  decide (runValue tinyCirc.toBlockR1CSE zE true seed = runValue toyC zE false seed)

/-! ## Mutations -/

#guard
  let zt := Vector.ofFn (zE noO)
  let lr := walkedTables toyC zt
  !decide (skipMessageOf toyP.nodes zt lr.2 zt #v[eOf 41, eOf 43] =
    skipMessage toyP.nodes toyC (zE noO) #v[eOf 41, eOf 43])

#guard
  let w := walkCols (rowTable toy3) (tabE 3 61)
  !decide ((w.2, w.1) = (toy3.toBlockR1CS E).cols (tabE 3 61))

end LeanerVMTests.Protocol.FlockFast
