import LeanVM.Cost.Extractor.Transcript
import LeanVM.Cost.Extractor.Runner

/-!
# Tests: the compiled transcript index, leaf reader and fast path run

The program of each compiled function's bodies computes the function's value.
-/

namespace LeanVMTests.Cost.Extractor

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics Common

attribute [local instance] lexOrd

/-- Two forward queries from the zero state. -/
def qs : List (PermutationQuery KeccakState × KeccakState) :=
  [(.forward (Vector.replicate 25 0), Vector.ofFn fun i ↦ (i.val + 1).toUInt64),
   (.forward (Vector.ofFn fun i ↦ if i.val < 17 then 7 else 0), Vector.replicate 25 3)]

#guard (evalBody (Program.ofList transcriptIndexC.costDeps) 100000
    transcriptIndexC.costDeps.head!.1 [Enc.enc qs, Enc.enc (64 : ℕ)]).map (·.1) ==
  some (Enc.enc (transcriptIndex qs 64))

def leaves : Array (List K) := #[[K.ofBits 1, K.ofBits 2], [K.ofBits 3, K.ofBits 4]]

#guard (evalBody (Program.ofList leafAtC.costDeps) 1000 leafAtC.costDeps.head!.1
    [Enc.enc leaves, Enc.enc (1 : ℕ), Enc.enc (2 : ℕ), Enc.enc (3 : ℕ)]).map (·.1) ==
  some (Enc.enc (leafAt leaves 1 2 3))

/-- A committed word of `2^7` columns (`κ = 1`, `R = 0`, height 7, width 64): the fast path. -/
def leaves7 : Array (List K) :=
  Array.ofFn fun v : Fin 128 ↦ (List.range 2).map fun u ↦ K.ofBits (u + v.val)

#guard (evalBody (Program.ofList fastStacksOfLeavesC.costDeps) 100000000
    fastStacksOfLeavesC.costDeps.head!.1
    [Enc.enc (7 : ℕ), Enc.enc (0 : ℕ), Enc.enc leaves7, Enc.enc (7 : ℕ), Enc.enc (64 : ℕ)]).map
    (·.1) == some (Enc.enc (fastStacksOfLeaves 7 0 leaves7 7 64))

end LeanVMTests.Cost.Extractor
