import LeanerVM.Protocol.MerkleBinding
import LeanerVM.Protocol.RandomOracle

/-!
# Collisions and hits of a log, in one pass

`scan` reads a joint log of the hash oracle, compactly (`Entry`: the input's bytes and the answer),
and finds whether it has a collision and whether it has a hit, with hash maps, in one pass: the
decidable clauses of the headline's hypothesis on a log too long for `QueryLog.HasCollision` and
`Hit`, whose decisions are quadratic. `LeanerVMTests.Protocol.Headline` checks it against them on
small logs; the `leanervm-prove` executable runs it on the honest prover's log. It imports only
the definitions it reads, so that an executable importing it initialises nothing else.
-/

namespace LeanerVMTests.Protocol.LogScan

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash

/-- A logged query, compactly: its input's bytes and its answer. -/
abbrev Entry : Type := ByteArray × Digest

/-- A log, compactly. -/
def entries (log : hashSpec.QueryLog) : Array Entry :=
  log.toArray.map fun e ↦ (⟨e.1.toArray⟩, e.2)

attribute [local instance] Digest.hashable in
/-- **The collisions and hits of a joint log**, in one pass with hash maps. The first `nA` entries
are the prover's; `seed` lists the digests in play from the start, `roots` the proof's roots. An
entry is a collision when its digest answered an earlier, different input; a hit when its input is
new and its digest is in play (one of `seed`, a half of an earlier input, the program hash an
earlier input carries, a root rebuilt from two earlier observe steps) or, past the prover's
entries, a root of the proof. Then its halves, the program hash it carries and the roots its
observe step completes are put in play. -/
def scan (seed roots : List Digest) (nA : ℕ) (log : Array Entry) : Bool × Bool := Id.run do
  let rootSet : Std.HashSet Digest := Std.HashSet.ofList roots
  let mut answers : Std.HashMap Digest ByteArray := {}
  let mut seen : Std.HashSet ByteArray := {}
  let mut play : Std.HashSet Digest := Std.HashSet.ofList seed
  let mut firstObs : Std.HashMap Digest E := {}
  let mut pending : Std.HashMap Digest (Array E) := {}
  let mut collision := false
  let mut hit := false
  let mut k := 0
  for (t, a) in log do
    match answers[a]? with
    | some t' => if t' != t then collision := true
    | none => answers := answers.insert a t
    if !seen.contains t && (play.contains a || (nA ≤ k && rootSet.contains a)) then hit := true
    seen := seen.insert t
    let q := t.toList
    for h in halves q ++ programHashSlot q do
      play := play.insert h
    if let some (cv, x) := observed? q then
      match firstObs[cv]? with
      | some x₁ =>
        if let some r := digestOfScalars (x₁, x) then play := play.insert r
      | none => pending := pending.insert cv ((pending.getD cv #[]).push x)
      if !firstObs.contains a then
        firstObs := firstObs.insert a x
        for x' in pending.getD a #[] do
          if let some r := digestOfScalars (x, x') then play := play.insert r
        pending := pending.erase a
    k := k + 1
  return (collision, hit)

end LeanerVMTests.Protocol.LogScan
