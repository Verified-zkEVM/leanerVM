/-
  LeanerVM.Protocol.Prove.Wire

  The wire of the compiled protocol's schedule, written over the writer's primitives: each
  message's scalars, each challenge's squeezes, the commitments and the grinding, in the stream
  order the executable verifier reads.
-/

module

public import LeanerVM.Protocol.ListBinding
public import LeanerVM.Protocol.ToArkLib.RunCodec
public import LeanerVM.Protocol.Verify.Whir

/-!
# The wire of the compiled schedule

The compiled protocol's honest prover (`LeanerVM.Protocol.Prove.Compiled`) sends the messages of
the oracle protocol and receives its challenges. The proof carries them as the deployed verifiers
read them (`LeanerVM.Protocol.Verify`, transcribed from leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`). `compiledCodec` maps the compiled schedule
`listBindingSpec` to that stream, round by round, over the writer's five primitives (`WireOps`):
send a scalar, squeeze a challenge, grind, commit rows under a Merkle root, and squeeze query
positions. It is the writer's side of the verifier's walk: each phase's codec mirrors the walk of
`LeanerVM.Protocol.Verify` step by step.

* A round polynomial sends its coefficients but the dropped one (`RoundPoly.encode`): `c_0` in a
  round whose equality weight is factored out (the grand product's and the zerocheck's), `c_1` in
  a plain round.
* A challenge of several elements is that many squezes: the four fingerprint challenges `α`,
  then `β`; a point, one squeeze per coordinate.
* The committed words: the level-0 word's row at a position is its first `n` lanes in reverse,
  lane `u` at word `n - 1 - u` (`level0Rows`); a later level's row is its lanes in order, each
  lane's three limbs (`laterRows`). Each word is committed under its root, which is sent as two
  scalars; the openings come after the stream, from the commitments kept (`LeanerVM.Protocol.Prove`).
* The oracle protocol's grinding nonce is a message its honest prover sends as zero and its
  verifier never reads; on the wire it is the nonce the grind finds, absorbed (`WireOps.grind`).
* The query positions are one challenge `Fin t → Fin (2 ^ b)`; on the wire, the squeezes
  `walkPositions` reads, `⌊192/b⌋` positions to a squeeze, low bits first (`positionsWith`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec Whir StepSchedule

@[expose] public section

namespace Prove

/-- The writer's primitives in a monad `w`. -/
structure WireOps (w : Type → Type) where
  /-- Send a scalar, observed. -/
  send : E → w Unit
  /-- Squeeze a challenge. -/
  sample : w E
  /-- Grind WHIR's query bits and send the nonce, absorbed. -/
  grind : w Unit
  /-- Commit to `2 ^ depth` rows, each hashed as its leaf image of `leafWords` words, and send the
  root as two scalars. -/
  commit : (depth leafWords : ℕ) → Vector (List K) (2 ^ depth) → w Unit
  /-- Squeeze `t` query positions of `depth` bits. -/
  positions : (depth t : ℕ) → w (Fin t → Fin (2 ^ depth))

variable {w : Type → Type} [Monad w]

/-- `need` positions of `depth` bits from successive squeezes of `sample`, `⌊192/depth⌋` to a
squeeze, low bits first: the positions `Verify.walkPositions` reads. -/
def positionsWith (sample : w E) (depth : ℕ) : (fuel need : ℕ) → w (List ℕ)
  | 0, _ => pure []
  | _, 0 => pure []
  | fuel + 1, need + 1 => do
    let x ← sample
    let k := min (192 / depth) (need + 1)
    let ps := (List.range k).map fun c ↦ Verify.chalBits x / 2 ^ (c * depth) % 2 ^ depth
    let rest ← positionsWith sample depth fuel (need + 1 - k)
    return ps ++ rest

variable (ops : WireOps w)

/-- Send scalars in order. -/
def sendAll : List E → w Unit
  | [] => pure ()
  | x :: xs => do
    ops.send x
    sendAll xs

/-- `k` squeezes, in order. -/
def samples : ℕ → w (List E)
  | 0 => pure []
  | k + 1 => do
    let x ← ops.sample
    let xs ← samples k
    return x :: xs

/-- A plain round polynomial: its coefficients but `c_1`. -/
def sendPlain {d : ℕ} (c : Vector E (d + 1)) : w Unit := sendAll ops (RoundPoly.encode none c)

/-- A round polynomial whose equality weight is factored out: its coefficients but `c_0`. -/
def sendNormal {d : ℕ} (c : Vector E (d + 1)) : w Unit := sendAll ops (RoundPoly.encode (some 0) c)

/-- Tables in order. -/
def sendTables {k ρ : ℕ} (c : Fin k → Vector E (2 ^ ρ)) : w Unit :=
  sendAll ops ((List.finRange k).flatMap fun t ↦ (c t).toList)

/-! ## The committed rows -/

/-- The stored level-0 rows of a `K` word: the first `n` lanes in reverse, lane `u` at word
`n - 1 - u`; the leaf image puts the zero lanes above them. -/
def level0Rows {ℓ b t : ℕ} (n : ℕ) (x : KWord ℓ b t) : Vector (List K) (2 ^ b) :=
  Vector.ofFn fun y ↦ ((x.row y).toList.take n).reverse

/-- The stored rows of a later level's word: its lanes in order, each lane's three limbs. -/
def laterRows {ℓ b t : ℕ} (x : Word ℓ b t) : Vector (List K) (2 ^ b) :=
  Vector.ofFn fun y ↦ (x.row y).toList.flatMap fun e ↦ [e.limb 0, e.limb 1, e.limb 2]

/-! ## The phases' wires -/

/-- The commitment of the level-0 word, `n` lanes stored a row. -/
def commitCodec (n : ℕ) {ℓ b t : ℕ} :
    RoundCodec w (Component.sendSpec (KWord ℓ b t)) :=
  RoundCodec.sendOne fun x ↦ ops.commit b (2 ^ ℓ) (level0Rows n x)

/-- The bus phase: `α` and `β`, the two roots, the grand product's layers (normalized rounds, the
three trees' values at the descendants, the combination challenges, each layer's combiner), the
boundary values (`Verify.walkBus`). -/
def busCodec (I : M3Instance) : RoundCodec w (busSpec I) :=
  (((RoundCodec.chal (do
      let a ← samples ops 4
      let b ← ops.sample
      return ((fun i ↦ a.getD i 0), b))).append
    (RoundCodec.msg fun r : E × E ↦ do ops.send r.1; ops.send r.2)).append
    (RoundCodec.gkr I.μBus (sendNormal ops) (sendTables ops) (sendNormal ops) (sendTables ops)
      ops.sample)).append
    (RoundCodec.msg fun v : Vector E I.busClaims ↦ sendAll ops v.toList)

/-- The table sumcheck: `ξ`, the plain cubic rounds, the columns' values (`Verify.walkTables`). -/
def tableCodec (I : M3Instance) : RoundCodec w (tableSpec I) :=
  ((RoundCodec.chal ops.sample).append (RoundCodec.rounds (sendPlain ops) ops.sample I.τmax)).append
    (RoundCodec.msg fun v : Vector E I.tableColumns ↦ sendAll ops v.toList)

/-- The public input: `r`, then the values sent (`Verify.walkPub`). -/
def pubCodec : RoundCodec w pubSpec where
  send
    | ⟨0, _⟩, h, _ => nomatch h
    | ⟨1, _⟩, _, xs => sendAll ops xs
  draw
    | ⟨0, _⟩, _ => ops.sample
    | ⟨1, _⟩, h => nomatch h

/-- The Flock phase for `2 ^ k` compressions: the point's coordinates, the 64 values, `z_skip`,
the normalized zerocheck rounds, `â, b̂`, the lincheck's `α`, its plain rounds, the 64 slices and
the six ring-switching challenges (`Verify.walkFlock`). -/
def flockCodecOf (k : ℕ) : RoundCodec w (flockSpecOf k) :=
  (((((((((RoundCodec.chals ops.sample (k + 1)).append
    (RoundCodec.msg fun v : Vector E 64 ↦ sendAll ops v.toList)).append
    (RoundCodec.chal ops.sample)).append (RoundCodec.rounds (sendNormal ops) ops.sample 8)).append
    (RoundCodec.rounds (sendNormal ops) ops.sample k)).append
    (RoundCodec.msg fun v : Vector E 2 ↦ sendAll ops v.toList)).append
    (RoundCodec.chal ops.sample)).append (RoundCodec.rounds (sendPlain ops) ops.sample 8)).append
    (RoundCodec.msg fun v : Vector E 64 ↦ sendAll ops v.toList)).append
    (RoundCodec.chals ops.sample 6)

/-- The Flock slot: the Flock phase of the region, or nothing. -/
def flockCodecOpt (I : M3Instance) :
    (o : Option (FlockRegion I.toShape)) → RoundCodec w (flockSpecOpt I o)
  | none => RoundCodec.empty
  | some r => flockCodecOf ops r.kBatch

/-- One level of WHIR before the last, then the rest: the fold rounds (a challenge, then the next
round polynomial), the next word committed, the out-of-domain point, value and polynomial, the
grinding, the positions, the batching challenge and the query batch's polynomial
(`Verify.walkLevel`). -/
def levelCodec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step} (rest : RoundCodec w (seqSpec k)) :
    RoundCodec w (seqSpec (levelSteps sh sh' κ' k)) :=
  (RoundCodec.chal ops.sample).append <|
  (RoundCodec.rounds (sendPlain ops) ops.sample sh.lm1).append <|
  (RoundCodec.msg (sendPlain ops)).append <|
  (RoundCodec.msg fun x : WordOf sh' κ' ↦
    ops.commit (κ' + sh'.R) (3 * 2 ^ sh'.ℓ) (laterRows x)).append <|
  (RoundCodec.chals ops.sample (Kap sh' κ')).append <|
  (RoundCodec.msg ops.send).append <|
  (RoundCodec.msg (sendPlain ops)).append <|
  (RoundCodec.msg fun _ : E ↦ ops.grind).append <|
  (RoundCodec.chal (ops.positions (Kap sh' κ' + sh.R) sh.t)).append <|
  (RoundCodec.chal ops.sample).append <|
  RoundCodec.empty.append <|
  (RoundCodec.msg (sendPlain ops)).append <|
  RoundCodec.empty.append rest

/-- WHIR's last level: the fold rounds, the residual table in the clear, the grinding, the
positions, the batching challenge, the query batch's polynomial and the tail rounds. -/
def finalCodec (sh : Whir.Shape) (nf : ℕ) : RoundCodec w (seqSpec (finalSteps sh nf)) :=
  (RoundCodec.chal ops.sample).append <|
  (RoundCodec.rounds (sendPlain ops) ops.sample sh.lm1).append <|
  (RoundCodec.msg (sendPlain ops)).append <|
  (RoundCodec.msg fun f : Tab (nf + 1) ↦
    sendAll ops (show Vector E (2 ^ (nf + 1)) from f).toList).append <|
  (RoundCodec.msg fun _ : E ↦ ops.grind).append <|
  (RoundCodec.chal (ops.positions (nf + 1 + sh.R) sh.t)).append <|
  (RoundCodec.chal ops.sample).append <|
  RoundCodec.empty.append <|
  (RoundCodec.msg (sendPlain ops)).append <|
  RoundCodec.empty.append <|
  (RoundCodec.chal ops.sample).append <|
  (RoundCodec.rounds (sendPlain ops) ops.sample nf).append RoundCodec.empty

/-- WHIR's levels. -/
def ladderCodec : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → RoundCodec w (seqSpec L.steps)
  | _, _, .last sh nf => finalCodec ops sh nf
  | _, _, @Ladder.cons sh sh' κ' L => levelCodec ops sh sh' κ' (ladderCodec L)

/-- **The wire of the compiled schedule**: the level-0 commitment, `n` lanes stored a row, the
bus phase, the table sumcheck, the public input, the Flock phase, the opening's batching
challenge, and WHIR: its first round polynomial, then its levels. -/
def compiledCodec (I : M3Instance) (n : ℕ) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) :
    RoundCodec w (listBindingSpec I sh κ L) :=
  (((((((commitCodec ops n).append (busCodec ops I)).append (tableCodec ops I)).append
    (pubCodec ops)).append (flockCodecOpt ops I I.flock)).append
    (RoundCodec.chal ops.sample)).append RoundCodec.empty).append
    (RoundCodec.empty.append ((RoundCodec.msg (sendPlain ops)).append (ladderCodec ops L)))

end Prove

end
end LeanerVM.Protocol
