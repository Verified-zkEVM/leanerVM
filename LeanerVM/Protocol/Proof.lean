/-
  LeanerVM.Protocol.Proof

  leanVM's proof object, the sizes announced at the head of its stream, and the transcript's
  reader and writer over the Fiat–Shamir chain.
-/

module

public import LeanerVM.Protocol.Transcript
public import LeanerVM.Protocol.LeanIsa

/-!
# The proof object and its transcript

Category B, transcribed from the pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`).

**The proof** is a stream of elements of `E` and a list of Merkle opening phases, one per
commitment opened, of a type `M` the caller fixes (`Proof`,
`crates/fiat_shamir/src/transcript.rs:8-12`; the deployed proof carries pruned paths).

**The reader** (`VerifierState`, `transcript.rs:146-220, 255-324`) holds the chain state, the
unread stream and the unread openings, and fails with a `ReadError` (`Error`, `:21-29`):

* `nextScalar` reads a scalar and observes it (`next_scalar`, `:281-287`); `nextScalars n` reads
  `n` in order.
* `nextRoot` reads a digest as two scalars and rejects a nonzero top limb in either
  (`next_root`, `:95-99`; `scalars_to_hash`, `merkle.rs:26-36`).
* `nextRoundPoly d claim eq?` reads and observes the `d` coefficients of a degree-`d` round
  polynomial the wire carries, low degree first, and derives the dropped one from the running
  claim (`next_round_poly`, `:289-309`); its chain effect is `nextScalars d`'s, whatever the claim
  (`Reader.nextRoundPoly_eq`). A plain round drops `c_1 = claim + Σ_{i≥2} c_i`; a
  round whose equality weight `r` is factored out drops `c_0 = claim + r·Σ_{i≥1} c_i`. These are
  the round's checks `h(0) + h(1) = claim` and `(1 + r)·h(0) + r·h(1) = claim` solved in
  characteristic two, so a decoded polynomial passes its round's check and no check remains
  (`RoundPoly.check_of_decode`); the decoding is injective (`RoundPoly.encode_decode`) and keeps
  every polynomial that passes the check (`RoundPoly.decode_encode`).
* `sample` squeezes a challenge; `checkPow bits` reads a nonce, checks the proof of work,
  absorbs the nonce and returns it, failing after the absorb (`grind_check`, `:314-323`).
* `nextOpening auth` takes the next opening phase and authenticates it with `auth`
  (`next_merkle_batch`, `:263-279`); openings are not absorbed.
* `finish` fails unless the stream and the openings are fully consumed (`:212-219`).

**The writer** (`ProverState`, `:112-144, 222-253`) is the mirror: `addScalar(s)`, `addRoot`,
`addRoundPoly` (the coefficients but the dropped one, `:63-71`), `sample`, `grind` (the nonce
pushed raw, absorbed by the grind, `:249-252`) and `hintOpening`.

**The announced sizes** head the stream: the memory log-size, the six opcode tables'
log-heights in the order `XOR, MUL, SET, DEREF, JUMP, BLAKE2S`, and the WHIR rate's log, each a
scalar whose upper two limbs are zero (`announce_public`, `read_public`,
`crates/lean_vm/src/cpu/mod.rs:118-149`). `Proof.announced?` reads them off a proof;
`setupOk` is `read_public`'s checks of them (`:157-176`), `Sizes.Admissible` and `validRate`.
`Reader.readSizes` reads and checks them, and accepts only what `Proof.announced?` reads and
`setupOk` passes (`announced?_of_readSizes`).

**Round trips.** `ReadsBack wr rd R` says that the reader `rd`, run on what the writer `wr`
appends, consumes exactly that, ends in the writer's chain state and returns a value related to
the writer's; it composes along `bind` (`ReadsBack.bind`), holds of each pair of mirrored
operations for every hash function, and gives `runRead_runWrite`: the reader run on the writer's
proof returns the related value and the writer's chain state, with nothing left over.

**Differences from the Rust.** None on a proof read to the end. `Proof.announced?` returns `none`
for a memory log-size of `0`, which `read_public` rejects by its window. `nextRoundPoly` and
`addRoundPoly` take the degree `d`, where the Rust takes the number of coefficients `d + 1`. At a
degree of `0`, which the Rust refuses by an assertion on both sides, `nextRoundPoly` rejects and
`addRoundPoly` writes a wire of one scalar or none, which the reader then rejects. `nextRoundPoly`
observes each coefficient as it reads it, as the Python verifier does, where the Rust reads them
all first: the chain states agree whenever the stream holds them. The setup checks run after all
eight sizes are read, where the Rust checks each size's limbs as it reads it: the same proofs are
rejected. The Rust reader also records raw openings for the recursion guest, which a verifier
does not need.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa

@[expose] public section

/-! ## The proof -/

/-- A proof: the scalar stream and the Merkle opening phases, in order (`Proof<M>`). -/
structure Proof (M : Type) where
  /-- The scalars, in transcript order. -/
  stream : List E
  /-- The opening phases, in transcript order. -/
  merkle : List M

/-- Why a reader rejects (`transcript::Error`; `publicInput` is `CpuError::PublicInput`). -/
inductive ReadError where
  /-- A scalar is read past the end of the stream. -/
  | exceededStream
  /-- An opening phase is read past the end of the openings. -/
  | missingHint
  /-- An opening phase fails its authentication. -/
  | invalidMerkleOpening
  /-- Scalars or openings are left over. -/
  | notFullyConsumed
  /-- A grinding nonce does not clear its bits. -/
  | powFailed
  /-- A half of a digest has a nonzero top limb. -/
  | nonCanonicalEncoding
  /-- An announced size has a nonzero upper limb or fails the setup checks. -/
  | publicInput
  /-- A round polynomial of degree `0`, which the Rust refuses by an assertion. -/
  | roundDegree
  deriving DecidableEq, Repr

/-! ## Round polynomials -/

namespace RoundPoly

/-- Horner evaluation of a coefficient list, low degree first. -/
def evalList : List E → E → E
  | [], _ => 0
  | c :: cs, x => c + x * evalList cs x

/-- The value at `x` of the polynomial with coefficients `c`, low degree first. -/
def eval {d : ℕ} (c : Vector E (d + 1)) (x : E) : E := evalList c.toList x

/-- The round's check: `h(0) + h(1) = claim` in a plain round, `(1 + r)·h(0) + r·h(1) = claim`
when the equality weight `r` is factored out. -/
def Check {d : ℕ} (claim : E) (eq? : Option E) (c : Vector E (d + 1)) : Prop :=
  match eq? with
  | none => eval c 0 + eval c 1 = claim
  | some r => (1 + r) * eval c 0 + r * eval c 1 = claim

/-- The round's check is decided by comparing elements of `E`. -/
instance {d : ℕ} {claim : E} {eq? : Option E} {c : Vector E (d + 1)} :
    Decidable (Check claim eq? c) :=
  match eq? with
  | none => inferInstanceAs (Decidable (eval c 0 + eval c 1 = claim))
  | some r => inferInstanceAs (Decidable ((1 + r) * eval c 0 + r * eval c 1 = claim))

/-- The position of the coefficient the wire drops: `1` in a plain round, `0` when the equality
weight is factored out (`fixed`). -/
def dropped (eq? : Option E) : ℕ := if eq?.isSome then 0 else 1

/-- The wire: the coefficients but the dropped one, low degree first (`add_round_poly`). -/
def encode {d : ℕ} (eq? : Option E) (c : Vector E (d + 1)) : List E :=
  c.toList.eraseIdx (dropped eq?)

/-- The coefficients from the wire, the dropped one derived from the claim (`next_round_poly`).
An empty plain wire, a polynomial of degree `0`, has no coefficient to keep; `decode` rejects it. -/
def complete (claim : E) : Option E → List E → List E
  | none, [] => [claim]
  | none, c0 :: rest => c0 :: (claim + rest.sum) :: rest
  | some r, rest => (claim + r * rest.sum) :: rest

/-- A list of length `n` as a vector. -/
def ofList? (n : ℕ) (l : List E) : Option (Vector E n) :=
  if h : l.length = n then some ⟨l.toArray, by simpa using h⟩ else none

/-- Decode a degree-`d` round polynomial from its `d` wire coefficients and the running claim;
`none` for another number of coefficients or `d = 0`. -/
def decode (d : ℕ) (claim : E) (eq? : Option E) (w : List E) : Option (Vector E (d + 1)) :=
  if 0 < d ∧ w.length = d then ofList? (d + 1) (complete claim eq? w) else none

end RoundPoly

/-! ## The announced sizes -/

/-- A size as a scalar, `n + 0·y + 0·y²` (`F192::new(n as u64, 0, 0)`). -/
def sizeScalar (n : ℕ) : E := E.ofLimbs (K.ofBits n) 0 0

/-- The size a scalar carries, or `none` if an upper limb is nonzero (`read_size`). -/
def sizeOf? (x : E) : Option ℕ :=
  if x.limb 1 = 0 ∧ x.limb 2 = 0 then some (x.limb 0).toBitVec.toNat else none

/-- The scalars announcing the sizes and the rate (`announce_public`). -/
def announcement (s : Sizes) (ρ : ℕ) : List E :=
  (s.logMem :: List.ofFn s.τ ++ [ρ]).map sizeScalar

/-- The sizes and the rate read off eight scalars; `none` for another number, a nonzero upper
limb, or a memory log-size of `0`. -/
def decodeAnnouncement : List E → Option (Sizes × ℕ)
  | [lm, t0, t1, t2, t3, t4, t5, r] => do
    let logMem ← sizeOf? lm
    let τ0 ← sizeOf? t0
    let τ1 ← sizeOf? t1
    let τ2 ← sizeOf? t2
    let τ3 ← sizeOf? t3
    let τ4 ← sizeOf? t4
    let τ5 ← sizeOf? t5
    let ρ ← sizeOf? r
    if h : 0 < logMem then some (⟨logMem, h, ![τ0, τ1, τ2, τ3, τ4, τ5]⟩, ρ) else none
  | _ => none

/-- The sizes and the rate a proof announces, read off the head of its stream. -/
def Proof.announced? {M : Type} (p : Proof M) : Option (Sizes × ℕ) :=
  decodeAnnouncement (p.stream.take 8)

/-- The sizes a proof announces. -/
def Proof.sizes? {M : Type} (p : Proof M) : Option Sizes := p.announced?.map Prod.fst

/-- The setup checks of the announced sizes and rate (`read_public`, `cpu/mod.rs:157-176`): the
memory window, the height cap, the `BLAKE2S` floor and the stacked size's cap
(`Sizes.Admissible`), and the rate's window (`validRate`). -/
def setupOk (prog : Program) (s : Sizes) (ρ : ℕ) : Bool := decide (s.Admissible prog ∧ validRate ρ)

/-! ## The reader -/

/-- The reader's state: the chain, the unread scalars and the unread openings (`VerifierState`). -/
structure ReaderState (M : Type) where
  /-- The chain state. -/
  fs : FsState
  /-- The scalars not yet read. -/
  stream : List E
  /-- The opening phases not yet read. -/
  merkle : List M

/-- The reader's monad: its state and a rejection, over the hash's monad. -/
abbrev ReadM (m : Type → Type) (M : Type) := StateT (ReaderState M) (ExceptT ReadError m)

namespace Reader

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) {M : Type}

/-- The next scalar, not observed (`take_raw`). -/
def takeRaw : ReadM m M E := do
  match (← get).stream with
  | [] => throw .exceededStream
  | x :: rest =>
    modify fun st ↦ { st with stream := rest }
    return x

/-- Observe a scalar. -/
def observe (x : E) : ReadM m M Unit := do
  let fs ← ((← get).fs.observe H x : m FsState)
  modify fun st ↦ { st with fs }

/-- Read and observe the next scalar (`next_scalar`). -/
def nextScalar : ReadM m M E := do
  let x ← takeRaw
  observe H x
  return x

/-- Read and observe the next `n` scalars (`next_scalars`). -/
def nextScalars : ℕ → ReadM m M (List E)
  | 0 => pure []
  | n + 1 => do
    let x ← nextScalar H
    let xs ← nextScalars n
    return x :: xs

/-- Read a digest as two scalars, rejecting a nonzero top limb (`next_root`). -/
def nextRoot : ReadM m M Digest := do
  let a ← nextScalar H
  let b ← nextScalar H
  match digestOfScalars (a, b) with
  | some d => return d
  | none => throw .nonCanonicalEncoding

/-- Read a degree-`d` round polynomial: its `d` wire coefficients, observed in order, then the
dropped one derived from the claim (`next_round_poly`). The second rejection is unreachable:
`nextScalars H d` returns `d` scalars, which decode for `0 < d` (`RoundPoly.isSome_decode`). -/
def nextRoundPoly (d : ℕ) (claim : E) (eq? : Option E) : ReadM m M (Vector E (d + 1)) := do
  if d = 0 then throw .roundDegree
  let w ← nextScalars H d
  match RoundPoly.decode d claim eq? w with
  | some c => return c
  | none => throw .roundDegree

/-- Squeeze a challenge. -/
def sample : ReadM m M E := do
  let p ← ((← get).fs.sample H : m (E × FsState))
  modify fun st ↦ { st with fs := p.2 }
  return p.1

/-- Read a grinding nonce, check it clears `bits` and absorb it, failing after the absorb
(`grind_check`): the nonce. -/
def checkPow (bits : ℕ) : ReadM m M E := do
  let nonce ← takeRaw
  let r ← ((← get).fs.checkPow H bits nonce : m (Bool × FsState))
  modify fun st ↦ { st with fs := r.2 }
  unless r.1 do throw .powFailed
  return nonce

/-- Take the next opening phase and authenticate it (`next_merkle_batch`); not observed. -/
def nextOpening {α : Type} (auth : M → m (Option α)) : ReadM m M α := do
  match (← get).merkle with
  | [] => throw .missingHint
  | o :: rest =>
    modify fun st ↦ { st with merkle := rest }
    match ← (auth o : m (Option α)) with
    | some a => return a
    | none => throw .invalidMerkleOpening

/-- Fail unless the stream and the openings are fully consumed (`finish`). -/
def finish : ReadM m M Unit := do
  let st ← get
  unless st.stream.isEmpty && st.merkle.isEmpty do throw .notFullyConsumed

/-- Read the announced sizes and rate and make the setup checks (`read_public`). -/
def readSizes (prog : Program) : ReadM m M (Sizes × ℕ) := do
  match decodeAnnouncement (← nextScalars H 8) with
  | none => throw .publicInput
  | some (s, ρ) => if setupOk prog s ρ then return (s, ρ) else throw .publicInput

/-- For a positive degree, reading a round polynomial is reading `d` scalars, then decoding them:
its chain effect does not depend on the claim. -/
theorem nextRoundPoly_eq {d : ℕ} (hd : 0 < d) (claim : E) (eq? : Option E) :
    nextRoundPoly (M := M) H d claim eq? = (do
      let w ← nextScalars H d
      match RoundPoly.decode d claim eq? w with
      | some c => return c
      | none => throw .roundDegree) := by
  simp only [nextRoundPoly, Nat.pos_iff_ne_zero.mp hd, ↓reduceIte]

end Reader

/-- Run a reader on a proof from a chain state, then `finish`: the value and the final chain
state, or the rejection. -/
def runRead {m : Type → Type} [Monad m] {M β : Type} (rd : ReadM m M β) (fs : FsState)
    (p : Proof M) : m (Except ReadError (β × FsState)) :=
  ((do let b ← rd; Reader.finish; return (b, (← get).fs)) : ReadM m M (β × FsState)).run'
    ⟨fs, p.stream, p.merkle⟩ |>.run

/-! ## The writer -/

/-- The writer's state: the chain, and the scalars and openings written so far (`ProverState`). -/
structure WriterState (M : Type) where
  /-- The chain state. -/
  fs : FsState
  /-- The scalars written. -/
  stream : Array E
  /-- The opening phases written. -/
  merkle : Array M

/-- The proof written so far. -/
def WriterState.proof {M : Type} (w : WriterState M) : Proof M := ⟨w.stream.toList, w.merkle.toList⟩

/-- The writer's monad: its state, and failure when a grind runs out of fuel. -/
abbrev WriteM (m : Type → Type) (M : Type) := StateT (WriterState M) (OptionT m)

namespace Writer

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) {M : Type}

/-- Send a scalar: observe it and append it (`add_scalar`). -/
def addScalar (x : E) : WriteM m M Unit := do
  let fs ← ((← get).fs.observe H x : m FsState)
  modify fun st ↦ { st with fs, stream := st.stream.push x }

/-- Send scalars in order (`add_scalars`). -/
def addScalars : List E → WriteM m M Unit
  | [] => pure ()
  | x :: xs => do
    addScalar H x
    addScalars xs

/-- Send a digest as two scalars (`add_root`). -/
def addRoot (d : Digest) : WriteM m M Unit :=
  addScalars H [(digestScalars d).1, (digestScalars d).2]

/-- Send a round polynomial: its coefficients but the dropped one (`add_round_poly`). -/
def addRoundPoly {d : ℕ} (eq? : Option E) (c : Vector E (d + 1)) : WriteM m M Unit :=
  addScalars H (RoundPoly.encode eq? c)

/-- Squeeze a challenge. -/
def sample : WriteM m M E := do
  let p ← ((← get).fs.sample H : m (E × FsState))
  modify fun st ↦ { st with fs := p.2 }
  return p.1

/-- Grind `bits` with `fuel` candidate nonces, absorb the nonce and append it raw; fails when
the fuel runs out (`grind`). -/
def grind (fuel bits : ℕ) : WriteM m M Unit := do
  match ← ((← get).fs.grind H fuel bits : m (Option (E × FsState))) with
  | none => failure
  | some p => modify fun st ↦ { st with fs := p.2, stream := st.stream.push p.1 }

/-- Append an opening phase, not observed (`hint_merkle`). -/
def hintOpening (o : M) : WriteM m M Unit :=
  modify fun st ↦ { st with merkle := st.merkle.push o }

/-- Announce the sizes and the rate (`announce_public`). -/
def announce (s : Sizes) (ρ : ℕ) : WriteM m M Unit := addScalars H (announcement s ρ)

end Writer

/-- Run a writer from a chain state on an empty proof: the value and the final writer state, or
`none` when a grind runs out of fuel. -/
def runWrite {m : Type → Type} [Monad m] {M α : Type} (wr : WriteM m M α) (fs : FsState) :
    m (Option (α × WriterState M)) :=
  (wr.run ⟨fs, #[], #[]⟩).run

/-! ## The wire of a round polynomial -/

namespace RoundPoly

private theorem evalList_zero (c : E) (cs : List E) : evalList (c :: cs) 0 = c := by
  simp [evalList]

private theorem evalList_one : ∀ cs : List E, evalList cs 1 = cs.sum
  | [] => rfl
  | c :: cs => by simp [evalList, evalList_one cs]

/-- A polynomial of positive degree has at least two coefficients. -/
private theorem toList_eq_cons_cons {d : ℕ} (hd : 0 < d) (c : Vector E (d + 1)) :
    ∃ c0 c1 rest, c.toList = c0 :: c1 :: rest := by
  have hlen := c.length_toList
  rcases hc : c.toList with _ | ⟨c0, _ | ⟨c1, rest⟩⟩ <;> simp [hc] at hlen
  · omega
  · exact ⟨c0, c1, rest, rfl⟩

private theorem length_complete (claim : E) (eq? : Option E) (w : List E) :
    (complete claim eq? w).length = w.length + 1 := by
  rcases eq? with _ | _ <;> rcases w with _ | _ <;> simp [complete]

private theorem ofList?_toList {n : ℕ} (c : Vector E n) : ofList? n c.toList = some c := by
  rcases c with ⟨a, rfl⟩
  simp [ofList?]

/-- A decoding succeeds at a positive degree on `d` wire coefficients, to their completion. -/
private theorem of_decode {d : ℕ} {claim : E} {eq? : Option E} {w : List E}
    {c : Vector E (d + 1)} (h : decode d claim eq? w = some c) :
    (0 < d ∧ w.length = d) ∧ c.toList = complete claim eq? w := by
  obtain ⟨hw, h⟩ := Option.ite_none_right_eq_some.mp h
  unfold ofList? at h
  split at h <;> cases h
  exact ⟨hw, rfl⟩

/-- The wire of a polynomial of positive degree `d` has `d` coefficients. -/
theorem length_encode {d : ℕ} (hd : 0 < d) {eq? : Option E} (c : Vector E (d + 1)) :
    (encode eq? c).length = d := by
  simp only [encode, List.length_eraseIdx, Vector.length_toList, dropped]
  split <;> split <;> omega

/-- The wire of a polynomial that passes its round's check decodes to the polynomial: the honest
round survives the wire. -/
theorem decode_encode {d : ℕ} (hd : 0 < d) {claim : E} {eq? : Option E}
    {c : Vector E (d + 1)} (h : Check claim eq? c) :
    decode d claim eq? (encode eq? c) = some c := by
  suffices complete claim eq? (encode eq? c) = c.toList by
    rw [decode, ite_eq_left_of_eq_true _ _ (eq_true ⟨hd, length_encode hd c⟩), this, ofList?_toList]
  obtain ⟨c0, c1, rest, hc⟩ := toList_eq_cons_cons hd c
  have hz : (2 : E) = 0 := CharTwo.two_eq_zero
  rcases eq? with _ | r <;>
    simp only [Check, eval, hc, evalList_zero, evalList_one, List.sum_cons] at h <;>
    simp [encode, dropped, hc, complete]
  · linear_combination -1 * h + (c0 + rest.sum) * hz
  · linear_combination -1 * h + (r * c0 + r * c1 + r * rest.sum) * hz

/-- Every `d` wire coefficients decode, for a positive degree `d`. -/
theorem isSome_decode {d : ℕ} (hd : 0 < d) (claim : E) (eq? : Option E) {w : List E}
    (hw : w.length = d) : (decode d claim eq? w).isSome := by
  simp [decode, ofList?, hd, hw, length_complete]

/-- A decoded polynomial carries the wire: the decoding is injective. -/
theorem encode_decode {d : ℕ} {claim : E} {eq? : Option E} {w : List E} {c : Vector E (d + 1)}
    (h : decode d claim eq? w = some c) : encode eq? c = w := by
  obtain ⟨⟨hd, hw⟩, hc⟩ := of_decode h
  rw [encode, hc]
  rcases eq? with _ | _ <;> rcases w with _ | _ <;> simp [complete, dropped] at hw ⊢
  omega

/-- A decoded polynomial passes its round's check: no check remains for the verifier. -/
theorem check_of_decode {d : ℕ} {claim : E} {eq? : Option E} {w : List E}
    {c : Vector E (d + 1)} (h : decode d claim eq? w = some c) : Check claim eq? c := by
  obtain ⟨⟨hd, hw⟩, hc⟩ := of_decode h
  have hz : (2 : E) = 0 := CharTwo.two_eq_zero
  rcases eq? with _ | r
  · rcases w with _ | ⟨c0, rest⟩
    · simp at hw; omega
    · simp only [Check, eval, hc, complete, evalList_zero, evalList_one, List.sum_cons]
      linear_combination (c0 + rest.sum) * hz
  · simp only [Check, eval, hc, complete, evalList_zero, evalList_one, List.sum_cons]
    linear_combination (r * w.sum + r * claim + r ^ 2 * w.sum) * hz

end RoundPoly

/-! ## The announcement round trip -/

private theorem sizeOf?_sizeScalar {n : ℕ} (h : n ≤ 32) : sizeOf? (sizeScalar n) = some n := by
  simp [sizeOf?, sizeScalar, K.ofBits]

/-- The announcement of sizes that pass the setup checks decodes to them. -/
theorem decodeAnnouncement_announcement {prog : Program} {s : Sizes} {ρ : ℕ}
    (h : setupOk prog s ρ = true) : decodeAnnouncement (announcement s ρ) = some (s, ρ) := by
  obtain ⟨⟨-, hm, hτ, -, -⟩, -, hr⟩ := of_decide_eq_true h
  obtain ⟨logMem, hpos, τ⟩ := s
  simp [announcement, decodeAnnouncement, List.ofFn_succ, sizeOf?_sizeScalar hm,
    sizeOf?_sizeScalar (hτ _), sizeOf?_sizeScalar (show ρ ≤ 32 by omega), hpos]
  funext j
  fin_cases j <;> rfl

private theorem sizeScalar_of_sizeOf? {x : E} {n : ℕ} (h : sizeOf? x = some n) :
    sizeScalar n = x := by
  unfold sizeOf? at h
  split_ifs at h with hl
  cases h
  conv_rhs => rw [← ofLimbs_limb x, hl.1, hl.2]
  refine congrArg (E.ofLimbs · 0 0) (BF64.toBitVec_injective ?_)
  simp [K.ofBits]

/-- **Eight scalars that decode to sizes and a rate are their announcement.** -/
theorem eq_announcement_of_decodeAnnouncement {xs : List E} {s : Sizes} {ρ : ℕ}
    (h : decodeAnnouncement xs = some (s, ρ)) : xs = announcement s ρ := by
  match xs, h with
  | [lm, t0, t1, t2, t3, t4, t5, r], h =>
    simp only [decodeAnnouncement, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.dite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨n₀, h₀, n₁, h₁, n₂, h₂, n₃, h₃, n₄, h₄, n₅, h₅, n₆, h₆, n₇, h₇, -, rfl, rfl⟩ := h
    simp [announcement, List.ofFn_succ, sizeScalar_of_sizeOf? h₀, sizeScalar_of_sizeOf? h₁,
      sizeScalar_of_sizeOf? h₂, sizeScalar_of_sizeOf? h₃, sizeScalar_of_sizeOf? h₄,
      sizeScalar_of_sizeOf? h₅, sizeScalar_of_sizeOf? h₆, sizeScalar_of_sizeOf? h₇]

/-- **A proof's stream opens with the announcement of the sizes and the rate it announces.** -/
theorem take_eq_announcement_of_announced? {M : Type} {p : Proof M} {s : Sizes} {ρ : ℕ}
    (h : p.announced? = some (s, ρ)) : p.stream.take 8 = announcement s ρ :=
  eq_announcement_of_decodeAnnouncement h

/-! ## Round trips: the reader reads back what the writer writes -/

/-- The reader `rd` reads back what the writer `wr` writes: whenever `wr`, run from a writer
state, returns `a`, it has appended scalars `xs` and openings `ms`, and there is a `b` with
`R a b` that `rd` returns when run from the writer's starting chain state on `xs` and `ms`
followed by anything, consuming exactly `xs` and `ms` and ending in the writer's final chain
state. -/
def ReadsBack {M α β : Type} (wr : WriteM Id M α) (rd : ReadM Id M β) (R : α → β → Prop) :
    Prop :=
  ∀ (w w' : WriterState M) (a : α), (wr.run w).run = some (a, w') →
    ∃ xs ms b, w'.stream.toList = w.stream.toList ++ xs ∧
      w'.merkle.toList = w.merkle.toList ++ ms ∧ R a b ∧
      ∀ tail mtail, (rd.run ⟨w.fs, xs ++ tail, ms ++ mtail⟩).run =
        Except.ok (b, ⟨w'.fs, tail, mtail⟩)

section RoundTrip

variable {M : Type}

private theorem reads_bind {α β : Type} {rd : ReadM Id M α} {rf : α → ReadM Id M β}
    {st st' st'' : ReaderState M} {a : α} {b : β} (h₁ : (rd.run st).run = Except.ok (a, st'))
    (h₂ : ((rf a).run st').run = Except.ok (b, st'')) :
    ((rd >>= rf).run st).run = Except.ok (b, st'') := by
  rw [StateT.run_bind, ExceptT.run_bind, h₁]
  exact h₂

private theorem reads_bind_inv {α β : Type} {rd : ReadM Id M α} {rf : α → ReadM Id M β}
    {st st'' : ReaderState M} {b : β} (h : ((rd >>= rf).run st).run = Except.ok (b, st'')) :
    ∃ a st', (rd.run st).run = Except.ok (a, st') ∧ ((rf a).run st').run = Except.ok (b, st'') := by
  rw [StateT.run_bind, ExceptT.run_bind] at h
  rcases h₁ : (rd.run st).run with e | ⟨a, st'⟩ <;> rw [h₁] at h
  · cases h
  · exact ⟨a, st', rfl, h⟩

/-- Pure values read back. -/
theorem ReadsBack.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ReadsBack (M := M) (Pure.pure a) (Pure.pure b) R := by
  rintro w _ _ ⟨⟩
  exact ⟨[], [], b, by simp, by simp, h, fun _ _ ↦ rfl⟩

/-- Reading back composes along `bind`. -/
theorem ReadsBack.bind {α β γ δ : Type} {wr : WriteM Id M α} {rd : ReadM Id M β}
    {R : α → β → Prop} {wf : α → WriteM Id M γ} {rf : β → ReadM Id M δ} {S : γ → δ → Prop}
    (h₁ : ReadsBack wr rd R) (h₂ : ∀ a b, R a b → ReadsBack (wf a) (rf b) S) :
    ReadsBack (wr >>= wf) (rd >>= rf) S := by
  intro w w'' c hw
  rw [StateT.run_bind, OptionT.run_bind] at hw
  rcases h₀ : (wr.run w).run with _ | ⟨a, w'⟩ <;> rw [h₀] at hw
  · cases hw
  obtain ⟨xs, ms, b, hxs, hms, hR, hrd⟩ := h₁ w w' a h₀
  obtain ⟨xs', ms', d, hxs', hms', hS, hrf⟩ := h₂ a b hR w' w'' c hw
  refine ⟨xs ++ xs', ms ++ ms', d, by simp [hxs', hxs], by simp [hms', hms], hS,
    fun tail mtail ↦ ?_⟩
  rw [List.append_assoc, List.append_assoc]
  exact reads_bind (hrd _ _) (hrf tail mtail)

/-- A reader that reads back `wr` and then returns a value computed from its own reads back `wr`. -/
private theorem ReadsBack.map {α β γ : Type} {wr : WriteM Id M α} {rd : ReadM Id M β}
    {R : α → β → Prop} {rf : β → ReadM Id M γ} {S : α → γ → Prop} (h : ReadsBack wr rd R)
    (hf : ∀ a b, R a b → ∃ c, rf b = Pure.pure c ∧ S a c) : ReadsBack wr (rd >>= rf) S := by
  rw [← bind_pure wr]
  exact h.bind fun a b hab ↦ (hf a b hab).elim fun _ ⟨hc, hS⟩ ↦ hc ▸ ReadsBack.pure hS

variable (H : List UInt8 → Id Digest)

/-! ### Each operation reads back -/

/-- A scalar reads back. -/
theorem readsBack_scalar (x : E) :
    ReadsBack (M := M) (Writer.addScalar H x) (Reader.nextScalar H) (fun _ b ↦ b = x) := by
  rintro w _ _ ⟨⟩
  exact ⟨[x], [], x, by simp, by simp, rfl, fun _ _ ↦ rfl⟩

/-- Scalars read back. -/
theorem readsBack_scalars (xs : List E) :
    ReadsBack (M := M) (Writer.addScalars H xs) (Reader.nextScalars H xs.length)
      (fun _ b ↦ b = xs) := by
  induction xs with
  | nil => exact ReadsBack.pure rfl
  | cons x xs ih =>
    refine (readsBack_scalar H x).bind fun _ y hy ↦ ih.map fun _ ys hys ↦ ?_
    exact ⟨y :: ys, rfl, by rw [hy, hys]⟩

/-- A root reads back. -/
theorem readsBack_root (d : Digest) :
    ReadsBack (M := M) (Writer.addRoot H d) (Reader.nextRoot H) (fun _ b ↦ b = d) := by
  refine (readsBack_scalar H _).bind fun _ a ha ↦ (readsBack_scalar H _).map fun _ b hb ↦ ?_
  subst ha hb
  exact ⟨d, by simp only [Prod.mk.eta, digestOfScalars_digestScalars], rfl⟩

/-- A round polynomial that passes its round's check reads back. -/
theorem readsBack_roundPoly {d : ℕ} (hd : 0 < d) {claim : E} {eq? : Option E}
    {c : Vector E (d + 1)} (hc : RoundPoly.Check claim eq? c) :
    ReadsBack (M := M) (Writer.addRoundPoly H eq? c) (Reader.nextRoundPoly H d claim eq?)
      (fun _ b ↦ b = c) := by
  have hs := readsBack_scalars (M := M) H (RoundPoly.encode eq? c)
  rw [RoundPoly.length_encode hd] at hs
  rw [Reader.nextRoundPoly_eq H hd]
  refine hs.map fun _ w hw ↦ ⟨c, ?_, rfl⟩
  simp only [hw, RoundPoly.decode_encode hd hc]

/-- A challenge reads back. -/
theorem readsBack_sample :
    ReadsBack (M := M) (Writer.sample H) (Reader.sample H) (· = ·) := by
  rintro w _ _ ⟨⟩
  exact ⟨[], [], _, by simp, by simp, rfl, fun _ _ ↦ rfl⟩

/-- A grinding nonce reads back and passes the check. -/
theorem readsBack_grind (fuel bits : ℕ) :
    ReadsBack (M := M) (Writer.grind H fuel bits) (Reader.checkPow H bits) (fun _ _ ↦ True) := by
  intro w w' a hw
  rcases hg : Id.run (w.fs.grind H fuel bits) with _ | ⟨nonce, fs'⟩ <;>
    simp [Writer.grind, StateT.run_bind, show w.fs.grind H fuel bits = Pure.pure _ from hg] at hw
  cases hw
  refine ⟨[nonce], [], nonce, by simp, by simp, trivial, fun _ _ ↦ ?_⟩
  simp [Reader.checkPow, Reader.takeRaw, StateT.run_bind,
    show w.fs.checkPow H bits nonce = Pure.pure (true, fs') from FsState.checkPow_of_grind H hg]
  rfl

/-- An opening phase reads back when it authenticates. -/
theorem readsBack_opening {α : Type} (o : M) {auth : M → Id (Option α)} {a : α}
    (ha : auth o = some a) :
    ReadsBack (Writer.hintOpening (m := Id) o) (Reader.nextOpening auth) (fun _ b ↦ b = a) := by
  rintro w _ _ ⟨⟩
  exact ⟨[], [o], a, by simp, by simp, rfl, fun _ _ ↦ by simp [Reader.nextOpening, ha]; rfl⟩

/-- The announced sizes read back when they pass the setup checks. -/
theorem readsBack_announce {prog : Program} {s : Sizes} {ρ : ℕ} (h : setupOk prog s ρ = true) :
    ReadsBack (M := M) (Writer.announce H s ρ) (Reader.readSizes H prog)
      (fun _ b ↦ b = (s, ρ)) := by
  have hs := readsBack_scalars (M := M) H (announcement s ρ)
  rw [show (announcement s ρ).length = 8 by simp [announcement]] at hs
  refine hs.map fun _ xs hxs ↦ ⟨(s, ρ), ?_, rfl⟩
  simp only [hxs, decodeAnnouncement_announcement h, h, ↓reduceIte]

/-! ### What the reader of the sizes accepts -/

private theorem nextScalars_take {n : ℕ} {fs : FsState} {xs ys : List E} {ms : List M}
    {st' : ReaderState M}
    (h : ((Reader.nextScalars H n).run ⟨fs, xs, ms⟩).run = Except.ok (ys, st')) :
    ys = xs.take n := by
  induction n generalizing fs xs ys with
  | zero => cases h; rfl
  | succ n ih =>
    obtain ⟨y, st₁, h₁, h₂⟩ := reads_bind_inv h
    obtain ⟨ys', st₂, h₃, ⟨⟩⟩ := reads_bind_inv h₂
    rcases xs with _ | ⟨x, xs⟩ <;> cases h₁
    rw [ih h₃, List.take_succ_cons]

/-- Sizes the reader accepts are the sizes the proof announces, and pass the setup checks. -/
theorem announced?_of_readSizes {prog : Program} {fs : FsState} {p : Proof M} {s : Sizes}
    {ρ : ℕ} {st' : ReaderState M}
    (h : ((Reader.readSizes H prog).run ⟨fs, p.stream, p.merkle⟩).run =
      Except.ok ((s, ρ), st')) :
    p.announced? = some (s, ρ) ∧ setupOk prog s ρ = true := by
  obtain ⟨xs, st₁, h₁, h₂⟩ := reads_bind_inv h
  rw [nextScalars_take H h₁] at h₂
  rw [Proof.announced?]
  revert h₂
  rcases decodeAnnouncement (p.stream.take 8) with _ | ⟨s', ρ'⟩
  · rintro ⟨⟩
  · cases hs : setupOk prog s' ρ' <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] <;>
      rintro ⟨⟩
    exact ⟨rfl, hs⟩

/-! ### The transcript round trip -/

/-- The reader run on the proof the writer writes, from the writer's starting chain state,
returns a value related to the writer's and ends in the writer's final chain state, with the
stream and the openings fully consumed. -/
theorem runRead_runWrite {α β : Type} {wr : WriteM Id M α} {rd : ReadM Id M β}
    {R : α → β → Prop} (h : ReadsBack wr rd R) {fs : FsState} {a : α} {w : WriterState M}
    (hw : Id.run (runWrite wr fs) = some (a, w)) :
    ∃ b, R a b ∧ Id.run (runRead rd fs w.proof) = Except.ok (b, w.fs) := by
  obtain ⟨xs, ms, b, hxs, hms, hR, hrd⟩ := h _ _ _ hw
  refine ⟨b, hR, ?_⟩
  have hrun := hrd [] []
  simp only [List.append_nil] at hrun
  simp [runRead, WriterState.proof, hxs, hms, StateT.run'_eq, StateT.run_bind, ExceptT.run_bind,
    hrun]
  rfl

end RoundTrip

end
end LeanerVM.Protocol
