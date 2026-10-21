/-
  LeanVM.E2E.Batch

  The batching leg of the end-to-end theorem in the random-oracle model (package W6): from the
  constant start, the bytecode part only, in cache form over the game's log, for every batching
  instance at once; and the game ends with the batching's bad event with probability at most
  `Q · (2/2^192 + 4 (Q + 1)/2^256)`.
-/

module

public import LeanVM.E2E.Batch.With
public import LeanVM.E2E.Engine

/-!
# The batching of deferred claims, in the random-oracle model

A node proves its children in-circuit and batches their deferred claims: `NodeRelWith` asks
`batchWith H s0 cs w.hints = some (some s.defer)`, `s0` the batching's start as data (decision
D5: the guest bakes `blake2sBytes batchLabel`; in the idealized system it is a constant, not an
oracle answer). V_I's outer check verifies only the bytecode part of the root's deferred claim
(`DeferredClaim.BytecodeHolds`). T4 needs: if a node's deferred claim's bytecode part holds and
the batching of its children, every hash answered by the game's log, produced it, then every
child's bytecode claims hold, its proof's (`FixedClaims.BytecodeHolds`) and its statement's
(`DeferredClaim.BytecodeHolds`), except on a bad event of the log.

## The constant start

The random-oracle theorem's decoder (`LeanVM.Protocol.Compile.Rom.Decode`) starts a chain only at
the output of a seeding's last input: a seeding's first input is never a chain input
(`Seeds.first_len`), and every decoded state is the output of an entry. A constant start `s0` is
no entry's output, so the decoder never reads the chain from it: the theorem does not apply to
the log as it is. Nor is the constant start harmless in itself: an answer equal to `s0`, a
collision with a constant the adversary knows, would make a chain step from `s0` ambiguous, and
nothing in `Fail` excludes it.

The fix (`startLog s0 ℓ`): read the log as the one where the label's hash is `s0`, the entry
`(batchLabel, s0)` first and the log's own entries at the label dropped. Its lookup is `look ℓ`
on every other input (`look_startLog_of_ne`), so on every chain input; the batching's seedings
`batchSeeds` (the label's hash, then the child count absorbed) seed it at `s0`, so the batching
from `s0` answered by `look ℓ` is the seeded program's run answered by `look (startLog s0 ℓ)`. Its
failure (`Fail` of `startLog s0 ℓ`) adds to the log's exactly the events the constant start
needs: an answer equal to `s0` is a collision with the first entry. Freshness needs nothing
else: the first absorb's input `s0 ‖ (count, 1)` is known in advance, but the challenges are
squeezed after the children's cells are absorbed, which the decoder's order (`lt_of_chunk`) and
the doom certificate track as for any seed.

## The bytecode part

The batching's bytecode side (its lambdas and first sumcheck) is sound alone
(`LeanVM.E2E.Batch.Prog`): the program `bytecodeAny` stops after the bytecode's final check,
whose doom specification tracks only the bytecode's gaps. So the matrix part of the deferred
claim, false in the idealized world, plays no part.

## The statements

* `batchPot s0 bytecode ℓ`: the potential of the bytecode part's certificate (`bytecodeCert`),
  for every child count (`batchSeeds`, counts below `2^64 - 1`), on `startLog s0 ℓ`; one
  function of the log covering every batching instance at once, every node of the aggregation.
  `BatchBad s0 bytecode ℓ` is `1 ≤ batchPot s0 bytecode ℓ`; it includes `Fail` of `startLog s0 ℓ`.
* `bytecodeHolds_of_batchWith` (**the cache form**): on a log that is not batching-bad, every
  batching answered by `look ℓ` from `s0`, of fewer than `2^64 - 1` children of the bytecode's
  shapes, whose deferred claim's bytecode part holds, has children whose bytecode claims hold.
  It is `final_ineq` at the certificate. `children_bytecodeHolds` is it for a node,
  `NodeRelWith (look ℓ) s0 …`, the children's shapes read off their accepted proofs
  (`verifyDeferredWith_shaped`) and their statements.
* `batchPot_step`: one fresh hash query raises the potential, in expectation, by at most
  `2/|E| + 4 (|ℓ| + 2) / |Digest|`; `batchPot_nil`: the empty log has potential `0`.
* `prEvent_game_batchBad_le` (**the probability**): for a game with at most `Q` hash queries,
  `Pr[BatchBad s0 bytecode z.2] ≤ Q · (2/2^192 + 4 (Q + 1)/2^256)`, by the game's engine; the
  batching's own queries are entries of the game's log (V_I's or the prover's), so `Q` counts
  them. `prEvent_game_batchFalse_le` (batchings) and `prEvent_game_childrenFalse_le` (nodes)
  are the events T4 reads, `prEvent_game_batchFalse_le_of_costs` the bound with the game's query
  bound from its parts (`isQueryBoundP_gameComp`).

This is `κ_batch` of `docs/roadmap/e2e-security.md` §0 in the accounting of decision E2E-1, with
the program's own query bound `QV_b` absent (its queries are the game's) and the escape bound
`2/|E|` per query (the lambdas `1/|E|`, the sumcheck's rounds `2/|E|`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The constant start -/

/-- The batching's seedings for every child count below `2^64 - 1`: the label's hash, then the
count absorbed. -/
abbrev batchSeedsAll : Seeds (Fin (2 ^ 64 - 1)) := batchSeeds (2 ^ 64 - 1) le_rfl

/-- **The log read from the constant start `s0`**: the label's hash is `s0`, the log's own
entries at the label dropped. -/
def startLog (s0 : Digest) (ℓ : Log) : Log :=
  (batchLabel, s0) :: ℓ.filter fun e ↦ decide (e.1 ≠ batchLabel)

/-- The label's hash is `s0`. -/
theorem look_startLog_label (s0 : Digest) (ℓ : Log) :
    look (startLog s0 ℓ) batchLabel = some s0 := by
  simp [startLog, look, logLookup_cons]

/-- Dropping the entries at the label keeps the other lookups. -/
theorem look_filter_of_ne {x : Bytes} (hx : x ≠ batchLabel) :
    ∀ ℓ : Log, look (ℓ.filter fun e ↦ decide (e.1 ≠ batchLabel)) x = look ℓ x
  | [] => rfl
  | e :: ℓ => by
    by_cases he : e.1 = batchLabel
    · simp only [List.filter_cons, he, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, look, logLookup_cons]
      split
      · rename_i h
        exact absurd h.symm hx
      · exact look_filter_of_ne hx ℓ
    · simp only [List.filter_cons, ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte, look,
        logLookup_cons]
      split
      · rfl
      · exact look_filter_of_ne hx ℓ

/-- **Off the label, the log read from `s0` answers as the log.** -/
theorem look_startLog_of_ne (s0 : Digest) (ℓ : Log) {x : Bytes} (hx : x ≠ batchLabel) :
    look (startLog s0 ℓ) x = look ℓ x := by
  simp only [startLog, look, logLookup_cons]
  split
  · rename_i h
    exact absurd h.symm hx
  · exact look_filter_of_ne hx ℓ

/-- A chain input is not the label: it has 64 bytes, the label 31. -/
theorem chainInput_ne_label (c : Digest) (x : E) (t : ℕ) :
    digestBytes c ++ blockOf x t ≠ batchLabel := by
  intro h
  have := congrArg List.length h
  rw [List.length_append, digestBytes_length, blockOf_length, batchLabel_length] at this
  omega

/-- The log read from `s0` answers every chain input as the log. -/
theorem look_startLog_chain (s0 : Digest) (ℓ : Log) (c : Digest) (x : E) (t : ℕ) :
    look (startLog s0 ℓ) (digestBytes c ++ blockOf x t) = look ℓ (digestBytes c ++ blockOf x t) :=
  look_startLog_of_ne s0 ℓ (chainInput_ne_label c x t)

/-- A fresh entry at the label leaves the log read from `s0` unchanged. -/
theorem startLog_append_label (s0 : Digest) (ℓ : Log) (u : Digest) :
    startLog s0 (ℓ ++ [(batchLabel, u)]) = startLog s0 ℓ := by
  simp [startLog, List.filter_append]

/-- A fresh entry off the label is appended to the log read from `s0`. -/
theorem startLog_append_of_ne (s0 : Digest) (ℓ : Log) {t : Bytes} (ht : t ≠ batchLabel)
    (u : Digest) : startLog s0 (ℓ ++ [(t, u)]) = startLog s0 ℓ ++ [(t, u)] := by
  simp [startLog, List.filter_append, ht]

/-- The log read from `s0` has at most one entry more than the log. -/
theorem length_startLog_le (s0 : Digest) (ℓ : Log) : (startLog s0 ℓ).length ≤ ℓ.length + 1 := by
  simp only [startLog, List.length_cons]
  have := List.length_filter_le (fun e : Bytes × Digest ↦ decide (e.1 ≠ batchLabel)) ℓ
  omega

/-- An input fresh in the log, off the label, is fresh in the log read from `s0`. -/
theorem not_mem_startLog {s0 : Digest} {ℓ : Log} {t : Bytes} (ht : t ∉ ℓ.map Prod.fst)
    (hl : t ≠ batchLabel) : t ∉ (startLog s0 ℓ).map Prod.fst := by
  intro hm
  simp only [startLog, List.map_cons, List.mem_cons] at hm
  rcases hm with h | h
  · exact hl h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact ht (List.mem_map.mpr ⟨e, (List.mem_filter.mp he).1, rfl⟩)

/-- **The batching from `s0` is the seeded run** on the log read from `s0`: the seeding of the
count `n` computes the count's absorb from `s0`. -/
theorem seed_run_startLog (s0 : Digest) (ℓ : Log) (n : Fin (2 ^ 64 - 1)) :
    (batchSeedsAll.seed n).run (look (startLog s0 ℓ)) =
      look ℓ (digestBytes s0 ++ blockOf (ofK (gpow n)) 1) := by
  simp only [batchSeedsAll, batchSeeds, Seed.run, look_startLog_label, bind, Option.bind_some,
    List.foldlM_cons, List.foldlM_nil, Seed.input, List.nil_append]
  rw [look_startLog_chain]
  cases look ℓ (digestBytes s0 ++ blockOf (ofK (gpow n)) 1) <;> rfl

/-! ## The potential and the bad event -/

/-- **The batching's potential** on the log `ℓ`, from the constant start `s0`: the potential of
the bytecode part's certificate, for every child count, on the log read from `s0` (`0` for a
bytecode whose length is not a power of two, where no deferred claim's bytecode part holds). -/
noncomputable def batchPot (s0 : Digest) (bytecode : List K) (ℓ : Log) : ℝ≥0∞ :=
  if hb : bytecode.length = 2 ^ Nat.log2 bytecode.length then
    pot (bytecodeCert hb).D batchSeedsAll (bytecodeAny bytecode) (startLog s0 ℓ)
  else 0

/-- **The batching's bad event** on the log `ℓ`: its potential is at least one. It holds when the
log read from `s0` fails (`Fail`), a collision or a prediction among its answers, `s0` included. -/
def BatchBad (s0 : Digest) (bytecode : List K) (ℓ : Log) : Prop := 1 ≤ batchPot s0 bytecode ℓ

/-- For a bytecode of a power-of-two length, the batching's potential is the certificate's. -/
theorem batchPot_eq {s0 : Digest} {bytecode : List K} {ℓ : Log}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) :
    batchPot s0 bytecode ℓ =
      pot (bytecodeCert hb).D batchSeedsAll (bytecodeAny bytecode) (startLog s0 ℓ) := by
  unfold batchPot
  split
  · rfl
  · contradiction

/-- A failed log read from `s0` is batching-bad. -/
theorem batchBad_of_fail {s0 : Digest} {bytecode : List K} {ℓ : Log}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hf : Fail batchSeedsAll (startLog s0 ℓ)) : BatchBad s0 bytecode ℓ := by
  rw [BatchBad, batchPot_eq hb]
  simp only [pot, hf, ↓reduceIte, le_refl]

/-- Not batching-bad is a potential below one. -/
theorem not_batchBad_iff {s0 : Digest} {bytecode : List K} {ℓ : Log} :
    ¬ BatchBad s0 bytecode ℓ ↔ batchPot s0 bytecode ℓ < 1 :=
  not_le

/-- A log that is not batching-bad, read from `s0`, has not failed. -/
theorem not_fail_of_not_batchBad {s0 : Digest} {bytecode : List K} {ℓ : Log}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : ¬ BatchBad s0 bytecode ℓ) :
    ¬ Fail batchSeedsAll (startLog s0 ℓ) :=
  fun hf ↦ h (batchBad_of_fail hb hf)

/-! ## The cache form -/

/-- **The batching from the constant start, the cache form.** On a log `ℓ` that is not
batching-bad, every batching answered by `look ℓ` from `s0`, of fewer than `2^64 - 1` children of
the bytecode's shapes, whose deferred claim's bytecode part holds, has children whose bytecode
claims hold: each child's proof's (`FixedClaims.BytecodeHolds`, what the deferring verifier
used) and its statement's (`DeferredClaim.BytecodeHolds`). -/
theorem bytecodeHolds_of_batchWith {s0 : Digest} {bytecode : List K} {ℓ : Log}
    (hgood : ¬ BatchBad s0 bytecode ℓ) {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hn : cs.length < 2 ^ 64 - 1) (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hbw : batchWith (look ℓ) s0 cs h = some (some d)) (hd : d.BytecodeHolds bytecode) :
    ∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode := by
  by_contra hfalse
  have hb : bytecode.length = 2 ^ Nat.log2 bytecode.length := by
    rw [← hd.1.1, hd.2.1]
  apply hgood
  by_cases hf : Fail batchSeedsAll (startLog s0 ℓ)
  · exact batchBad_of_fail hb hf
  show 1 ≤ batchPot s0 bytecode ℓ
  rw [batchPot_eq hb]
  obtain ⟨cv, hcv, hrun⟩ := runProof_bytecodeProg_of_batchWith (H := look ℓ)
    (H' := look (startLog s0 ℓ)) (look_startLog_chain s0 ℓ) hs hbw hd
  let x : Fin (2 ^ 64 - 1) := ⟨cs.length, hn⟩
  have hx : (x : ℕ) < 2 ^ 64 := by have := x.2; omega
  have hv : Rom.verify (look (startLog s0 ℓ)) (batchSeedsAll.seed x)
      (nodeAt (bytecodeAny bytecode) (batchSeedsAll.root x)) ⟨bytecodeStream cs h, []⟩ =
        some true := by
    have hcv' : look ℓ (digestBytes s0 ++ blockOf (ofK (gpow (x : ℕ))) 1) = some cv := hcv
    rw [show batchSeedsAll.root x = countRoot x from rfl, nodeAt_countRoot_bytecode bytecode hx]
    simp only [Rom.verify, seed_run_startLog, hcv', bind, Option.bind_some]
    exact hrun
  exact final_ineq (bytecodeCert hb) hf (rootOk_countRoot_bytecode bytecode hx) hv
    (doomed_of_falseBytecode hb le_rfl hv
      ⟨cs, rfl, hs, List.prefix_append _ _, hfalse⟩)

/-! ## A node's children -/

/-- A relation on two lists relates every element of the first to one of the second. -/
theorem exists_of_forall₂_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ a ∈ l₁, ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- A relation on two lists relates every element of the second to one of the first. -/
theorem exists_of_forall₂_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- The children's claims a node batches are its children's proofs' claims and statements'
deferred claims, in order. -/
theorem childClaimsWith_forall₂ {H : Bytes → Option Digest} {seed : Digest} :
    ∀ {children : List Child} {cs : List ChildClaims}, childClaimsWith H seed children = some cs →
      List.Forall₂ (fun c cc ↦ cc.fresh = c.fresh ∧ cc.carried = c.statement.defer) children cs
  | [], cs, h => by
    simp only [childClaimsWith, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | c :: children, cs, h => by
    simp only [childClaimsWith, List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨cc, ⟨pi, -, rfl⟩, ccs, hccs, rfl⟩ := h
    exact .cons ⟨rfl, rfl⟩ (childClaimsWith_forall₂ hccs)

/-- **A node's children, from the constant start** (what T4 reads): on a log `ℓ` that is not
batching-bad, a node related to its witness with every hash answered by `look ℓ`
(`NodeRelWith (look ℓ) s0 …`), whose deferred claim's bytecode part holds and which has fewer
than `2^64 - 1` children, has children whose bytecode claims hold: each child's proof's, which the
deferring verifier used, and its statement's deferred claim's. -/
theorem children_bytecodeHolds {s0 : Digest} {bytecode : List K} {ℓ : Log}
    (hgood : ¬ BatchBad s0 bytecode ℓ) {pc pr : LeanDa.Digest} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness}
    (hN : NodeRelWith (look ℓ) s0 pc pr bytecode seed s w) (hs : s.defer.BytecodeHolds bytecode)
    (hn : w.children.length < 2 ^ 64 - 1) :
    ∀ c ∈ w.children,
      c.fresh.BytecodeHolds bytecode ∧ c.statement.defer.BytecodeHolds bytecode := by
  obtain ⟨-, hch, -, -, -, hbat⟩ := hN
  by_cases hw : w.children = []
  · intro c hc
    simp [hw] at hc
  simp only [hw, ↓reduceIte] at hbat
  obtain ⟨cs, hcs, hbw⟩ := hbat
  have h2 := childClaimsWith_forall₂ hcs
  have hsh : ∀ cc ∈ cs, ChildShaped bytecode cc := by
    intro cc hcc
    obtain ⟨c, hc, hf, hcar⟩ := exists_of_forall₂_right h2 cc hcc
    obtain ⟨hshc, pi, -, hv⟩ := hch c hc
    exact ⟨by rw [hf]; exact verifyDeferredWith_shaped _ hv, by rw [hcar]; exact hshc⟩
  have hres := bytecodeHolds_of_batchWith hgood (h2.length_eq ▸ hn) hsh hbw hs
  intro c hc
  obtain ⟨cc, hcc, hf, hcar⟩ := exists_of_forall₂_left h2 c hc
  have := hres cc hcc
  rwa [hf, hcar] at this

/-! ## The potential's steps -/

/-- The empty log read from `s0` has not failed: its one entry, the label's, collides with
nothing and is no chunk, root or seeding step. -/
theorem not_fail_startLog_nil (s0 : Digest) : ¬ Fail batchSeedsAll (startLog s0 []) := by
  rintro ⟨i, hi, hbad⟩
  simp only [startLog, List.filter_nil, List.length_cons, List.length_nil, zero_add,
    Nat.lt_one_iff] at hi
  subst hi
  simp only [startLog, List.filter_nil, List.take_zero, List.getElem_cons_zero, BadEntry,
    List.not_mem_nil, false_and, exists_false, List.map_nil, List.mem_singleton,
    exists_eq_left, false_or] at hbad
  rcases hbad with h | h | h | ⟨a, ha, -⟩
  · have := congrArg List.length h
    simp [chunk0, digestBytes_length, batchLabel_length] at this
  · have := congrArg List.length h
    simp [chunk1, digestBytes_length, batchLabel_length] at this
  · obtain ⟨_, _, _, _, -, hf, -⟩ := h
    simp at hf
  · simp [batchSeedsAll, batchSeeds] at ha

/-- The label is no chain input. -/
theorem parse_label : parse batchLabel = none := by
  unfold parse
  split
  · rename_i hex
    obtain ⟨q, -, hq⟩ := hex
    have := congrArg List.length hq
    rw [List.length_append, digestBytes_length, blockOf_length, batchLabel_length] at this
    omega
  · rfl

/-- **The empty log has potential zero**: read from `s0`, its one entry starts nothing. -/
theorem batchPot_nil (s0 : Digest) (bytecode : List K) : batchPot s0 bytecode [] = 0 := by
  unfold batchPot
  split_ifs with hb
  · have hroot : rootAt batchSeedsAll [] batchLabel = none := by
      unfold rootAt
      split
      · rename_i hex
        obtain ⟨x, hx⟩ := hex
        simp [pend, look, logLookup, batchSeedsAll, batchSeeds] at hx
      · rfl
    have hstep : (step batchSeedsAll (bytecodeAny bytecode) [] Dec.init batchLabel).1 =
        Shape.none := by
      simp only [step, hroot, parse_label]
    have hsum : termSum (bytecodeCert hb).D batchSeedsAll (bytecodeAny bytecode)
        (startLog s0 []) = 0 := by
      have hk : (decode batchSeedsAll (bytecodeAny bytecode) (startLog s0 [])).kinds =
          [(Shape.none, s0)] := by
        rw [show startLog s0 [] = [] ++ [(batchLabel, s0)] from rfl, kinds_decode_append,
          decode_nil, hstep]
        rfl
      simp only [termSum, hk, List.map_cons, List.map_nil, term, List.sum_cons, List.sum_nil,
        add_zero]
    simp only [pot, not_fail_startLog_nil, ↓reduceIte, hsum, min_eq_right (zero_le_one' ℝ≥0∞)]
  · rfl

/-- **The potential's step**: one fresh hash query raises the batching's potential, in
expectation, by at most `2/|E| + 4 (|ℓ| + 2) / |Digest|`: the certificate's escape bound and the
failure of the new answer in the log read from `s0`, one entry longer. A fresh query at the label
changes nothing. -/
theorem batchPot_step (s0 : Digest) (bytecode : List K) (ℓ : Log) (t : Bytes)
    (ht : t ∉ ℓ.map Prod.fst) :
    (∑ u, batchPot s0 bytecode (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      batchPot s0 bytecode ℓ +
        (batchε + ((4 * (ℓ.length + 2) : ℕ) : ℝ≥0∞) / Fintype.card Digest) := by
  unfold batchPot
  split_ifs with hb
  · by_cases hl : t = batchLabel
    · subst hl
      simp only [startLog_append_label]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · simp only [startLog_append_of_ne s0 ℓ hl]
      refine (step_ineq (bytecodeCert hb) (bytecodeCert_bound hb) (startLog s0 ℓ) t
        (not_mem_startLog ht hl)).trans (add_le_add le_rfl (add_le_add le_rfl ?_))
      refine ENNReal.div_le_div_right ?_ _
      have hlen := length_startLog_le s0 ℓ
      have hsteps : (batchSeedsAll.steps).length = 0 := rfl
      rw [hsteps]
      exact_mod_cast Nat.mul_le_mul_left 4 (by omega)
  · simp

/-! ## The probability in the game -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The game ends batching-bad with probability at most `Q · (2/2^192 + 4 (Q + 1)/2^256)`**,
for a game with at most `Q` hash queries. -/
theorem prEvent_game_batchBad_le (s0 : Digest) (bytecode : List K) (guest : Semantics.Program)
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[BatchBad s0 bytecode z.2] ≤
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) := by
  have h := prEvent_game_le_of_freshStepBelow (Φ := batchPot s0 bytecode)
    (δ := batchε + ((4 * (Q + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest) Q
    (fun ℓ t hℓ ht ↦ by
      refine (batchPot_step s0 bytecode ℓ t ht).trans (add_le_add le_rfl (add_le_add le_rfl ?_))
      refine ENNReal.div_le_div_right ?_ _
      exact_mod_cast Nat.mul_le_mul_left 4 (by omega))
    guest fuel budget A Q hQ le_rfl (fun _ ℓ ↦ BatchBad s0 bytecode ℓ) (fun _ _ hz ↦ hz)
  rw [batchPot_nil, zero_add] at h
  refine h.trans (le_of_eq ?_)
  have hE : ∀ i : Fintype E, @Fintype.card E i = 2 ^ 192 := fun i ↦ by
    convert card_E
  rw [batchε, hE, card_digest]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- **The batching leg in the game.** The final log answers a batching from `s0` of fewer than
`2^64 - 1` children of the bytecode's shapes, whose deferred claim's bytecode part holds while
some child's bytecode claim is false, with probability at most
`Q · (2/2^192 + 4 (Q + 1)/2^256)`, for a game with at most `Q` hash queries. -/
theorem prEvent_game_batchFalse_le (s0 : Digest) (bytecode : List K) (guest : Semantics.Program)
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[∃ (cs : List ChildClaims) (h : BatchHints)
        (d : DeferredClaim), cs.length < 2 ^ 64 - 1 ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
        batchWith (look z.2) s0 cs h = some (some d) ∧ d.BytecodeHolds bytecode ∧
        ¬ ∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode] ≤
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz ↦ ?_)
    (prEvent_game_batchBad_le s0 bytecode guest fuel budget A Q hQ)
  obtain ⟨cs, h, d, hn, hs, hbw, hd, hfalse⟩ := hz
  by_contra hbad
  exact hfalse (bytecodeHolds_of_batchWith hbad hn hs hbw hd)

/-- **A node's children in the game.** The final log answers a node related to its witness
(`NodeRelWith (look z.2) s0 …`) with fewer than `2^64 - 1` children, whose deferred claim's bytecode
part holds while some child's bytecode claim is false, with probability at most
`Q · (2/2^192 + 4 (Q + 1)/2^256)`, for a game with at most `Q` hash queries. -/
theorem prEvent_game_childrenFalse_le (s0 : Digest) (bytecode : List K) (pc pr : LeanDa.Digest)
    (guest : Semantics.Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[∃ (seed : Digest) (s : NodeStatement) (w : NodeWitness),
        NodeRelWith (look z.2) s0 pc pr bytecode seed s w ∧ s.defer.BytecodeHolds bytecode ∧
        w.children.length < 2 ^ 64 - 1 ∧
        ¬ ∀ c ∈ w.children, c.fresh.BytecodeHolds bytecode ∧
          c.statement.defer.BytecodeHolds bytecode] ≤
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) := by
  refine le_trans (prEvent_mono_of_support _ _ _ fun z _ hz ↦ ?_)
    (prEvent_game_batchBad_le s0 bytecode guest fuel budget A Q hQ)
  obtain ⟨seed, s, w, hN, hs, hn, hfalse⟩ := hz
  by_contra hbad
  exact hfalse (children_bytecodeHolds hbad hN hs hn)

/-- **The batching leg in the game, with the game's query bound from its parts**: the honest
signers' costs, the adversary's hash queries and signing requests, and V_I's budget. -/
theorem prEvent_game_batchFalse_le_of_costs (s0 : Digest) (bytecode : List K)
    {cxk csk cxs css : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Semantics.Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    let Q := nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget
    Pr{let z ← game guest fuel budget A}[∃ (cs : List ChildClaims) (h : BatchHints)
        (d : DeferredClaim), cs.length < 2 ^ 64 - 1 ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
        batchWith (look z.2) s0 cs h = some (some d) ∧ d.BytecodeHolds bytecode ∧
        ¬ ∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode] ≤
      Q * (2 / 2 ^ 192 + 4 * (Q + 1) / 2 ^ 256) :=
  prEvent_game_batchFalse_le s0 bytecode guest fuel budget A _
    (isQueryBoundP_gameComp hxk hsk hxs hss guest fuel budget A hH hX hS)

end Game

end
end LeanVM.E2E
