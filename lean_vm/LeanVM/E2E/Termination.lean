/-
  LeanVM.E2E.Termination

  Termination of the aggregation's child relation (T3 of `docs/roadmap/e2e-security.md`): on a
  log without failure and without a prediction of a batching's last challenge, a child's
  statement digest is answered before its parent's, and the game ends with such a prediction
  with probability at most `Q (Q + 1) / 2^193`.
-/

module

public import LeanVM.E2E.Batch

/-!
# Termination (T3)

V_I closes the nodes of an idealized proof under the children each candidate decodes
(`closure`, `LeanVM/E2E/Statement.lean`). A claim of the root is held by a direct witness or by
a child, whose statement holds it again; T4 follows the children down, and needs the descent to
end. It ends because a child's statement digest is an *earlier entry* of the oracle's log than
its parent's: the **rank** of a node is the index of the log entry answering its statement
digest.

**The child's digest is absorbed before the parent's challenges** (`absorbed_batchWith`). The
parent's batching (`batchWith`, the deferred claims of its children) observes each child's
public input, the child's statement digest, as its two halves; the entry observing the second
half completes the digest as a root (`RootOf`), so the child's digest entry comes before it
(`lt_of_rootOf`), and every later step of the chain comes after its predecessor
(`lt_of_chunk`): along an answered chain the entries grow (`ChainLE`). The chain ends with the
matrices' sumcheck, whose last challenge is the last coordinate of the parent's deferred
matrix point (`getLast_batchRoundsWith`).

**The parent's digest hashes that challenge** (`slice_statementInput`). The parent's statement
bytes carry its deferred claim's cells at fixed offsets; the last matrix coordinate sits at
`predOffset bytecode = 96 + 24 (log₂ |bytecode| + 2 · blake2sR1csLogSize)` for a claim of the
bytecode's shape (`DeferredClaim.Shaped`).

**The prediction event** (`Pred o ℓ`): an entry's input carries, at the offset `o`, the 24 bytes
of the challenge of an answer of the same or a later entry. Without it, the parent's statement
entry comes after the batching's last entry, so after the child's statement entry
(`rank_lt_of_child`, the cache form of T3).

**The probability** (`prEvent_game_pred_le`). A fresh answer's challenge is uniform in `E`
(`sum_challengeOf_div`), so it equals the slice of one of the `|ℓ| + 1` inputs with probability
at most `(|ℓ| + 1)/|E|`; summed over at most `Q` fresh answers, with the potential
`ind (Pred o ℓ) + Σ_{|ℓ| ≤ k < Q} (k + 1)/|E|` (no step raises it), the game ends with a
prediction with probability at most `Q (Q + 1) / 2^193 ≤ (Q + 1)² / 2^193`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/- `E`'s enumeration is the repository's (`sum_challengeOf_div`), not leanDA's. -/
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-! ## The order of a chain's entries -/

section Chain

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **`b` follows `a` on the log `ℓ`**: equal, or `b` is the answer of an entry after every entry
answering `a`. -/
def ChainLE (ℓ : Log) (a b : Digest) : Prop :=
  a = b ∨ ∃ (j : ℕ) (hj : j < ℓ.length), ℓ[j].2 = b ∧
    ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = a → i < j

/-- Every state follows itself. -/
theorem ChainLE.refl (ℓ : Log) (a : Digest) : ChainLE ℓ a a := Or.inl rfl

/-- Following is transitive. -/
theorem ChainLE.trans {a b c : Digest} (h₁ : ChainLE ℓ a b) (h₂ : ChainLE ℓ b c) :
    ChainLE ℓ a c := by
  rcases h₁ with rfl | ⟨j₁, hj₁, hb, h₁⟩
  · exact h₂
  rcases h₂ with rfl | ⟨j₂, hj₂, hc, h₂⟩
  · exact Or.inr ⟨j₁, hj₁, hb, h₁⟩
  exact Or.inr ⟨j₂, hj₂, hc, fun i hi ha ↦ (h₁ i hi ha).trans (h₂ j₁ hj₁ hb)⟩

/-- **A chain step's entry**: without failure, the entry answering `cv ‖ b` comes after every
entry answering `cv`. -/
theorem chain_step (hf : ¬ Fail σ ℓ) {cv cv' : Digest} {b : Bytes}
    (h : look ℓ (digestBytes cv ++ b) = some cv') :
    ∃ (j : ℕ) (hj : j < ℓ.length), ℓ[j] = (digestBytes cv ++ b, cv') ∧
      look (ℓ.take j) (digestBytes cv ++ b) = none ∧
      ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = cv → i < j := by
  obtain ⟨j, hj, hej, hn⟩ := (look_eq_some_iff ℓ _ _).mp h
  refine ⟨j, hj, hej, hn, fun i hi hcv ↦ lt_of_chunk hf hi hj (Or.inl ?_)⟩
  rw [hej, hcv]
  exact chunk0_append _ _

/-- A chain step follows its state. -/
theorem chainLE_step (hf : ¬ Fail σ ℓ) {cv cv' : Digest} {b : Bytes}
    (h : look ℓ (digestBytes cv ++ b) = some cv') : ChainLE ℓ cv cv' := by
  obtain ⟨j, hj, hej, -, hlt⟩ := chain_step hf h
  exact Or.inr ⟨j, hj, by rw [hej], hlt⟩

/-- Absorbing scalars follows the state. -/
theorem chainLE_obsAllW (hf : ¬ Fail σ ℓ) :
    ∀ (xs : List E) (cv cv' : Digest), obsAllW (look ℓ) cv xs = some cv' → ChainLE ℓ cv cv'
  | [], cv, cv', h => by
    simp only [obsAllW, List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    exact ChainLE.refl _ _
  | x :: xs, cv, cv', h => by
    rw [obsAllW_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    exact (chainLE_step hf hc).trans (chainLE_obsAllW hf xs c cv' h)

/-- Two squeezes per child follow the state. -/
theorem chainLE_sq2W (hf : ¬ Fail σ ℓ) :
    ∀ (n : ℕ) (cv : Digest) {ls : List (E × E)} {cv' : Digest},
      sq2W (look ℓ) n cv = some (ls, cv') → ChainLE ℓ cv cv'
  | 0, cv, ls, cv', h => by
    simp only [sq2W, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ChainLE.refl _ _
  | n + 1, cv, ls, cv', h => by
    simp only [sq2W, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, r, hr, he⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact ((chainLE_step hf h1).trans (chainLE_step hf h2)).trans (chainLE_sq2W hf n c2 hr)

/-- Three squeezes per child follow the state. -/
theorem chainLE_sq3W (hf : ¬ Fail σ ℓ) :
    ∀ (n : ℕ) (cv : Digest) {ls : List (E × E × E)} {cv' : Digest},
      sq3W (look ℓ) n cv = some (ls, cv') → ChainLE ℓ cv cv'
  | 0, cv, ls, cv', h => by
    simp only [sq3W, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ChainLE.refl _ _
  | n + 1, cv, ls, cv', h => by
    simp only [sq3W, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, c3, h3, r, hr, he⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact (((chainLE_step hf h1).trans (chainLE_step hf h2)).trans
      (chainLE_step hf h3)).trans (chainLE_sq3W hf n c3 hr)

/-- A sumcheck's rounds follow the state. -/
theorem chainLE_batchRoundsWith (hf : ¬ Fail σ ℓ) :
    ∀ (rounds : List (E × E)) (claim : E) (cv : Digest) {r : (List E × E) × Digest},
      (batchRoundsWith (look ℓ) claim rounds).run cv = some r → ChainLE ℓ cv r.2
  | [], claim, cv, r, h => by
    simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ChainLE.refl _ _
  | (g1, gInf) :: rounds, claim, cv, r, h => by
    rw [batchRoundsWith_run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c2, h2, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c3, h3, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact (((chainLE_step hf h1).trans (chainLE_step hf h2)).trans
      (chainLE_step hf h3)).trans (chainLE_batchRoundsWith hf rounds _ c3 (r := r') hr')

/-- **The last challenge of a sumcheck is the final state's**: a nonempty sumcheck's last
challenge is the challenge of the chain state it ends at. -/
theorem getLast_batchRoundsWith {H : Bytes → Option Digest} :
    ∀ (rounds : List (E × E)) (claim : E) (cv : Digest) {rs : List E} {fin : E} {cv' : Digest},
      (batchRoundsWith H claim rounds).run cv = some ((rs, fin), cv') → rounds ≠ [] →
        rs.getLast? = some (challengeOf cv')
  | [], _, _, _, _, _, _, hne => absurd rfl hne
  | (g1, gInf) :: rounds, claim, cv, rs, fin, cv', h, _ => by
    rw [batchRoundsWith_run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c1, -, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c2, -, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c3, -, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨⟨rs', fin'⟩, cv''⟩, hr', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    rcases rounds with _ | ⟨rd, rounds⟩
    · simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hr'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr'
      rfl
    · have hl := length_batchRoundsWith H _ _ _ hr'
      have ih := getLast_batchRoundsWith (rd :: rounds) _ c3 hr' (List.cons_ne_nil _ _)
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, rs' = x :: xs :=
        List.exists_cons_of_length_pos (by rw [hl]; simp)
      rw [List.getLast?_cons_cons]
      exact ih

end Chain

/-! ## A child's digest is absorbed -/

section Absorbed

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **The digest `pc` is absorbed before the chain state `cv`**: an entry answering `pc` comes
before an entry whose answer `cv` follows. -/
def Absorbed (ℓ : Log) (pc cv : Digest) : Prop :=
  ∃ (i j : ℕ) (hi : i < ℓ.length) (hj : j < ℓ.length), ℓ[i].2 = pc ∧ i < j ∧
    ChainLE ℓ ℓ[j].2 cv

/-- Absorbed before a state, absorbed before every state following it. -/
theorem Absorbed.chain {pc a b : Digest} (h : Absorbed ℓ pc a) (hab : ChainLE ℓ a b) :
    Absorbed ℓ pc b := by
  obtain ⟨i, j, hi, hj, hpc, hij, hc⟩ := h
  exact ⟨i, j, hi, hj, hpc, hij, hc.trans hab⟩

/-- A state absorbed before is the answer of an entry after the digest's. -/
theorem Absorbed.exists_lt {pc cv : Digest} (h : Absorbed ℓ pc cv) :
    ∃ (i k : ℕ) (hi : i < ℓ.length) (hk : k < ℓ.length), ℓ[i].2 = pc ∧ i < k ∧ ℓ[k].2 = cv := by
  obtain ⟨i, j, hi, hj, hpc, hij, hc⟩ := h
  rcases hc with hc | ⟨k, hk, hkc, hlt⟩
  · exact ⟨i, j, hi, hj, hpc, hij, hc⟩
  · exact ⟨i, k, hi, hk, hpc, hij.trans (hlt j hj rfl), hkc⟩

/-- **Observing a digest's two halves absorbs it**: without failure, the entry observing the
second half completes the digest as a root (`RootOf`), so comes after the digest's entry. -/
theorem absorbed_obsAllW_pair (hf : ¬ Fail σ ℓ) {pc cv cv' : Digest} {rest : List E}
    (hpc : ∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = pc)
    (h : obsAllW (look ℓ) cv ((digestScalars pc).1 :: (digestScalars pc).2 :: rest) =
      some cv') :
    Absorbed ℓ pc cv' := by
  rw [obsAllW_cons, Option.bind_eq_some_iff] at h
  obtain ⟨c1, h1, h⟩ := h
  rw [obsAllW_cons, Option.bind_eq_some_iff] at h
  obtain ⟨c2, h2, h⟩ := h
  obtain ⟨k, hk, hek, -, -⟩ := chain_step hf h1
  obtain ⟨j, hj, hej, -, hkj⟩ := chain_step hf h2
  have hkj' : k < j := hkj k hk (by rw [hek])
  obtain ⟨i, hi, hpi⟩ := hpc
  have hroot : RootOf (ℓ.take j) ℓ[j].1 pc := by
    refine ⟨c1, (digestScalars pc).1, (digestScalars pc).2, ℓ[k], by rw [hej], ?_, ?_,
      by rw [digestOfScalars_digestScalars]⟩
    · rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simp [hek], k, by simp; omega, by simp, fun m hm ↦ ?_⟩
      have hm' : m < ℓ.length := by omega
      simp only [List.getElem_take]
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro he
      exact output_ne hf hm' hk hm (by rw [he, hek])
    · rw [hek]
      simp [digestBytes_length]
  exact ⟨i, j, hi, hj, hpi, lt_of_rootOf hf hi hj (by rw [hpi]; exact hroot),
    by rw [hej]; exact chainLE_obsAllW hf rest c2 cv' h⟩

/-- A child's cells: its public input's two halves, its fixed claims, its carried claim. -/
theorem childCells_eq (c : ChildClaims) :
    childCells c = (digestScalars c.publicInput).1 :: (digestScalars c.publicInput).2 ::
      (fixedCells c.fresh ++ c.carried.cells) := by
  simp [childCells]

/-- **Absorbing the children's cells absorbs every child's public input** whose digest the log
answers. -/
theorem absorbed_obsAllW_children (hf : ¬ Fail σ ℓ) :
    ∀ (cs : List ChildClaims) (cv cv' : Digest),
      obsAllW (look ℓ) cv (cs.flatMap childCells) = some cv' → ∀ c ∈ cs,
        (∃ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = c.publicInput) → Absorbed ℓ c.publicInput cv'
  | [], _, _, _, c, hc, _ => absurd hc List.not_mem_nil
  | c :: cs, cv, cv', h, c', hc', hpc => by
    rw [List.flatMap_cons, obsAllW_append, Option.bind_eq_some_iff] at h
    obtain ⟨cv1, h1, h2⟩ := h
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [childCells_eq] at h1
      exact (absorbed_obsAllW_pair hf hpc h1).chain (chainLE_obsAllW hf _ _ _ h2)
    · exact absorbed_obsAllW_children hf cs cv1 cv' h2 c' hc' hpc

end Absorbed

/-! ## The batching's last challenge -/

section Batching

variable {H : Bytes → Option Digest}

/-- **`batchWith`, unrolled to its end**: a batching that defers `d` absorbed the count and the
cells from `s0`, squeezed the bytecode's lambdas, ran the bytecode's sumcheck, squeezed the
matrices' lambdas, and ran the matrices' sumcheck, whose challenges are `d`'s matrix point. -/
theorem batchWith_some_full {s0 : Digest} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hbw : batchWith H s0 cs h = some (some d)) :
    ∃ cvA lB cv1 rB fB cv2 lM cv3 cM fM cv4,
      obsAllW H s0 (ofK (gpow cs.length) :: cs.flatMap childCells) = some cvA ∧
      sq2W H cs.length cvA = some (lB, cv1) ∧
      (batchRoundsWith H (claimBOf cs lB) h.bytecodeRounds).run cv1 = some ((rB, fB), cv2) ∧
      sq3W H cs.length cv2 = some (lM, cv3) ∧
      (batchRoundsWith H cM h.matrixRounds).run cv3 = some ((d.matrixPoint, fM), cv4) := by
  simp only [batchWith, batchWith.go, StateT.run'_eq, StateT.run_bind, observeWith_run,
    forIn_childrenW, forIn_sq2W, forIn_sq3W] at hbw
  simp only [Option.map_eq_map, Option.bind_eq_bind, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at hbw
  obtain ⟨r, ⟨_, ⟨cvc, hcvc, rfl⟩, _, ⟨cvA, hcvA, rfl⟩, _, ⟨⟨lB, cv1⟩, hsq, rfl⟩,
    ⟨⟨rB, fB⟩, cv2⟩, hrB, _, ⟨⟨lM, cv3⟩, hsq3, rfl⟩, ⟨⟨rM, fM⟩, cv4⟩, hrM, hif⟩, hd⟩ := hbw
  simp only [List.nil_append] at hrB hif hrM hsq3
  split_ifs at hif with hc
  · simp only [StateT.run_pure, Option.pure_def, Option.some.injEq] at hif
    subst hif
    simp only [Option.some.injEq] at hd
    subst hd
    refine ⟨cvA, lB, cv1, rB, fB, cv2, lM, cv3, _, fM, cv4, ?_, hsq, hrB, hsq3, hrM⟩
    rw [obsAllW_cons, hcvc]
    exact hcvA
  · simp only [StateT.run_pure, Option.pure_def, Option.some.injEq] at hif
    subst hif
    simp at hd

end Batching

/-! ## The statement's bytes -/

section Statement

/-- **The bytes a statement digest hashes**, from the seed, the signer set's digest `sd`, the
DA list's digest `dd` and the deferred claim `d`: the three digests, the cells (an odd count
paired with a zero cell), zero-filled to whole 64-byte blocks (`statementDigestWith`). -/
def stmtInput (seed sd dd : Digest) (d : DeferredClaim) : Bytes :=
  let cells := d.cells ++ if d.cells.length % 2 = 1 then [0] else []
  let bytes := digestBytes seed ++ digestBytes sd ++ digestBytes dd ++ cells.flatMap eBytes
  bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0

/-- **An answered statement digest** hashes the statement's bytes, its nested digests
answered. -/
theorem statementDigestWith_eq_some {H : Bytes → Option Digest} {seed pi : Digest}
    {s : NodeStatement} (h : statementDigestWith H seed s = some pi) :
    ∃ sd dd, signersDigestWith H s.claims.xmss s.claims.sphincs = some sd ∧
      daListDigestWith H s.claims.da = some dd ∧ H (stmtInput seed sd dd s.defer) = some pi := by
  simp only [statementDigestWith, bind, Option.bind_eq_some_iff] at h
  obtain ⟨sd, hsd, dd, hdd, h⟩ := h
  exact ⟨sd, dd, hsd, hdd, h⟩

/-- **A cell in fixed-width bytes**: the 24 bytes after a prefix and `k` cells are cell `k`'s. -/
theorem slice_flatMap_eBytes (pre rest : Bytes) {l : List E} {k : ℕ} (hk : k < l.length) :
    ((pre ++ (l.flatMap eBytes ++ rest)).drop (pre.length + 24 * k)).take 24 = eBytes l[k] := by
  rw [← List.drop_drop, List.drop_left' rfl]
  have hfl : ∀ (l : List E) (k : ℕ), k < l.length →
      (l.flatMap eBytes ++ rest).drop (24 * k) =
        eBytes l[k]! ++ ((l.drop (k + 1)).flatMap eBytes ++ rest) := by
    intro l k hk
    induction l generalizing k with
    | nil => simp at hk
    | cons a l ih =>
      rcases k with _ | k
      · simp
      · rw [List.flatMap_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm, ← List.drop_drop,
          List.drop_left' (by rfl)]
        simp only [List.length_cons] at hk
        rw [ih k (by omega)]
        simp
  rw [hfl l k hk, List.take_left' (by rw [getElem!_pos l k hk]; rfl), getElem!_pos l k hk]

/-- **The last matrix coordinate in the statement's bytes**: the 24 bytes at offset
`96 + 24 (|bytecode point| + |matrix point|)` are its encoding. -/
theorem slice_stmtInput (seed sd dd : Digest) {d : DeferredClaim} {x : E}
    (hx : d.matrixPoint.getLast? = some x) :
    ((stmtInput seed sd dd d).drop
      (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length))).take 24 = eBytes x := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hx
  set pad : List E := if d.cells.length % 2 = 1 then [0] else []
  have hcells : d.cells = (d.bytecodePoint ++ [d.bytecodeValue] ++ ys) ++
      x :: [d.matrixA, d.matrixB] := by
    simp [DeferredClaim.cells, hys]
  have hk : d.bytecodePoint.length + d.matrixPoint.length < (d.cells ++ pad).length := by
    rw [List.length_append, hcells]
    simp [hys]
    omega
  have hget : (d.cells ++ pad)[d.bytecodePoint.length + d.matrixPoint.length] = x := by
    rw [List.getElem_append_left (by rw [hcells]; simp [hys])]
    simp only [hcells]
    rw [List.getElem_append_right (by simp [hys])]
    simp [hys]
  have e : stmtInput seed sd dd d = (digestBytes seed ++ digestBytes sd ++ digestBytes dd) ++
      ((d.cells ++ pad).flatMap eBytes ++ List.replicate
        ((64 - (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
          (d.cells ++ pad).flatMap eBytes).length % 64) % 64) 0) := by
    simp only [stmtInput, pad, List.append_assoc]
  rw [e, show 96 = (digestBytes seed ++ digestBytes sd ++ digestBytes dd).length by
    simp [digestBytes_length], slice_flatMap_eBytes _ _ hk, hget]

end Statement

/-! ## The prediction event and the rank -/

section Rank

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **The prediction event at offset `o`**: an entry's input carries, at the offset `o`, the 24
bytes of the challenge of the answer of the same or a later entry. -/
def Pred (o : ℕ) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length) (j : ℕ) (hj : j ≤ i),
    ((ℓ[j]'(Nat.lt_of_le_of_lt hj hi)).1.drop o).take 24 = eBytes (challengeOf ℓ[i].2)

/-- **The offset of the last matrix coordinate** in the statement bytes of a deferred claim of
the bytecode's shape. -/
def predOffset (bytecode : List K) : ℕ :=
  96 + 24 * (Nat.log2 bytecode.length + 2 * blake2sR1csLogSize)

/-- **T3, the cache form: a child's digest is answered before its parent's.** On a log without
failure and without a prediction at the offset of the parent's last matrix coordinate, if the
parent's statement bytes, of a deferred claim with a nonempty matrix point, are answered by
`pi`, and the batching from `s0` of children `cs` deferred that claim, then for every child whose
public input the log answers, the entry answering it comes before the entry answering `pi`. -/
theorem rank_lt_of_child (hf : ¬ Fail σ ℓ) {seed sd dd pi : Digest} {d : DeferredClaim}
    (hP : ¬ Pred (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length)) ℓ)
    (hpi : look ℓ (stmtInput seed sd dd d) = some pi) (hm : d.matrixPoint ≠ [])
    {s0 : Digest} {cs : List ChildClaims} {h : BatchHints}
    (hbw : batchWith (look ℓ) s0 cs h = some (some d)) {c : ChildClaims} (hc : c ∈ cs)
    {i p : ℕ} (hi : i < ℓ.length) (hp : p < ℓ.length) (hci : ℓ[i].2 = c.publicInput)
    (hpp : ℓ[p].2 = pi) : i < p := by
  obtain ⟨cvA, lB, cv1, rB, fB, cv2, lM, cv3, cM, fM, cv4, hA, h1, h2, h3, h4⟩ :=
    batchWith_some_full hbw
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv0, -, hA⟩ := hA
  have hab := absorbed_obsAllW_children hf cs cv0 cvA hA c hc ⟨i, hi, hci⟩
  have hc4 : ChainLE ℓ cvA cv4 :=
    (((chainLE_sq2W hf _ _ h1).trans (chainLE_batchRoundsWith hf _ _ _ h2)).trans
      (chainLE_sq3W hf _ _ h3)).trans (chainLE_batchRoundsWith hf _ _ _ h4)
  obtain ⟨i', k, hi', hk, hci', hik, hck⟩ := (hab.chain hc4).exists_lt
  obtain rfl : i' = i := index_eq_of_output hf hi' hi (by rw [hci', hci])
  have hround : h.matrixRounds ≠ [] := by
    intro he
    have hl := length_batchRoundsWith (look ℓ) _ _ _ h4
    rw [he] at hl
    exact hm (List.eq_nil_of_length_eq_zero hl)
  have hlast := getLast_batchRoundsWith _ _ _ h4 hround
  obtain ⟨p', hp', hep, -⟩ := (look_eq_some_iff ℓ _ _).mp hpi
  obtain rfl : p' = p := index_eq_of_output hf hp' hp (by rw [hep, hpp])
  have hkp : k < p' := by
    by_contra hle
    refine hP ⟨k, hk, p', by omega, ?_⟩
    rw [hep, hck]
    exact slice_stmtInput seed sd dd hlast
  omega

end Rank

/-! ## The probability of a prediction -/

section Prob

/-- A prediction in a log with one more entry is one in the log, or the new answer's challenge
is the slice of an input. -/
theorem pred_append {o : ℕ} {ℓ : Log} {t : Bytes} {u : Digest} (h : Pred o (ℓ ++ [(t, u)])) :
    Pred o ℓ ∨ ∃ x ∈ t :: ℓ.map Prod.fst, (x.drop o).take 24 = eBytes (challengeOf u) := by
  obtain ⟨i, hi, j, hj, heq⟩ := h
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hil : i < ℓ.length
  · refine Or.inl ⟨i, hil, j, hj, ?_⟩
    rw [List.getElem_append_left (Nat.lt_of_le_of_lt hj hil), List.getElem_append_left hil] at heq
    exact heq
  · obtain rfl : i = ℓ.length := by omega
    rw [List.getElem_append_right (le_refl _)] at heq
    simp only [Nat.sub_self, List.getElem_singleton] at heq
    refine Or.inr ?_
    by_cases hjl : j < ℓ.length
    · rw [List.getElem_append_left hjl] at heq
      exact ⟨ℓ[j].1, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ℓ[j], List.getElem_mem _, rfl⟩), heq⟩
    · obtain rfl : j = ℓ.length := by omega
      rw [List.getElem_append_right (le_refl _)] at heq
      simp only [Nat.sub_self, List.getElem_singleton] at heq
      exact ⟨t, List.mem_cons_self, heq⟩

/-- The average of a constant plus a function of a uniform digest. -/
theorem avg_const_add (c : ℝ≥0∞) (g : Digest → ℝ≥0∞) :
    (∑ u, (c + g u)) / Fintype.card Digest = c + (∑ u, g u) / Fintype.card Digest := by
  rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)]

/-- **A fresh answer predicts a slice of one of the inputs** with probability at most the
number of inputs over `|E|`. -/
theorem avg_ind_predicts (o : ℕ) (X : List Bytes) :
    (∑ u : Digest, ind (∃ x ∈ X, (x.drop o).take 24 = eBytes (challengeOf u))) /
      Fintype.card Digest ≤ (X.length : ℝ≥0∞) / 2 ^ 192 := by
  have hs := sum_challengeOf_div (fun c ↦ ind (∃ x ∈ X, (x.drop o).take 24 = eBytes c))
  have hcard : ∀ inst : Fintype E, @Fintype.card E inst = 2 ^ 192 := fun _ ↦ BF64.card_ext3
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at hs
  refine (le_of_eq hs).trans (ENNReal.div_le_div_right ?_ _)
  calc ∑ c : E, ind (∃ x ∈ X, (x.drop o).take 24 = eBytes c)
      ≤ ∑ c : E, (X.map fun x ↦ ind ((x.drop o).take 24 = eBytes c)).sum :=
        Finset.sum_le_sum fun c _ ↦ ind_exists_le X _
    _ = (X.map fun x ↦ ∑ c : E, ind ((x.drop o).take 24 = eBytes c)).sum :=
        sum_list_sum_comm X fun x c ↦ ind ((x.drop o).take 24 = eBytes c)
    _ ≤ X.length * 1 := list_sum_le X _ 1 fun x _ ↦
        sum_ind_le_one fun c c' hc hc' ↦ Guest.Binding.eBytes_inj (hc.symm.trans hc')
    _ = X.length := mul_one _

/-- The potential's budget: the probabilities still to be spent by the fresh answers from the
`n`-th to the `N`-th. -/
noncomputable def predBudget (n N : ℕ) : ℝ≥0∞ :=
  ((∑ k ∈ Finset.Ico n N, (k + 1) : ℕ) : ℝ≥0∞) / 2 ^ 192

/-- One fresh answer spends `(n + 1) / |E|` of the budget. -/
theorem predBudget_succ {n N : ℕ} (h : n < N) :
    predBudget n N = ((n + 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + predBudget (n + 1) N := by
  rw [predBudget, predBudget, Finset.sum_eq_sum_Ico_succ_bot h, Nat.cast_add, ENNReal.add_div]

/-- **The prediction's potential** for at most `N` fresh answers: the indicator of a
prediction, and the budget left. -/
noncomputable def predPot (o N : ℕ) (ℓ : Log) : ℝ≥0∞ := ind (Pred o ℓ) + predBudget ℓ.length N

/-- **No fresh answer raises the prediction's potential**, at logs shorter than `N`. -/
theorem predPot_step (o N : ℕ) (ℓ : Log) (t : Bytes) (hN : ℓ.length < N) :
    (∑ u, predPot o N (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ predPot o N ℓ + 0 := by
  rw [add_zero]
  have hpt : ∀ u, predPot o N (ℓ ++ [(t, u)]) ≤
      (ind (Pred o ℓ) + predBudget (ℓ.length + 1) N) +
        ind (∃ x ∈ t :: ℓ.map Prod.fst, (x.drop o).take 24 = eBytes (challengeOf u)) := by
    intro u
    rw [predPot, List.length_append, List.length_singleton]
    calc ind (Pred o (ℓ ++ [(t, u)])) + predBudget (ℓ.length + 1) N
        ≤ (ind (Pred o ℓ) + ind (∃ x ∈ t :: ℓ.map Prod.fst,
            (x.drop o).take 24 = eBytes (challengeOf u))) + predBudget (ℓ.length + 1) N :=
          add_le_add ((ind_mono pred_append).trans (ind_or_le _ _)) le_rfl
      _ = _ := by ring
  calc (∑ u, predPot o N (ℓ ++ [(t, u)])) / Fintype.card Digest
      ≤ (∑ u, ((ind (Pred o ℓ) + predBudget (ℓ.length + 1) N) +
          ind (∃ x ∈ t :: ℓ.map Prod.fst, (x.drop o).take 24 = eBytes (challengeOf u)))) /
          Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
    _ = (ind (Pred o ℓ) + predBudget (ℓ.length + 1) N) +
          (∑ u, ind (∃ x ∈ t :: ℓ.map Prod.fst, (x.drop o).take 24 = eBytes (challengeOf u))) /
            Fintype.card Digest := avg_const_add _ _
    _ ≤ (ind (Pred o ℓ) + predBudget (ℓ.length + 1) N) +
          ((t :: ℓ.map Prod.fst).length : ℝ≥0∞) / 2 ^ 192 :=
        add_le_add le_rfl (avg_ind_predicts o _)
    _ = predPot o N ℓ := by
      rw [predPot, predBudget_succ hN, List.length_cons, List.length_map]
      push_cast
      ring

/-- The empty log has no prediction. -/
theorem not_pred_nil (o : ℕ) : ¬ Pred o [] := fun ⟨_, hi, _⟩ ↦ by simp at hi

/-- **The potential of the empty log**: `N (N + 1) / 2^193`. -/
theorem predPot_nil (o N : ℕ) : predPot o N [] = N * (N + 1) / 2 ^ 193 := by
  rw [predPot, ind_of_not (not_pred_nil o), zero_add, predBudget, List.length_nil,
    ← Finset.range_eq_Ico]
  have hg : (∑ k ∈ Finset.range N, (k + 1)) * 2 = N * (N + 1) := by
    induction N with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have h2 : ((∑ k ∈ Finset.range N, (k + 1) : ℕ) : ℝ≥0∞) = (N * (N + 1) : ℕ) / 2 := by
    rw [← hg, Nat.cast_mul, Nat.cast_ofNat, ENNReal.mul_div_cancel_right (by norm_num)
      (by norm_num)]
  rw [h2, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, mul_assoc, ← ENNReal.mul_inv (by simp) (by simp)]
  congr 2
  norm_num

end Prob

/-! ## The game -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **T3's probability: the game ends with a prediction with probability at most
`Q (Q + 1) / 2^193`**, at any offset, for a game with at most `Q` hash queries. -/
theorem prEvent_game_pred_le (o : ℕ) (guest : Semantics.Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred o z.2] ≤ Q * (Q + 1) / 2 ^ 193 := by
  have h := prEvent_game_le_of_freshStepBelow (Φ := predPot o Q) (δ := 0) Q
    (fun ℓ t hℓ _ ↦ predPot_step o Q ℓ t hℓ) guest fuel budget A Q hQ le_rfl
    (fun _ ℓ ↦ Pred o ℓ) (fun z _ hz ↦ by
      rw [predPot, ind_of hz]
      exact le_self_add)
  rwa [predPot_nil, mul_zero, add_zero] at h

/-- **T3's probability, squared form**: at most `(Q + 1)² / 2^193`. -/
theorem prEvent_game_pred_le_sq (o : ℕ) (guest : Semantics.Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred o z.2] ≤ (Q + 1) ^ 2 / 2 ^ 193 := by
  refine (prEvent_game_pred_le o guest fuel budget A Q hQ).trans ?_
  refine ENNReal.div_le_div_right ?_ _
  rw [sq]
  gcongr
  exact le_self_add

end Game

end
end LeanVM.E2E
