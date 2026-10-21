/-
  LeanVM.Guest.B1.Digest.StatementM

  `statement_digest` under a hash model: its relation under the model's semantics gives the
  answered hash of the statement's bytes, and `statementDigestWith` from its parts.
-/

module

public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.CommonM
public import LeanVM.Spec.NodeWith

/-!
# `statement_digest` over a hash model

`statement_digest` hashes 22 blocks from the IV (`Statement.lean`). Under a `HashModel` the
chain is `HashModel.chain_blocks`: the model answers the hash of the 22 blocks' bytes, which are
the statement's (`sd_bytes`, `stmtBytes`). So the function's relation under `M.sem` gives
`stmtDigestOfWith M.H seed sig da cells = some pi` (`statement_digest_model`), the statement's
digest given its signer-set and DA list digests; `statementDigestWith_of` assembles
`statementDigestWith M.H seed s = some pi` from the answered parts (pattern E). At the deployed
model the meaning is the deployed one (`meaning_statement_digestWith_deployed`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## The statement's bytes, for any hash -/

/-- The bytes `statementDigest` hashes, on its parts. -/
def stmtBytes (seed sig da : Digest) (defer : List E) : List UInt8 :=
  let cells := defer ++ if defer.length % 2 = 1 then [0] else []
  let bytes := digestBytes seed ++ digestBytes sig ++ digestBytes da ++ cells.flatMap eBytes
  bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0

/-- `stmtDigestOf` is BLAKE2s of `stmtBytes`. -/
theorem stmtDigestOf_eq_bytes (seed sig da : Digest) (defer : List E) :
    stmtDigestOf seed sig da defer = blake2sBytes (stmtBytes seed sig da defer) := rfl

/-- `stmtBytes` at the guest's cell count: 1392 bytes and 16 zero bytes. -/
theorem stmtBytes_eq (seed sig da : Digest) (cells : List E) (hlen : cells.length = 53) :
    stmtBytes seed sig da cells = (digestBytes seed ++ digestBytes sig ++
      digestBytes da ++ (cells ++ [0]).flatMap eBytes) ++ List.replicate 16 0 := by
  simp only [stmtBytes, hlen]
  simp only [↓reduceIte, List.length_append, length_digestBytes,
    length_flatMap_eBytes, hlen, List.length_cons, List.length_nil]

/-- **`statementDigest` on its parts, with the hash `H`** (`stmtDigestOf`). -/
def stmtDigestOfWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (seed sig da : Digest)
    (defer : List E) : m Digest :=
  H (stmtBytes seed sig da defer)

/-- `statementDigestWith` on its parts, the last hash `stmtDigestOfWith`. -/
theorem statementDigestWith_eq {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (seed : Digest)
    (s : NodeStatement) :
    statementDigestWith H seed s = (do
      let sd ← signersDigestWith H s.claims.xmss s.claims.sphincs
      let dd ← daListDigestWith H s.claims.da
      stmtDigestOfWith H seed sd dd s.defer.cells) := rfl

/-- **The statement's digest from its answered parts** (pattern E): the signer-set digest, the DA
list digest and `statement_digest`'s hash, each answered, answer `statementDigestWith`. -/
theorem statementDigestWith_of {H : List UInt8 → Option Digest} {seed sd dd pi : Digest}
    {s : NodeStatement} (hs : signersDigestWith H s.claims.xmss s.claims.sphincs = some sd)
    (hd : daListDigestWith H s.claims.da = some dd)
    (h : stmtDigestOfWith H seed sd dd s.defer.cells = some pi) :
    statementDigestWith H seed s = some pi := by
  rw [statementDigestWith_eq, hs]
  simp only [Option.bind_eq_bind, Option.bind_some, hd]
  exact h

/-! ## The meaning -/

/-- **`statement_digest` over a hash model**: the answered hash of the statement whose seed and
list digests are the argument cells (the signer-set digest read at `signers_hash`) and whose 53
deferred cells are read at `defer`. -/
def Meaning_statement_digestWith (M : HashModel) (rd : Reader) (args rets : List E) : Prop :=
  ∃ seed0 seed1 sigp da0 da1 dp d0 d1, args = [seed0, seed1, sigp, da0, da1, dp] ∧
    rets = [d0, d1] ∧ ∃ (seed sig da : Digest) (cells : List E), cells.length = deferStmtCells ∧
      (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
      LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
      CellsAt rd dp cells ∧
      ∃ pi, stmtDigestOfWith M.H seed sig da cells = some pi ∧ (d0, d1) = digestScalars pi

/-- At the deployed model the meaning is the deployed one. -/
theorem meaning_statement_digestWith_deployed (rd : Reader) (args rets : List E) :
    Meaning_statement_digestWith HashModel.deployed rd args rets ↔
      Meaning_statement_digest rd args rets := by
  simp only [Meaning_statement_digestWith, Meaning_statement_digest, stmtDigestOfWith,
    HashModel.deployed, Option.some.injEq, exists_eq_left', stmtDigestOf_eq_bytes]

/-- The facts of block `b` of `statement_digest`'s chain under `S` (`sdBlk_fwd`). -/
theorem sdBlkB_fwd {S : BlakeSem} {rd : Reader} {σ : Val} {b : ℕ}
    (h : ∀ a ∈ sdBlk b, a.HoldsB S rd σ) :
    σ (bv b 2) = word (64 * (b + 1)) (if b + 1 = 22 then 4294967295 else 0) 0 ∧
      S.check ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
        σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))] (σ (bv b 0)) (σ (bv b 1))
        (σ (bv (b + 1) 0)) (σ (bv (b + 1) 1)) (σ (bv b 2)) := by
  simpa only [sdBlk, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true] using h

/-- **`statement_digest` is sound under a hash model** (G:2664-2703): its relation under the
model's semantics gives the answered hash of the statement's bytes. -/
theorem statement_digest_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "statement_digest" args rets) :
    Meaning_statement_digestWith M rd args rets := by
  rw [relB_of_find find_statement_digest] at h
  simp only [Fn.SemB, sdBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.HoldsB, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, ⟨⟨⟨⟨⟨⟨h6, h7, h8, h9, h10, h11⟩, hpair⟩, hlast⟩, h740, h741, h742⟩, hblk⟩,
    h809, h810⟩, hr⟩ := h
  have hpair : ∀ p < 26, ∀ a ∈ sdPair p, a.Holds rd σ := fun p hp =>
    (forall_holdsB_noBlake (by simp [sdPair, atomNoBlake])).mp (hpair p hp)
  have hlast : ∀ a ∈ sdLast, a.Holds rd σ :=
    (forall_holdsB_noBlake (by simp [sdLast, atomNoBlake])).mp hlast
  obtain ⟨l714, e722, e731, e739⟩ := sdLast_fwd hlast
  -- the chain
  obtain ⟨pi, hpi, hst⟩ := HashModel.chain_blocks (M := M) (n := 21)
    (blocks := fun b => ![σ (.n (cellIdx (4 * b))), σ (.n (cellIdx (4 * b + 1))),
      σ (.n (cellIdx (4 * b + 2))), σ (.n (cellIdx (4 * b + 3)))])
    (md := fun b => σ (bv b 2)) (st := fun b => (σ (bv b 0), σ (bv b 1)))
    (by simp only [bv, Nat.reduceMul, Nat.reduceAdd]; rw [h741, h742, iv0_word, iv1_word]; rfl)
    (fun j hj => by
      rw [(sdBlkB_fwd (hblk j (by omega))).1, word_metadata]
      congr 1
      simp only [decide_eq_false_iff_not]
      omega)
    (by rw [(sdBlkB_fwd (hblk 21 (by omega))).1, word_metadata]; rfl)
    (fun j hj => (sdBlkB_fwd (hblk j (by omega))).2)
  have hcan : ∀ k < 88, IsCanonical128 (σ (.n (cellIdx k))) := by
    intro k hk
    have := (M.canonical (sdBlkB_fwd (hblk (k / 4) (by omega))).2).1 ⟨k % 4, by omega⟩
    have hk4 : k = 4 * (k / 4) + k % 4 := by omega
    rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h <;>
      simp only [h] at this <;> rw [hk4, h] <;> simpa using this
  have can : ∀ k < 6, IsCanonical128 (σ (.n (6 + k))) := fun k hk => by
    have := hcan k (by omega); rwa [cellIdx_hdr k hk] at this
  let seed := cellsDigest (σ (.n 6)) (σ (.n 7))
  let sig := cellsDigest (σ (.n 8)) (σ (.n 9))
  let da := cellsDigest (σ (.n 10)) (σ (.n 11))
  have dseed : digestScalars seed = (σ (.n 6), σ (.n 7)) :=
    digestScalars_cellsDigest (can 0 (by omega)) (can 1 (by omega))
  have dsig : digestScalars sig = (σ (.n 8), σ (.n 9)) :=
    digestScalars_cellsDigest (can 2 (by omega)) (can 3 (by omega))
  have dda : digestScalars da = (σ (.n 10), σ (.n 11)) :=
    digestScalars_cellsDigest (can 4 (by omega)) (can 5 (by omega))
  let cells : List E :=
    (List.range 53).map fun q => if q < 52 then σ (pv (q / 2) (q % 2)) else σ (.n 714)
  have hlen : cells.length = 53 := by simp [cells]
  have hD : ∀ q < 54, (cells ++ [0]).getD q 0 =
      if q < 52 then σ (pv (q / 2) (q % 2)) else if q = 52 then σ (.n 714) else 0 := by
    intro q hq
    rcases (show q < 53 ∨ q = 53 by omega) with h | h
    · rw [List.getD_eq_getElem _ _ (by simp [cells]; omega),
        List.getElem_append_left (by simp [cells]; omega)]
      simp only [cells, List.getElem_map, List.getElem_range]
      split_ifs <;> first | rfl | omega
    · subst h; simp [cells]
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 809), σ (.n 810),
    hp.symm, hr.symm, seed, sig, da, cells, hlen, ?_, ?_, ?_, ?_, ?_, pi, ?_, ?_⟩
  · rw [dseed, h6, h7]
  · rw [dsig]; exact h8
  · rw [dsig]; exact h9
  · rw [dda, h10, h11]
  · intro k hk
    have hk' : k < 53 := by simpa [cells] using hk
    simp only [cells, List.getElem_map, List.getElem_range]
    split_ifs with h
    · obtain ⟨q, r, hr2, rfl⟩ : ∃ q r, r < 2 ∧ k = 2 * q + r :=
        ⟨k / 2, k % 2, by omega, by omega⟩
      rw [show (2 * q + r) / 2 = q by omega, show (2 * q + r) % 2 = r by omega]
      obtain ⟨la, lb, -⟩ := sdPair_fwd (hpair q (by omega))
      interval_cases r
      · simpa using la
      · exact lb
    · rw [show k = 52 by omega]; exact l714
  · have hpq : ∀ p < 27, cellBytes (σ (.n (cellIdx (6 + 3 * p)))) ++
        cellBytes (σ (.n (cellIdx (6 + 3 * p + 1)))) ++
          cellBytes (σ (.n (cellIdx (6 + 3 * p + 2)))) =
        eBytes ((cells ++ [0]).getD (2 * p) 0) ++ eBytes ((cells ++ [0]).getD (2 * p + 1) 0) := by
      intro p hp27
      rw [hD (2 * p) (by omega), hD (2 * p + 1) (by omega)]
      rcases (show p < 26 ∨ p = 26 by omega) with hp26 | rfl
      · obtain ⟨-, -, e8, e17, e26⟩ := sdPair_fwd (hpair p hp26)
        rw [cellIdx_A p hp26, cellIdx_B p hp26, cellIdx_C p hp26, e8, e17, e26, pair_bytes,
          ite_pos' (by omega), ite_pos' (by omega), show 2 * p / 2 = p by omega,
          show 2 * p % 2 = 0 by omega, show (2 * p + 1) / 2 = p by omega,
          show (2 * p + 1) % 2 = 1 by omega]
      · rw [show cellIdx (6 + 3 * 26) = 722 from rfl, show cellIdx (6 + 3 * 26 + 1) = 731 from rfl,
          show cellIdx (6 + 3 * 26 + 2) = 739 from rfl, e722, e731, e739, pair_bytes]
        simp
    have hb := sd_bytes (fun k => σ (.n (cellIdx k))) seed sig da cells hlen
      (by show cellBytes (σ (.n 6)) ++ cellBytes (σ (.n 7)) = _; rw [digestBytes_eq, dseed])
      (by show cellBytes (σ (.n 8)) ++ cellBytes (σ (.n 9)) = _; rw [digestBytes_eq, dsig])
      (by show cellBytes (σ (.n 10)) ++ cellBytes (σ (.n 11)) = _; rw [digestBytes_eq, dda])
      hpq (by show σ (.n 740) = 0; rw [h740, word_zero])
    rw [stmtDigestOfWith, stmtBytes_eq seed sig da cells hlen, ← hb]
    exact hpi
  · simp only [bv, Nat.reduceMul, Nat.reduceAdd] at hst
    rw [h809, h810]
    exact hst

end
end LeanVM.Guest.B1.Digest
