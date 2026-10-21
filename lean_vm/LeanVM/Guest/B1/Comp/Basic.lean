/-
  LeanVM.Guest.B1.Comp.Basic

  The guest's completeness over a completeness model: its answers as a hash model, the rows of an
  answered string's chain, and the answered runs taken apart step by step.
-/

module

public import LeanVM.Guest.B1.Basic
public import LeanVM.E2E.Complete.Model

/-!
# Completeness over a completeness model: the foundation

A `CompModel` (`E2E/Complete/Model.lean`) gives the rows of every answered string's standard
chain (`step`, `final`). The guest's B1 lemmas over a model are the backward halves of the deployed
iffs: "if the model answers the strings this function hashes, its relation holds under the model's
semantics at the honest values". This module gives what every such lemma uses.

* `CompModel.hm`: the model's answers as a `HashModel` (with the semantics checking nothing, so its
  laws hold vacuously): the W2 meanings over a hash model (`RunsToM`, `obsCvM`, `…With M`) read only
  `M.H`, so at `CM.hm` they state what the model must answer. At `CompModel.deployed` they are the
  deployed meanings (`runsToM_hm_deployed`, `obsCvM_hm_deployed`, …).
* The rows of a chain: `CompModel.check_one` (one block from the IV, every Fiat-Shamir step and
  Merkle node), `check_empty`, and `chain_checks` (`chain_bytes`'s dual): the blocks of an answered
  string from the IV, through the cells `chainSt` after each whole block (`st`), to the answer.
* Answered runs, taken apart: `RunsToM.read_inv`, `sample_inv`, `ret_inv`, `readN_inv`,
  `sampleN_inv`: a run every hash of which the model answers is answered step by step.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.E2E.Complete

@[expose] public section

/-! ## The answers as a hash model -/

/-- The semantics checking nothing. -/
def blakeNone : BlakeSem := ⟨fun _ _ _ _ _ _ ↦ False, fun _ _ _ _ _ _ ↦ instDecidableFalse⟩

/-- **A completeness model's answers, as a hash model**: `H` the model's, a semantics checking
nothing (so the laws hold vacuously). The W2 meanings read only `H`. -/
def _root_.LeanVM.E2E.Complete.CompModel.hm (CM : CompModel) : HashModel where
  sem := blakeNone
  canonical h := h.elim
  H := CM.H
  Prefix bs st := bs = [] ∧ st = ivCells
  prefix_nil := ⟨rfl, rfl⟩
  prefix_step _ h := h.elim
  final _ _ _ _ h := h.elim

theorem _root_.LeanVM.E2E.Complete.CompModel.hm_H (CM : CompModel) : CM.hm.H = CM.H := rfl

/-- At the deployed model, `RunsToM` over the answers is `RunsTo`. -/
theorem runsToM_hm_deployed {α : Type} {p : Prog α} {cv : Digest} {xs : List E} {a : α}
    {cv' : Digest} : RunsToM CompModel.deployed.hm p cv xs a cv' ↔ RunsTo p cv xs a cv' :=
  runsToM_deployed

theorem obsCvM_hm_deployed (cv : Digest) (x : E) :
    obsCvM CompModel.deployed.hm cv x = some (obsCv cv x) := rfl

theorem sqCvM_hm_deployed (cv : Digest) : sqCvM CompModel.deployed.hm cv = some (sqCv cv) := rfl

theorem obsAllM_hm_deployed (cv : Digest) (xs : List E) :
    obsAllM CompModel.deployed.hm cv xs = some (obsAll cv xs) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons x xs ih =>
    simp only [obsAllM, obsCvM_hm_deployed, Option.bind_some, ih]
    rfl

theorem sqAllM_hm_deployed : ∀ (n : ℕ) (cv : Digest),
    sqAllM CompModel.deployed.hm n cv = some (sqAll n cv)
  | 0, _ => rfl
  | n + 1, cv => by
    simp only [sqAllM, sqCvM_hm_deployed, Option.bind_some, sqAllM_hm_deployed n, Option.map_some]
    rfl

end
end LeanVM.Guest.B1

namespace LeanVM.E2E.Complete.CompModel

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.E2E.Complete

@[expose] public section

/-! ## The rows of a chain -/

/-- **One block from the IV** (every Fiat-Shamir step, every Merkle node): an answered 64-byte
string's block checks from the IV to the answer, at counter 64 with the flag. -/
theorem check_one (CM : CompModel) {m : Fin 4 → E} {d : Digest}
    (hm : ∀ j, IsCanonical128 (m j)) (hd : CM.H (blockBytes m) = some d) :
    CM.sem.check m ivCells.1 ivCells.2 (digestScalars d).1 (digestScalars d).2
      (metadataCell 64 true) := by
  have hn : nBlocks (blockBytes m) = 0 := by simp [nBlocks, length_blockBytes]
  have h := CM.final hd hm (by
    rw [tailOf, hn, Nat.mul_zero, List.drop_zero, length_blockBytes, Nat.sub_self,
      List.replicate_zero, List.append_nil])
  rw [hn, prefixAt_zero, CM.st_nil, length_blockBytes] at h
  exact h

/-- **The empty string**: one zero block from the IV, at counter 0 with the flag. -/
theorem check_empty (CM : CompModel) {d : Digest} (hd : CM.H [] = some d) :
    CM.sem.check ![0, 0, 0, 0] ivCells.1 ivCells.2 (digestScalars d).1 (digestScalars d).2
      (metadataCell 0 true) := by
  have hz : IsCanonical128 (0 : E) := by rw [zero_eq_ofLimbs]; rfl
  have hz' : ∀ i, (![0, 0, 0, 0] : Fin 4 → E) i = 0 := by
    intro i
    fin_cases i <;> rfl
  have hb : blockBytes ![0, 0, 0, 0] = tailOf [] ++ List.replicate (64 - (tailOf []).length) 0 := by
    simp only [blockBytes, hz', cellBytes_zero, tailOf, nBlocks, List.drop_nil, List.length_nil,
      Nat.sub_zero, List.nil_append, ← List.replicate_add]
  have h := CM.final hd (fun j ↦ by rw [hz']; exact hz) hb
  rw [show nBlocks [] = 0 from rfl, prefixAt_zero, CM.st_nil] at h
  exact h

/-- The cells of the chain of `x` after `j` blocks: the cells after its first `j` whole blocks,
and the answer `d` past them. -/
def chainSt (CM : CompModel) (x : Bytes) (d : Digest) (j : ℕ) : E × E :=
  if j ≤ nBlocks x then CM.st (prefixAt x j) else digestScalars d

theorem chainSt_zero (CM : CompModel) (x : Bytes) (d : Digest) :
    CM.chainSt x d 0 = ivCells := by
  simp [chainSt, CM.st_nil]

theorem chainSt_of_le (CM : CompModel) {x : Bytes} (d : Digest) {j : ℕ}
    (hj : j ≤ nBlocks x) : CM.chainSt x d j = CM.st (prefixAt x j) := by
  simp [chainSt, hj]

theorem chainSt_last (CM : CompModel) (x : Bytes) (d : Digest) :
    CM.chainSt x d (nBlocks x + 1) = digestScalars d := by
  simp [chainSt]

theorem chainSt_canonical (CM : CompModel) (x : Bytes) (d : Digest) (j : ℕ) :
    IsCanonical128 (CM.chainSt x d j).1 ∧ IsCanonical128 (CM.chainSt x d j).2 := by
  unfold chainSt
  split
  · exact CM.st_canonical _
  · exact isCanonical128_digestScalars d

/-- Chunk `j` of 64-byte chunks. -/
theorem take_drop_flatMap_range {f : ℕ → List UInt8} (hf : ∀ j, (f j).length = 64) :
    ∀ (N j : ℕ), j < N → (((List.range N).flatMap f).drop (64 * j)).take 64 = f j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, j, h => by
    have hlen : ((List.range N).flatMap f).length = 64 * N := by
      rw [List.length_flatMap]
      simp only [hf, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
      ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge j N with hj | hj
    · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by
        rw [List.length_drop]; omega)]
      exact take_drop_flatMap_range hf N j hj
    · obtain rfl : j = N := by omega
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append, List.take_of_length_le (by rw [hf])]

/-- **The rows of an answered string's chain from the IV** (the dual of `HashModel.chain_bytes`):
the `n + 1` blocks of `x` zero-filled to whole blocks, the non-final ones at the cumulative
counters, the last at `x.length` with the flag, each check from the cells after the blocks before
it (`chainSt`) to the cells after it, the last to the answer. -/
theorem chain_checks (CM : CompModel) {n : ℕ} {blocks : ℕ → Fin 4 → E} {md : ℕ → E}
    {x : Bytes} {d : Digest} (hd : CM.H x = some d) (hn : (x.length - 1) / 64 = n)
    (hbytes : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      x ++ List.replicate (64 * (n + 1) - x.length) 0)
    (hcan : ∀ j ≤ n, ∀ r, IsCanonical128 (blocks j r))
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell x.length true) :
    ∀ j ≤ n, CM.sem.check (blocks j) (CM.chainSt x d j).1 (CM.chainSt x d j).2
      (CM.chainSt x d (j + 1)).1 (CM.chainSt x d (j + 1)).2 (md j) := by
  have hN : nBlocks x = n := hn
  have hlo : 64 * n ≤ x.length := by
    rcases Nat.eq_zero_or_pos x.length with h | h
    · rw [h] at hn ⊢; simp at hn; omega
    · omega
  have hhi : x.length ≤ 64 * (n + 1) := by omega
  have hchunk : ∀ j ≤ n, blockBytes (blocks j) =
      ((x ++ List.replicate (64 * (n + 1) - x.length) 0).drop (64 * j)).take 64 := by
    intro j hj
    rw [← hbytes]
    exact (take_drop_flatMap_range (fun j ↦ length_blockBytes (blocks j)) (n + 1) j
      (by omega)).symm
  intro j hj
  rcases Nat.lt_or_ge j n with hjn | hjn
  · have hb : blockBytes (blocks j) = blockAt x j := by
      rw [hchunk j hj, blockAt, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    have h := CM.step hd (i := j) (by omega) (hcan j hj) hb
    rw [CM.chainSt_of_le d (by omega), CM.chainSt_of_le d (by omega), hmd j hjn]
    exact h
  · obtain rfl : j = n := by omega
    have hb : blockBytes (blocks j) = tailOf x ++ List.replicate (64 - (tailOf x).length) 0 := by
      have hl : ((x.drop (64 * j)) ++ List.replicate (64 * (j + 1) - x.length) 0).length ≤ 64 := by
        simp only [List.length_append, List.length_drop, List.length_replicate]
        omega
      rw [hchunk j hj, tailOf, hN, List.drop_append_of_le_length hlo, List.take_of_length_le hl,
        List.length_drop]
      congr 2
      omega
    have h := CM.final hd (hcan j hj) hb
    rw [hN] at h
    rw [CM.chainSt_of_le d (by omega), hN.symm, CM.chainSt_last, hN, hfin]
    exact h

/-- **Whole blocks from the IV** (the dual of `HashModel.chain_blocks`; `statement_digest`,
`da_hash_roots`, `da_verify_cell`): the `n + 1` blocks of an answered string of their bytes, the
last at counter `64·(n + 1)` with the flag. -/
theorem chain_checks_blocks (CM : CompModel) {n : ℕ} {blocks : ℕ → Fin 4 → E}
    {md : ℕ → E} {d : Digest}
    (hd : CM.H ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = some d)
    (hcan : ∀ j ≤ n, ∀ r, IsCanonical128 (blocks j r))
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell (64 * (n + 1)) true) :
    let x := (List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)
    ∀ j ≤ n, CM.sem.check (blocks j) (CM.chainSt x d j).1 (CM.chainSt x d j).2
      (CM.chainSt x d (j + 1)).1 (CM.chainSt x d (j + 1)).2 (md j) := by
  intro x
  have hlen : x.length = 64 * (n + 1) := by
    simp only [x, List.length_flatMap, length_blockBytes, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]
    ring
  exact CM.chain_checks hd (by rw [hlen]; omega)
    (by rw [hlen, Nat.sub_self, List.replicate_zero, List.append_nil]) hcan hmd (by rw [hfin, hlen])

/-- The length of a string of `n` whole blocks. -/
theorem length_flatMap_blocks (blocks : ℕ → Fin 4 → E) (n : ℕ) :
    ((List.range n).flatMap fun j ↦ blockBytes (blocks j)).length = 64 * n := by
  simp only [List.length_flatMap, length_blockBytes, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

/-- Block `j` of a string of whole blocks. -/
theorem blockAt_blocks (blocks : ℕ → Fin 4 → E) {n j : ℕ} (hj : j < n) :
    blockAt ((List.range n).flatMap fun j ↦ blockBytes (blocks j)) j = blockBytes (blocks j) :=
  take_drop_flatMap_range (fun j ↦ length_blockBytes (blocks j)) n j hj

/-- A string of `n + 1` whole blocks has `n` blocks before its last. -/
theorem nBlocks_blocks (blocks : ℕ → Fin 4 → E) (n : ℕ) :
    nBlocks ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = n := by
  unfold nBlocks
  rw [length_flatMap_blocks]
  omega

/-- The last block of a string of `n + 1` whole blocks. -/
theorem tailOf_blocks (blocks : ℕ → Fin 4 → E) (n : ℕ) :
    tailOf ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = blockBytes (blocks n) := by
  rw [tailOf, nBlocks_blocks, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.drop_append_of_le_length (by rw [length_flatMap_blocks]),
    List.drop_of_length_le (by rw [length_flatMap_blocks]), List.nil_append]

/-- **A whole non-final block of an answered string of whole blocks** (`step`): block `j < n`
checks from the cells after the first `j` blocks to the cells after `j + 1`. -/
theorem step_blocks (CM : CompModel) {blocks : ℕ → Fin 4 → E} {n : ℕ} {d : Digest}
    (hd : CM.H ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = some d) {j : ℕ}
    (hj : j < n) (hm : ∀ r, IsCanonical128 (blocks j r)) :
    let x := (List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)
    CM.sem.check (blocks j) (CM.st (prefixAt x j)).1 (CM.st (prefixAt x j)).2
      (CM.st (prefixAt x (j + 1))).1 (CM.st (prefixAt x (j + 1))).2
      (metadataCell (64 * (j + 1)) false) :=
  CM.step hd (by rw [nBlocks_blocks]; exact hj) hm (blockAt_blocks blocks (by omega)).symm

/-- **The last block of an answered string of whole blocks** (`final`): block `n` checks from the
cells after the first `n` blocks to the answer, at counter `64·(n + 1)` with the flag. -/
theorem final_blocks (CM : CompModel) {blocks : ℕ → Fin 4 → E} {n : ℕ} {d : Digest}
    (hd : CM.H ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)) = some d)
    (hm : ∀ r, IsCanonical128 (blocks n r)) :
    let x := (List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)
    CM.sem.check (blocks n) (CM.st (prefixAt x n)).1 (CM.st (prefixAt x n)).2
      (digestScalars d).1 (digestScalars d).2 (metadataCell (64 * (n + 1)) true) := by
  intro x
  have h := CM.final hd hm (by
    rw [tailOf_blocks, length_blockBytes, Nat.sub_self, List.replicate_zero, List.append_nil])
  rw [nBlocks_blocks, length_flatMap_blocks] at h
  exact h

/-- The last cells of a chain over `n + 1` blocks of `x` are the answer. -/
theorem chainSt_succ_of (CM : CompModel) {x : Bytes} (d : Digest) {n : ℕ}
    (hn : (x.length - 1) / 64 = n) : CM.chainSt x d (n + 1) = digestScalars d := by
  have : nBlocks x = n := hn
  rw [← this, CM.chainSt_last]

end
end LeanVM.E2E.Complete.CompModel

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.E2E.Complete

@[expose] public section

/-! ## Answered runs, taken apart -/

section Inv

variable {M : HashModel}

/-- A read of an answered run: the model answers the absorb of the word read. -/
theorem RunsToM.read_inv {α : Type} {k : E → Prog α} {cv cv' : Digest} {x : E} {xs : List E}
    {a : α} (h : RunsToM M (Prog.read k) cv (x :: xs) a cv') :
    ∃ c, obsCvM M cv x = some c ∧ RunsToM M (k x) c xs a cv' := by
  have h0 := h [] [] []
  simp only [runM, Compile.run, absorbBlock, List.cons_append, Option.bind_eq_bind] at h0
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h0
  refine ⟨c, hc, fun rest os roots ↦ ?_⟩
  have h1 := h rest os roots
  simp only [runM, Compile.run, absorbBlock, List.cons_append, Option.bind_eq_bind] at h1
  rw [show M.H (digestBytes cv ++ blockOf x 1) = some c from hc, Option.bind_some] at h1
  exact h1

/-- A read of an answered run needs a word. -/
theorem RunsToM.read_nil {α : Type} {k : E → Prog α} {cv cv' : Digest} {a : α}
    (h : RunsToM M (Prog.read k) cv [] a cv') : False := by
  have h0 := h [] [] []
  simp [runM, Compile.run] at h0

/-- A sample of an answered run: the model answers the squeeze. -/
theorem RunsToM.sample_inv {α : Type} {k : E → Prog α} {cv cv' : Digest} {xs : List E} {a : α}
    (h : RunsToM M (Prog.sample k) cv xs a cv') :
    ∃ c, sqCvM M cv = some c ∧ RunsToM M (k (challengeOf c)) c xs a cv' := by
  have h0 := h [] [] []
  simp only [runM, Compile.run, absorbBlock, Option.bind_eq_bind] at h0
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h0
  refine ⟨c, hc, fun rest os roots ↦ ?_⟩
  have h1 := h rest os roots
  simp only [runM, Compile.run, absorbBlock, Option.bind_eq_bind] at h1
  rw [show M.H (digestBytes cv ++ blockOf 0 2) = some c from hc, Option.bind_some] at h1
  exact h1

/-- The end of an answered run: no word read, the value and the state. -/
theorem RunsToM.ret_inv {α : Type} {a b : α} {cv cv' : Digest} {xs : List E}
    (h : RunsToM M (Prog.ret a) cv xs b cv') : xs = [] ∧ b = a ∧ cv' = cv := by
  have h0 := h [] [] []
  simp only [runM, Compile.run, List.append_nil, pure, Option.some.injEq, Prod.mk.injEq,
    St.mk.injEq, and_true] at h0
  obtain ⟨rfl, rfl, rfl⟩ := h0
  exact ⟨rfl, rfl, rfl⟩

/-- `readN` in an answered run: the words it reads, absorbed one by one, every absorb answered. -/
theorem RunsToM.readN_inv {β : Type} : ∀ {n : ℕ} {f : List E → Prog β} {cv cv' : Digest}
    {xs : List E} {b : β}, RunsToM M ((Prog.readN n).bind f) cv xs b cv' →
    ∃ ys zs c, xs = ys ++ zs ∧ ys.length = n ∧ obsAllM M cv ys = some c ∧
      RunsToM M (f ys) c zs b cv'
  | 0, f, cv, cv', xs, b, h => ⟨[], xs, cv, rfl, rfl, rfl, h⟩
  | n + 1, f, cv, cv', xs, b, h => by
    have e : (Prog.readN (n + 1)).bind f =
        Prog.read fun x ↦ (Prog.readN n).bind fun ys ↦ f (x :: ys) := by
      simp only [Prog.readN, Prog.readE, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
        Prog.bind]
    rw [e] at h
    match xs, h with
    | [], h => exact h.read_nil.elim
    | x :: xs, h =>
      obtain ⟨c1, hc1, h⟩ := h.read_inv
      obtain ⟨ys, zs, c, rfl, hl, hc, h⟩ := RunsToM.readN_inv h
      refine ⟨x :: ys, zs, c, rfl, by simp [hl], ?_, h⟩
      simp only [obsAllM, hc1, Option.bind_some, hc]

/-- `sampleN` in an answered run: the challenges and the state, every squeeze answered. -/
theorem RunsToM.sampleN_inv {β : Type} : ∀ {n : ℕ} {f : List E → Prog β} {cv cv' : Digest}
    {xs : List E} {b : β}, RunsToM M ((Prog.sampleN n).bind f) cv xs b cv' →
    ∃ cs c, sqAllM M n cv = some (cs, c) ∧ RunsToM M (f cs) c xs b cv'
  | 0, f, cv, cv', xs, b, h => ⟨[], cv, rfl, h⟩
  | n + 1, f, cv, cv', xs, b, h => by
    have e : (Prog.sampleN (n + 1)).bind f =
        Prog.sample fun x ↦ (Prog.sampleN n).bind fun ys ↦ f (x :: ys) := by
      simp only [Prog.sampleN, Prog.sampleE, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
        Prog.bind]
    rw [e] at h
    obtain ⟨c1, hc1, h⟩ := h.sample_inv
    obtain ⟨cs, c, hc, h⟩ := RunsToM.sampleN_inv h
    refine ⟨challengeOf c1 :: cs, c, ?_, h⟩
    simp only [sqAllM, hc1, Option.bind_some, hc, Option.map_some]

/-- `readE` then `f` in an answered run. -/
theorem RunsToM.readE_inv {β : Type} {f : E → Prog β} {cv cv' : Digest} {xs : List E} {b : β}
    (h : RunsToM M (Prog.readE.bind f) cv xs b cv') :
    ∃ x zs c, xs = x :: zs ∧ obsCvM M cv x = some c ∧ RunsToM M (f x) c zs b cv' := by
  match xs, h with
  | [], h => exact (RunsToM.read_nil (k := fun x ↦ (Prog.ret x).bind f) h).elim
  | x :: xs, h =>
    obtain ⟨c, hc, h⟩ := RunsToM.read_inv (k := fun x ↦ (Prog.ret x).bind f) h
    exact ⟨x, xs, c, rfl, hc, h⟩

/-- `sampleE` then `f` in an answered run. -/
theorem RunsToM.sampleE_inv {β : Type} {f : E → Prog β} {cv cv' : Digest} {xs : List E} {b : β}
    (h : RunsToM M (Prog.sampleE.bind f) cv xs b cv') :
    ∃ c, sqCvM M cv = some c ∧ RunsToM M (f (challengeOf c)) c xs b cv' :=
  RunsToM.sample_inv (k := fun x ↦ (Prog.ret x).bind f) h

/-- `readN` over known words in an answered run. -/
theorem RunsToM.readN_inv' {β : Type} {n : ℕ} {f : List E → Prog β} {cv cv' : Digest}
    {xs zs : List E} {b : β} (hn : xs.length = n)
    (h : RunsToM M ((Prog.readN n).bind f) cv (xs ++ zs) b cv') :
    ∃ c, obsAllM M cv xs = some c ∧ RunsToM M (f xs) c zs b cv' := by
  obtain ⟨ys, zs', c, he, hl, hc, h'⟩ := h.readN_inv
  obtain ⟨rfl, rfl⟩ := List.append_inj he.symm (by rw [hl, hn])
  exact ⟨c, hc, h'⟩

/-- An answered absorb of words, one at a time. -/
theorem obsAllM_cons_some {cv c : Digest} {x : E} {xs : List E}
    (h : obsAllM M cv (x :: xs) = some c) :
    ∃ c1, obsCvM M cv x = some c1 ∧ obsAllM M c1 xs = some c :=
  Option.bind_eq_some_iff.mp h

theorem obsAllM_nil_some {cv c : Digest} (h : obsAllM M cv [] = some c) : c = cv :=
  (Option.some.inj h).symm

/-! ## The states of an answered absorb -/

/-- The chain after each prefix of the words `xs`, every absorb read off the model (`default`
where it does not answer). -/
def obsAt (M : HashModel) (cv : Digest) (xs : List E) : ℕ → Digest
  | 0 => cv
  | i + 1 => (obsCvM M (obsAt M cv xs i) (xs.getD i 0)).getD default

theorem obsAt_cons (M : HashModel) (cv : Digest) (x : E) (xs : List E) :
    ∀ i, obsAt M cv (x :: xs) (i + 1) = obsAt M ((obsCvM M cv x).getD default) xs i
  | 0 => rfl
  | i + 1 => by
    rw [obsAt, obsAt_cons M cv x xs i, obsAt]
    rfl

/-- **An answered absorb of words, step by step**: every absorb answered, from the state after
the words before it to the state after it, the last state the answer. -/
theorem obsAllM_obsAt {M : HashModel} : ∀ {cv c : Digest} {xs : List E},
    obsAllM M cv xs = some c →
      (∀ i < xs.length, obsCvM M (obsAt M cv xs i) (xs.getD i 0) = some (obsAt M cv xs (i + 1))) ∧
        c = obsAt M cv xs xs.length
  | cv, c, [], h => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), (Option.some.inj h).symm⟩
  | cv, c, x :: xs, h => by
    obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs, hc⟩ := obsAllM_obsAt h
    have e1 : (obsCvM M cv x).getD default = c1 := by rw [hc1]; rfl
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · show obsCvM M cv x = some ((obsCvM M cv x).getD default)
        rw [hc1]; rfl
      · rw [obsAt_cons, obsAt_cons, e1, List.getD_cons_succ]
        exact hs i (by simp at hi; omega)
    · rw [List.length_cons, obsAt_cons, e1]
      exact hc

theorem obsAt_hm_deployed (cv : Digest) (xs : List E) :
    ∀ i, obsAt CompModel.deployed.hm cv xs i = (List.range i).foldl (fun c j ↦ obsCv c (xs.getD j 0)) cv
  | 0 => rfl
  | i + 1 => by
    rw [obsAt, obsAt_hm_deployed cv xs i, List.range_succ, List.foldl_append]
    rfl

/-- The chain after `j` squeezes, every squeeze read off the model (`default` where it does not
answer). -/
def sqAt (M : HashModel) (cv : Digest) : ℕ → Digest
  | 0 => cv
  | j + 1 => (sqCvM M (sqAt M cv j)).getD default

theorem sqAt_succ' (M : HashModel) (cv : Digest) :
    ∀ j, sqAt M cv (j + 1) = sqAt M ((sqCvM M cv).getD default) j
  | 0 => rfl
  | j + 1 => by
    rw [sqAt, sqAt_succ' M cv j, sqAt]

/-- **Answered squeezes, step by step**: every squeeze answered, from the state after the
squeezes before it, the challenges those of the states, the last state the answer. -/
theorem sqAllM_sqAt {M : HashModel} : ∀ {m : ℕ} {cv c : Digest} {cs : List E},
    sqAllM M m cv = some (cs, c) →
      (∀ j < m, sqCvM M (sqAt M cv j) = some (sqAt M cv (j + 1))) ∧
        cs = (List.range m).map (fun j ↦ challengeOf (sqAt M cv (j + 1))) ∧ c = sqAt M cv m
  | 0, cv, c, cs, h => by
    simp only [sqAllM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), rfl, rfl⟩
  | m + 1, cv, c, cs, h => by
    obtain ⟨c1, hc1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hrr⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨rfl, rfl⟩ := hrr
    obtain ⟨hs, hcs, hc⟩ := sqAllM_sqAt (m := m) (cv := c1) (c := r.2) (cs := r.1) hr
    have e1 : (sqCvM M cv).getD default = c1 := by rw [hc1]; rfl
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · rcases j with _ | j
      · show sqCvM M cv = some ((sqCvM M cv).getD default)
        rw [hc1]; rfl
      · rw [sqAt_succ', sqAt_succ', e1]
        exact hs j (by omega)
    · rw [hcs, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq]
      refine ⟨?_, List.map_congr_left fun j _ => ?_⟩
      · show challengeOf c1 = challengeOf ((sqCvM M cv).getD default)
        rw [e1]
      · show challengeOf (sqAt M c1 (j + 1)) = challengeOf (sqAt M cv (j + 1 + 1))
        rw [sqAt_succ' M cv (j + 1), e1]
    · rw [sqAt_succ', e1, hc]

theorem sqAt_hm_deployed : ∀ (j : ℕ) (cv : Digest), sqAt CompModel.deployed.hm cv j = (sqAll j cv).2
  | 0, _ => rfl
  | j + 1, cv => by
    rw [sqAt_succ', show (sqCvM CompModel.deployed.hm cv).getD default = sqCv cv from rfl,
      sqAt_hm_deployed j (sqCv cv)]
    rfl

end Inv

end
end LeanVM.Guest.B1
