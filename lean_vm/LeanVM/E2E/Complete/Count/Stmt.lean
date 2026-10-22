/-
  LeanVM.E2E.Complete.Count.Stmt

  The block prefixes a statement's digest logs, bounded by its lists and cells, and the
  batching's, none: it hashes single blocks.
-/

module

public import LeanVM.E2E.Complete.Count.Prog

/-!
# Statements and the batching

* `prefixCount_statementDigestWith_le`: a statement's digest hashes its two signature lists
  (`64` bytes a claim), the signer set (`64` bytes), the DA list (`64` bytes a claim) and the
  final string (`96` bytes and `24` a cell, zero-filled to whole blocks): at most
  `stmtBlocks s` block prefixes;
* `prefixCount_childClaimsM_le`: the children's claims, their statements' digests;
* `prefixCount_batchWith`: the batching only observes and squeezes, one block each, so its log
  has no block prefix whatever the hints (`LogShortS` through `batchWith.go`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node

@[expose] public section

variable (H : Bytes → Digest)

/-! ## A statement's digest -/

/-- The block prefixes a statement's digest logs, at most. -/
def stmtBlocks (s : NodeStatement) : ℕ :=
  s.claims.xmss.length + s.claims.sphincs.length + s.claims.da.length + s.defer.cells.length + 3

theorem length_claimBytes_count (r p : BitVec 128) (m : BitVec 256) :
    (claimBytes r p m).length = 64 := by
  simp [claimBytes, bytes16, LeanXmss.bytesLE]

theorem length_claimList {γ : Type} (f : γ → List UInt8) (hf : ∀ c, (f c).length = 64) :
    ∀ l : List γ, (l.flatMap f).length = 64 * l.length
  | [] => rfl
  | c :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_claimList f hf l, List.length_cons]
    ring

/-- A list of `64`-byte entries has at most one block prefix per entry. -/
theorem nBlocks_claimList_le {γ : Type} (f : γ → List UInt8) (hf : ∀ c, (f c).length = 64)
    (l : List γ) : nBlocks (l.flatMap f) ≤ l.length :=
  nBlocks_le_of_length_le (by rw [length_claimList f hf l]; omega)

theorem length_flatMap_eBytes_count (cells : List E) : (cells.flatMap Node.eBytes).length = 24 * cells.length := by
  induction cells with
  | nil => rfl
  | cons x cells ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    show 24 + 24 * cells.length = _
    ring

/-- The final string of a statement's digest, zero-filled. -/
theorem nBlocks_stmtFinal_le (seed sd dd : Digest) (cells : List E) :
    nBlocks (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
        (cells ++ if cells.length % 2 = 1 then [0] else []).flatMap Node.eBytes ++
      List.replicate ((64 - (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
        (cells ++ if cells.length % 2 = 1 then [0] else []).flatMap Node.eBytes).length % 64) % 64) 0) ≤
      cells.length + 3 := by
  refine nBlocks_le_of_length_le ?_
  have hp : (if cells.length % 2 = 1 then [(0 : E)] else []).length ≤ 1 := by
    split <;> simp
  simp only [List.length_append, List.length_replicate, length_digestBytes_count,
    length_flatMap_eBytes_count]
  generalize (if cells.length % 2 = 1 then [(0 : E)] else []).length = t at hp ⊢
  omega

/-- **The count of a statement's digest.** -/
theorem prefixCount_statementDigestWith_le (seed : Digest) (s : NodeStatement) :
    prefixCount (statementDigestWith (LogM.hash H) seed s).log ≤ stmtBlocks s := by
  have hsig : prefixCount (signersDigestWith (LogM.hash H) s.claims.xmss s.claims.sphincs).log ≤
      s.claims.xmss.length + s.claims.sphincs.length := by
    simp only [signersDigestWith, xmssListDigestWith, sphincsListDigestWith, prefixCount_bind,
      prefixCount_hash]
    have hx : nBlocks (s.claims.xmss.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2) ≤
        s.claims.xmss.length :=
      nBlocks_claimList_le _ (fun c ↦ length_claimBytes_count _ _ _) _
    have hs : nBlocks (s.claims.sphincs.flatMap fun c ↦ claimBytes c.1.root c.1.parameter c.2) ≤
        s.claims.sphincs.length :=
      nBlocks_claimList_le _ (fun c ↦ length_claimBytes_count _ _ _) _
    have h2 : ∀ a b : Digest, nBlocks (digestBytes a ++ digestBytes b) = 0 := fun a b ↦
      nBlocks_eq_zero_of_length_le (by
        rw [List.length_append, length_digestBytes_count, length_digestBytes_count])
    rw [h2]
    omega
  have hda : prefixCount (daListDigestWith (LogM.hash H) s.claims.da).log ≤ s.claims.da.length := by
    simp only [daListDigestWith, prefixCount_hash]
    exact nBlocks_claimList_le _ (fun c ↦ by
      rw [List.length_append, length_digestBytes_count, length_digestBytes_count]) _
  unfold statementDigestWith
  rw [prefixCount_bind, prefixCount_bind, prefixCount_hash]
  refine (Nat.add_le_add hsig (Nat.add_le_add hda (nBlocks_stmtFinal_le _ _ _ _))).trans ?_
  unfold stmtBlocks
  omega

/-- **The count of the children's claims**: their statements' digests. -/
theorem prefixCount_childClaimsM_le (seed : Digest) (cs : List Child) :
    prefixCount (childClaimsM (LogM.hash H) seed cs).log ≤ (cs.map (stmtBlocks ·.statement)).sum :=
  prefixCount_mapM_le _ _ cs fun c _ ↦ by
    rw [LogM.map_log]
    exact prefixCount_statementDigestWith_le H seed c.statement

/-! ## The batching -/

section Batch

attribute [local irreducible] LogM.instMonad

/-- An observation hashes one block. -/
theorem logShortS_observeWith (x : E) : LogShortS (observeWith (m := LogM) (LogM.hash H) x) :=
  fun s ↦ by
    simp only [observeWith, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_monadLift, monadLift_self, StateT.run_set, Functor.map_map]
    exact LogShort.map _ (LogShort.hash H (by
      rw [List.length_append, length_digestBytes_count, length_blockOf_count]))

/-- A squeeze hashes one block. -/
theorem logShortS_squeezeWith : LogShortS (squeezeWith (m := LogM) (LogM.hash H)) := fun s ↦ by
  simp only [squeezeWith, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_map, map_pure,
    Functor.map_map]
  exact LogShort.map _ (LogShort.hash H (by
    rw [List.length_append, length_digestBytes_count, length_blockOf_count]))

/-- A batching sumcheck hashes single blocks. -/
theorem logShortS_batchRoundsWith : ∀ (claim : E) (rounds : List (E × E)),
    LogShortS (batchRoundsWith (m := LogM) (LogM.hash H) claim rounds)
  | _, [] => LogShortS.pure _
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith]
    exact LogShortS.bind (logShortS_observeWith H _) fun _ ↦
      LogShortS.bind (logShortS_observeWith H _) fun _ ↦
        LogShortS.bind (logShortS_squeezeWith H) fun _ ↦
          LogShortS.bind (logShortS_batchRoundsWith _ _) fun _ ↦ LogShortS.pure _

/-- **The batching logs no block prefix**, whatever the children and the hints. -/
theorem prefixCount_batchWith (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    prefixCount (batchWith (LogM.hash H) s0 cs h).log = 0 := by
  refine LogShort.prefixCount_eq ?_
  unfold batchWith
  show LogShort ((·.1) <$> (batchWith.go (LogM.hash H) cs h).run s0)
  refine LogShort.map _ ?_
  revert s0
  show LogShortS _
  unfold batchWith.go
  refine LogShortS.bind (logShortS_observeWith H _) fun _ ↦ ?_
  refine LogShortS.bind (LogShortS.forIn _ (fun c _ ↦ ?_) _ _) fun _ ↦ ?_
  · exact LogShortS.bind (logShortS_observeWith H _) fun _ ↦
      LogShortS.bind (logShortS_observeWith H _) fun _ ↦
        LogShortS.bind (LogShortS.forIn _ (fun x _ ↦
          LogShortS.bind (logShortS_observeWith H x) fun _ ↦ LogShortS.pure _) _ _) fun _ ↦
          LogShortS.pure _
  refine LogShortS.bind (LogShortS.forIn _ (fun _ _ ↦ ?_) _ _) fun _ ↦ ?_
  · exact LogShortS.bind (logShortS_squeezeWith H) fun _ ↦
      LogShortS.bind (logShortS_squeezeWith H) fun _ ↦ LogShortS.pure _
  refine LogShortS.bind (logShortS_batchRoundsWith H _ _) fun ⟨_, _⟩ ↦ ?_
  dsimp only
  refine LogShortS.bind (LogShortS.forIn _ (fun _ _ ↦ ?_) _ _) fun _ ↦ ?_
  · exact LogShortS.bind (logShortS_squeezeWith H) fun _ ↦
      LogShortS.bind (logShortS_squeezeWith H) fun _ ↦
        LogShortS.bind (logShortS_squeezeWith H) fun _ ↦ LogShortS.pure _
  refine LogShortS.bind (logShortS_batchRoundsWith H _ _) fun ⟨_, _⟩ ↦ ?_
  dsimp only
  split <;> exact LogShortS.pure _

end Batch

end
end LeanVM.E2E.Complete
