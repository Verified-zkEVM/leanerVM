/-
  LeanVM.Guest.B1.Da.ListDigestM

  `da_hash_roots`, `da_list_digest` and `cover_da_root` under a hash model: the DA root list's
  answered digest (`daListDigestWith`), and the coverage read by transfer.
-/

module

public import LeanVM.Guest.B1.Da.ListDigest
public import LeanVM.Guest.B1.Digest.CommonM
public import LeanVM.Spec.NodeWith

/-!
# The DA root list over a hash model

`da_hash_roots__L{n}` is one chain of `n` blocks from the IV (`ListDigest.lean`). Under a
`HashModel` it is `HashModel.chain_blocks` (`HashModel.empty` for `n = 0`): the model answers the
list digest, `daListDigestWith M.H claims = some d` (`da_hash_roots_model`,
`da_list_digest_model`). `cover_da_root` has no `BLAKE2S` and carries over
(`cover_da_root_soundB`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-- **`da_hash_roots__L{n}` over a hash model**: the `n` DA claims at `roots` hash to their
answered list digest. -/
def Meaning_da_hash_rootsWith (M : HashModel) (n : ℕ) (rd : Reader) (args rets : List E) :
    Prop :=
  ∃ roots d0 d1, args = [roots] ∧ rets = [d0, d1] ∧ ∃ claims : List DaClaim,
    claims.length = n ∧ DaClaimsAt rd roots claims ∧
      ∃ d, daListDigestWith M.H claims = some d ∧ (d0, d1) = digestScalars d

/-- The bytes of the claims built from blocks of canonical cells are the blocks'. -/
theorem daList_bytes (n : ℕ) (b : ℕ → Fin 4 → E) (hc : ∀ i < n, ∀ r, IsCanonical128 (b i r)) :
    ((List.range n).map fun i => (cellsDigest (b i 0) (b i 1), cellsDigest (b i 2) (b i 3))).flatMap
        (fun c : DaClaim => digestBytes c.1 ++ digestBytes c.2) =
      (List.range n).flatMap fun j => blockBytes (b j) := by
  rw [List.flatMap_map]
  refine List.flatMap_congr fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [← blockBytes_daBlock]
  congr 1
  funext r
  simp only [daBlock, digestScalars_cellsDigest (hc i hi 0) (hc i hi 1),
    digestScalars_cellsDigest (hc i hi 2) (hc i hi 3)]
  fin_cases r <;> rfl

/-- `da_hash_roots__L{n}`'s body under a model, `n ≥ 1`, gives its meaning. -/
theorem da_hash_roots_succ_model {M : HashModel} (n : ℕ) (hn1 : 1 ≤ n) (rd : Reader)
    (args rets : List E)
    (h : Fn.SemB M.sem (coreProgram.RelB M.sem rd) rd ⟨hrNames.getD n "", [.n 0], hrBody n⟩
      args rets) :
    Meaning_da_hash_rootsWith M n rd args rets := by
  simp only [Fn.SemB, hrBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, hrBlock, List.forall_mem_cons, Atom.HoldsB,
    List.map_cons, List.map_nil, forall_mem_nil_iff, and_true] at h
  obtain ⟨σ, hp, ⟨⟨⟨h1, h2⟩, hblk⟩, h3, h4, h5, h6⟩, hr⟩ := h
  have hcan : ∀ i < n, ∀ r, IsCanonical128 (![σ (.n (3 + 7 * i)), σ (.n (4 + 7 * i)),
      σ (.n (5 + 7 * i)), σ (.n (6 + 7 * i))] r) := fun i hi =>
    (M.canonical (hblk i hi).2.2.2.2.2).1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, hd, hst⟩ := HashModel.chain_blocks (M := M) (n := m)
    (blocks := fun i => ![σ (.n (3 + 7 * i)), σ (.n (4 + 7 * i)), σ (.n (5 + 7 * i)),
      σ (.n (6 + 7 * i))]) (md := fun i => σ (.n (7 + 7 * i)))
    (st := fun i => (σ (.n (1 + 7 * i)), σ (.n (2 + 7 * i))))
    (by show (σ (.n 1), σ (.n 2)) = _; rw [h1, h2, iv0_word, iv1_word]; rfl)
    (fun j hj => by
      rw [(hblk j (by omega)).2.2.2.2.1, word_metadata]
      congr 1
      simp only [decide_eq_false_iff_not]
      omega)
    (by rw [(hblk m (by omega)).2.2.2.2.1, word_metadata]; simp)
    (fun j hj => (hblk j (by omega)).2.2.2.2.2)
  let claims : List DaClaim := (List.range (m + 1)).map fun i =>
    (cellsDigest (σ (.n (3 + 7 * i))) (σ (.n (4 + 7 * i))),
      cellsDigest (σ (.n (5 + 7 * i))) (σ (.n (6 + 7 * i))))
  have hlen : claims.length = m + 1 := by simp [claims]
  have hget : ∀ i (hi : i < m + 1), claims.getD i default =
      (cellsDigest (σ (.n (3 + 7 * i))) (σ (.n (4 + 7 * i))),
        cellsDigest (σ (.n (5 + 7 * i))) (σ (.n (6 + 7 * i)))) := by
    intro i hi
    simp [claims, List.getD_eq_getElem?_getD, hi]
  refine ⟨σ (.n 0), σ (.n (5 + 7 * (m + 1))), σ (.n (6 + 7 * (m + 1))), hp.symm, hr.symm, claims,
    hlen, ?_, d, ?_, ?_⟩
  · intro i hi
    have hi' : i < m + 1 := hlen ▸ hi
    have hc := hcan i hi'
    have c0 : IsCanonical128 (σ (.n (3 + 7 * i))) := hc 0
    have c1 : IsCanonical128 (σ (.n (4 + 7 * i))) := hc 1
    have c2 : IsCanonical128 (σ (.n (5 + 7 * i))) := hc 2
    have c3 : IsCanonical128 (σ (.n (6 + 7 * i))) := hc 3
    rw [← List.getD_eq_getElem _ default hi, hget i hi',
      digestScalars_cellsDigest c0 c1, digestScalars_cellsDigest c2 c3]
    exact ⟨(hblk i hi').1, (hblk i hi').2.1, (hblk i hi').2.2.1, (hblk i hi').2.2.2.1⟩
  · rw [daListDigestWith]
    refine Eq.trans (congrArg M.H ?_) hd
    exact daList_bytes (m + 1) (fun i => ![σ (.n (3 + 7 * i)), σ (.n (4 + 7 * i)),
      σ (.n (5 + 7 * i)), σ (.n (6 + 7 * i))]) hcan
  · rw [h5, h6, h3, h4]
    exact hst

/-- `da_hash_roots__L0`'s body under a model gives its meaning. -/
theorem da_hash_roots_zero_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : Fn.SemB M.sem (coreProgram.RelB M.sem rd) rd ⟨hrNames.getD 0 "", [.n 0], hrBody0⟩
      args rets) :
    Meaning_da_hash_rootsWith M 0 rd args rets := by
  simp only [Fn.SemB, hrBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] at h
  obtain ⟨σ, hp, h1, h2, h3, h4, h5, h6, h7, hc, h10, h11, hr⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7, word_zero, iv0_word, iv1_word] at hc
  obtain ⟨d, hd, hout⟩ := HashModel.empty (M := M) hc
  refine ⟨σ (.n 0), σ (.n 10), σ (.n 11), hp.symm, hr.symm, [], rfl,
    fun _ h => absurd h (by simp), d, hd, ?_⟩
  rw [h10, h11]
  exact hout

/-- **`da_hash_roots__L{n}` is sound under a hash model**: the answered list digest of the `n`
claims it reads. -/
theorem da_hash_roots_model {M : HashModel} (n : ℕ) (hn : n ≤ 16) (rd : Reader)
    (args rets : List E) (h : coreProgram.RelB M.sem rd (hrNames.getD n "") args rets) :
    Meaning_da_hash_rootsWith M n rd args rets := by
  rw [relB_of_find (find_da_hash_roots n hn)] at h
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · exact da_hash_roots_zero_model rd args rets h
  · simp only [show n ≠ 0 by omega, ↓reduceIte] at h
    exact da_hash_roots_succ_model n hn1 rd args rets h

/-- **`da_list_digest(roots, n_g)` over a hash model**: `n_g = g^n` for the `n ≤ 16` claims at
`roots`, hashed to their answered list digest. -/
def Meaning_da_list_digestWith (M : HashModel) (rd : Reader) (args rets : List E) : Prop :=
  ∃ roots n_g d0 d1, args = [roots, n_g] ∧ rets = [d0, d1] ∧ ∃ claims : List DaClaim,
    claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧ DaClaimsAt rd roots claims ∧
      ∃ d, daListDigestWith M.H claims = some d ∧ (d0, d1) = digestScalars d

/-- At the deployed model the meaning is the deployed one. -/
theorem meaning_da_list_digestWith_deployed (rd : Reader) (args rets : List E) :
    Meaning_da_list_digestWith HashModel.deployed rd args rets ↔
      Meaning_da_list_digest rd args rets := by
  simp only [Meaning_da_list_digestWith, Meaning_da_list_digest, daListDigestWith,
    HashModel.deployed, Option.some.injEq, exists_eq_left']
  rfl

/-- **`da_list_digest` is sound under a hash model** (G:3105-3109). -/
theorem da_list_digest_model {M : HashModel} (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "da_list_digest" args rets) :
    Meaning_da_list_digestWith M rd args rets := by
  rw [relB_of_find find_da_list_digest] at h
  simp only [Fn.SemB, List.map_cons, List.map_nil, Stmt.HoldsListB, Stmt.HoldsB,
    Atom.HoldsB] at h
  obtain ⟨σ, hp, ⟨⟨j, hj, hx, hc⟩, h4, h5, hr⟩⟩ := h
  have hj' : j ≤ 16 := by simp [hrNames] at hj; omega
  rw [← List.getD_eq_getElem _ "" hj] at hc
  obtain ⟨roots, d0, d1, hr0, hr1, claims, hlen, hcl, d, hd, hout⟩ :=
    da_hash_roots_model j hj' rd _ _ hc
  simp only [List.cons.injEq, and_true] at hr0 hr1
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 4), σ (.n 5), hp.symm, hr.symm, claims, hlen ▸ hj', ?_, ?_,
    d, hd, ?_⟩
  · rw [hx, hlen, gen_pow_eq_ofK]
  · rw [hr0]; exact hcl
  · rw [h4, h5, hr1.1, hr1.2]; exact hout

/-- `cover_da_root` is free of `BLAKE2S` and calls nothing. -/
theorem freeOn_cover_da_root : coreProgram.FreeOn ["cover_da_root"] = true := by
  decide +kernel

/-- **`cover_da_root` is sound under any semantics.** -/
theorem cover_da_root_soundB {S : BlakeSem} {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : coreProgram.RelB S rd "cover_da_root" args rets) : Meaning_cover_da_root rd args rets :=
  cover_da_root_sound hm
    ((relB_iff_rel_of_freeOn freeOn_cover_da_root (List.mem_singleton_self _) args rets).mp h)

end
end LeanVM.Guest.B1.Digest
