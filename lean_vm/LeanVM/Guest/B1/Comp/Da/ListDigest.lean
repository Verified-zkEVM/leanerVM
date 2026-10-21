/-
  LeanVM.Guest.B1.Comp.Da.ListDigest

  `da_hash_roots`, `da_list_digest` and `cover_da_root` over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Basic
public import LeanVM.Guest.B1.Da.ListDigestM

/-!
# The DA root list over a completeness model

The backward halves of `ListDigest.lean`'s iffs over a `CompModel`, from the meanings over the
model's answers (`Meaning_da_hash_rootsWith CM.hm`, `Meaning_da_list_digestWith CM.hm`: `CM.H`
answers the claims' bytes): `da_hash_roots__L{n}`'s `n` blocks check through the model's chain
(`CompModel.chain_checks_blocks`; the empty list's one block by `CompModel.check_empty`), and
`da_list_digest` dispatches to it. `cover_da_root` is free of `BLAKE2S`: its completeness carries
over (`cover_da_root_completeB`). At `CompModel.deployed` each gives the deployed backward
direction (`…_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node LeanVM.E2E.Complete

@[expose] public section

/-- The honest values of `da_hash_roots__L{n}` with the chain's cells `S` (`hrVals` at the
deployed chain). -/
noncomputable def hrValsC (n : ℕ) (roots : E) (claims : List DaClaim) (S : ℕ → E × E) (k : ℕ) :
    E :=
  if k = 0 then roots else
  if (k - 1) % 7 = 0 then (S ((k - 1) / 7)).1 else
  if (k - 1) % 7 = 1 then (S ((k - 1) / 7)).2 else
  if (k - 1) % 7 = 6 then hrM n ((k - 1) / 7) else
  if (k - 1) / 7 < n then blockAt (hrB claims ((k - 1) / 7)) ((k - 1) % 7 - 2) else
  if (k - 1) % 7 % 2 = 0 then (S ((k - 1) / 7)).1 else (S ((k - 1) / 7)).2

section
variable {n : ℕ} {roots : E} {claims : List DaClaim} {S : ℕ → E × E} (i : ℕ)

theorem hrValsC_0 : hrValsC n roots claims S 0 = roots := rfl

theorem hrValsC_1 : hrValsC n roots claims S (1 + 7 * i) = (S i).1 := by
  simp only [hrValsC, show ¬(1 + 7 * i = 0) by omega, show (1 + 7 * i - 1) / 7 = i by omega,
    show (1 + 7 * i - 1) % 7 = 0 by omega, ↓reduceIte]

theorem hrValsC_2 : hrValsC n roots claims S (2 + 7 * i) = (S i).2 := by
  simp only [hrValsC, show ¬(2 + 7 * i = 0) by omega, show (2 + 7 * i - 1) / 7 = i by omega,
    show (2 + 7 * i - 1) % 7 = 1 by omega, ↓reduceIte, one_ne_zero]

theorem hrValsC_7 : hrValsC n roots claims S (7 + 7 * i) = hrM n i := by
  simp only [hrValsC, show ¬(7 + 7 * i = 0) by omega, show (7 + 7 * i - 1) / 7 = i by omega,
    show (7 + 7 * i - 1) % 7 = 6 by omega, ↓reduceIte]
  simp

theorem hrValsC_cell (r : ℕ) (hr : r < 4) (hi : i < n) :
    hrValsC n roots claims S (3 + r + 7 * i) = blockAt (hrB claims i) r := by
  simp only [hrValsC, show ¬(3 + r + 7 * i = 0) by omega,
    show (3 + r + 7 * i - 1) / 7 = i by omega, show (3 + r + 7 * i - 1) % 7 = r + 2 by omega,
    show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega, hi, ↓reduceIte,
    Nat.add_sub_cancel]

theorem hrValsC_tail (r : ℕ) (hr : r < 4) :
    hrValsC n roots claims S (3 + r + 7 * n) = if r % 2 = 0 then (S n).1 else (S n).2 := by
  simp only [hrValsC, show ¬(3 + r + 7 * n = 0) by omega,
    show (3 + r + 7 * n - 1) / 7 = n by omega, show (3 + r + 7 * n - 1) % 7 = r + 2 by omega,
    show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega, lt_irrefl,
    ↓reduceIte, Nat.add_mod_right]

end

/-- The bytes of the honest blocks are the claims'. -/
theorem hrB_bytes (claims : List DaClaim) :
    (List.range claims.length).flatMap (fun j => blockBytes (hrB claims j)) =
      claims.flatMap fun c => digestBytes c.1 ++ digestBytes c.2 := by
  conv_rhs => rw [← range_map_getD claims default]
  rw [List.flatMap_map]
  exact List.flatMap_congr fun i _ => blockBytes_daBlock _

/-- `da_hash_roots__L{n}`'s body over a completeness model, `n ≥ 1`. -/
theorem da_hash_roots_succ_comp {CM : CompModel} (n : ℕ) (hn1 : 1 ≤ n) (rd : Reader)
    (args rets : List E) (hm : Meaning_da_hash_rootsWith CM.hm n rd args rets) :
    Fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd ⟨hrNames.getD n "", [.n 0], hrBody n⟩
      args rets := by
  simp only [Fn.SemB, hrBody, holdsListB_atoms, holdsListB_ret, List.forall_mem_append,
    forall_mem_flatMap_range, hrBlock, List.forall_mem_cons, Atom.HoldsB,
    List.map_cons, List.map_nil, forall_mem_nil_iff, and_true]
  obtain ⟨roots, d0, d1, rfl, rfl, claims, hlen, hroots, d, hdd, hd⟩ := hm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hH : CM.H ((List.range (m + 1)).flatMap fun j => blockBytes (hrB claims j)) = some d := by
    rw [← hlen, hrB_bytes]; exact hdd
  have hchk := CM.chain_checks_blocks (md := hrM (m + 1)) hH
    (fun j _ r => daBlock_canonical _ r)
    (fun j hj => by simp only [hrM]; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by simp [hrM])
  set X := (List.range (m + 1)).flatMap fun j => blockBytes (hrB claims j) with hX
  let S := CM.chainSt X d
  have hlenX : X.length = 64 * (m + 1) := by
    rw [hX, List.length_flatMap]
    simp [length_blockBytes]
    ring
  have hS0 : S 0 = ivCells := CM.chainSt_zero X d
  have hS : S (m + 1) = (d0, d1) := by
    rw [hd]
    exact CM.chainSt_succ_of d (n := m) (by rw [hlenX]; omega)
  refine ⟨fun v => hrValsC (m + 1) roots claims S v.idx, rfl, ⟨⟨⟨?_, ?_⟩, fun i hi => ?_⟩, ?_⟩, ?_⟩
  · show (S 0).1 = _
    rw [iv0_word, hS0]; rfl
  · show (S 0).2 = _
    rw [iv1_word, hS0]; rfl
  · have hc : ∀ r (hr : r < 4), hrValsC (m + 1) roots claims S (3 + r + 7 * i) =
        blockAt (hrB claims i) r := fun r hr => hrValsC_cell i r hr hi
    have hcl : claims.getD i default = claims[i]'(hlen ▸ hi) := List.getD_eq_getElem _ _ _
    have hR := hroots i (hlen ▸ hi)
    dsimp only
    rw [hrValsC_7, hrValsC_1, hrValsC_2, hrValsC_1, hrValsC_2,
      show 3 + 7 * i = 3 + 0 + 7 * i by rfl, show 4 + 7 * i = 3 + 1 + 7 * i by omega,
      show 5 + 7 * i = 3 + 2 + 7 * i by omega, show 6 + 7 * i = 3 + 3 + 7 * i by omega,
      hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega)]
    have hb : ∀ r, blockAt (hrB claims i) r = blockAt (daBlock claims[i]) r := by
      intro r; rw [hrB, hcl]
    rw [hrValsC_0, hb, hb, hb, hb]
    refine ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2, by rw [word_metadata]; rfl, ?_⟩
    rw [← hb, ← hb, ← hb, ← hb, show ![blockAt (hrB claims i) 0, blockAt (hrB claims i) 1,
      blockAt (hrB claims i) 2, blockAt (hrB claims i) 3] = hrB claims i by
        funext r; fin_cases r <;> rfl]
    exact hchk i (by omega)
  · dsimp only
    rw [show 3 + 7 * (m + 1) = 3 + 0 + 7 * (m + 1) by rfl,
      show 4 + 7 * (m + 1) = 3 + 1 + 7 * (m + 1) by omega,
      show 5 + 7 * (m + 1) = 3 + 2 + 7 * (m + 1) by omega,
      show 6 + 7 * (m + 1) = 3 + 3 + 7 * (m + 1) by omega,
      hrValsC_tail 0 (by omega), hrValsC_tail 1 (by omega), hrValsC_tail 2 (by omega),
      hrValsC_tail 3 (by omega), hrValsC_1, hrValsC_2]
    simp
  · dsimp only
    rw [show 5 + 7 * (m + 1) = 3 + 2 + 7 * (m + 1) by omega,
      show 6 + 7 * (m + 1) = 3 + 3 + 7 * (m + 1) by omega,
      hrValsC_tail 2 (by omega), hrValsC_tail 3 (by omega), hS]
    simp

/-- `da_hash_roots__L0`'s body over a completeness model. -/
theorem da_hash_roots_zero_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : Meaning_da_hash_rootsWith CM.hm 0 rd args rets) :
    Fn.SemB CM.sem (coreProgram.RelB CM.sem rd) rd ⟨hrNames.getD 0 "", [.n 0], hrBody0⟩
      args rets := by
  simp only [Fn.SemB, hrBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  obtain ⟨roots, d0, d1, rfl, rfl, claims, hl, -, d, hdd, hd⟩ := hm
  obtain rfl : claims = [] := List.eq_nil_of_length_eq_zero hl
  have hc := CM.check_empty (d := d) hdd
  rw [← hd] at hc
  refine ⟨listVal [roots, 0, 0, 0, 0, ivCells.1, ivCells.2,
    metadataCell 0 true, d0, d1, d0, d1], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals simp only [listVal, List.getD_cons_succ, List.getD_cons_zero]
  · exact word_zero.symm
  · exact word_zero.symm
  · exact word_zero.symm
  · exact word_zero.symm
  · exact iv0_word.symm
  · exact iv1_word.symm
  · rfl
  · exact hc

/-- **`da_hash_roots__L{n}` is complete over a completeness model**: when the model answers the
`n` claims' bytes, its relation holds under the model's semantics. -/
theorem da_hash_roots_comp {CM : CompModel} (n : ℕ) (hn : n ≤ 16) (rd : Reader)
    (args rets : List E) (hm : Meaning_da_hash_rootsWith CM.hm n rd args rets) :
    coreProgram.RelB CM.sem rd (hrNames.getD n "") args rets := by
  rw [relB_of_find (find_da_hash_roots n hn)]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact da_hash_roots_zero_comp rd args rets hm
  · simp only [show n ≠ 0 by omega, ↓reduceIte]
    exact da_hash_roots_succ_comp n h rd args rets hm

/-- **`da_list_digest` is complete over a completeness model** (G:3105-3109). -/
theorem da_list_digest_comp {CM : CompModel} (rd : Reader) (args rets : List E)
    (hm : Meaning_da_list_digestWith CM.hm rd args rets) :
    coreProgram.RelB CM.sem rd "da_list_digest" args rets := by
  rw [relB_of_find find_da_list_digest]
  simp only [Fn.SemB, List.map_cons, List.map_nil, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
  obtain ⟨roots, n_g, d0, d1, rfl, rfl, claims, hlen, rfl, hcl, d, hdd, hd⟩ := hm
  refine ⟨listVal [roots, gen ^ claims.length, d0, d1, d0, d1], rfl,
    ⟨claims.length, by simp [hrNames]; omega, by simp [listVal, gen_pow_eq_ofK], ?_⟩, rfl, rfl,
    rfl⟩
  rw [← List.getD_eq_getElem _ "" _]
  exact da_hash_roots_comp _ hlen rd _ _ ⟨roots, d0, d1, rfl, rfl, claims, rfl, hcl, d, hdd, hd⟩

/-- **`cover_da_root` is complete under any semantics** (free of `BLAKE2S`). -/
theorem cover_da_root_completeB {S : BlakeSem} {rd : Reader} (hm : MemOk rd)
    {roots cover mark r0 r1 r2 r3 : E} {i M : ℕ} (hM : M ≤ 2 ^ 16) (hi : i < M)
    (hmark : LoadHolds rd (cover * gen ^ i) 0 mark)
    (hroot : CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]) :
    coreProgram.RelB S rd "cover_da_root" [roots, cover, gen ^ M, mark] [r0, r1, r2, r3] :=
  (relB_iff_rel_of_freeOn freeOn_cover_da_root (List.mem_singleton_self _) _ _).mpr
    (cover_da_root_complete hm hM hi hmark hroot)

/-! ## At the deployed model -/

theorem meaning_da_hash_rootsWith_deployed (n : ℕ) (rd : Reader) (args rets : List E) :
    Meaning_da_hash_rootsWith CompModel.deployed.hm n rd args rets ↔
      Meaning_da_hash_roots n rd args rets := by
  simp only [Meaning_da_hash_rootsWith, Meaning_da_hash_roots, daListDigestWith,
    CompModel.hm, CompModel.deployed, Option.some.injEq, exists_eq_left']
  rfl

theorem da_hash_roots_of_comp (n : ℕ) (hn : n ≤ 16) (rd : Reader) (args rets : List E)
    (h : Meaning_da_hash_roots n rd args rets) :
    coreProgram.Rel rd (hrNames.getD n "") args rets := by
  rw [← relB_deployed]
  exact da_hash_roots_comp (CM := CompModel.deployed) n hn rd args rets
    ((meaning_da_hash_rootsWith_deployed n rd args rets).mpr h)

theorem da_list_digest_of_comp (rd : Reader) (args rets : List E)
    (h : Meaning_da_list_digest rd args rets) :
    coreProgram.Rel rd "da_list_digest" args rets := by
  rw [← relB_deployed]
  exact da_list_digest_comp (CM := CompModel.deployed) rd args rets
    ((meaning_da_list_digestWith_deployed rd args rets).mpr h)

end
end LeanVM.Guest.B1.Digest
