/-
  LeanVM.Guest.B1.Comp.Digest.SmallAtC

  `statement_digest`, `da_list_digest` and `cover_da_root` complete over a completeness model in the
  uniform placed form (`CompleteRelBS`): the model version of `B1/Digest/SmallAt.lean`.
-/

module

public import LeanVM.Guest.B1.Comp.CompleteAtB
public import LeanVM.Guest.B1.Digest.SmallAt
public import LeanVM.Guest.B1.Comp.Digest.Statement
public import LeanVM.Guest.B1.Comp.Da.ListDigest
public import LeanVM.Guest.Memory.SizeB

/-!
# The small callees of `main`, uniformly placed, over a completeness model

`SmallAt.lean`'s proofs under `CM.sem`, each digest the function returns answered by the model's
`CM.H` (`SdPreAtC`, `DaListPreAtC`; `CoverPreAt` hashes nothing):

* `sd_completeRelBS`, `dl_completeRelBS`: pure, so `completeAtS_of_rel_pureBat` on the model's
  relation (`statement_digest_comp`, `da_list_digest_comp`), every read pinned by the caller's
  words (`forced_agree`);
* `cover_completeRelBS`: `completeAtS_leafB` on its honest run, under any semantics;
* `…_completeRelB_of_comp`: at `CompModel.deployed` the deployed `sd_completeRelAtB`,
  `dl_completeRelAtB`, `cover_completeRelAtB` (with constant bounds).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.Node LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtB CompleteRelB CompleteAtBS CompleteRelBS DisjL disj_nil Within
  Returns completeRelBS_deployed)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ}

/-- The class is empty, or a memory of it exists (`completeRel_casesB` over `S`). -/
theorem completeRel_casesBS {κ : ℕ} {f : String} {Pre : Reader → List E → List E → Prop} {B : ℕ}
    (h : ∀ args rets Lin, (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      ∀ rd1, LowDef κ rd1 → MemL rd1 Lin → CompleteAtBS S fs cert κ f Lin args (Returns rets) B) :
    CompleteRelBS S fs cert κ f Pre B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin hpre rd1 hl1 hL1 fp
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL

/-! ## `statement_digest` -/

/-- `statement_digest`'s precondition over `H` (`SdPreAt`): the statement's digest answered. -/
def SdPreAtC (H : List UInt8 → Option Digest) (sig : Digest) (cells : List E) (rd : Reader) :
    List E → List E → Prop
  | [seed0, seed1, sigp, da0, da1, dp], [d0, d1] => ∃ (seed da : Digest),
      cells.length = deferStmtCells ∧ (seed0, seed1) = digestScalars seed ∧
      LoadHolds rd sigp 0 (digestScalars sig).1 ∧ LoadHolds rd sigp 1 (digestScalars sig).2 ∧
      (da0, da1) = digestScalars da ∧ CellsAt rd dp cells ∧
      ∃ pd, stmtDigestOfWith H seed sig da cells = some pd ∧ (d0, d1) = digestScalars pd
  | _, _ => False

theorem sdPreAtC_shape {H : List UInt8 → Option Digest} {sig : Digest} {cells : List E} {rd : Reader}
    {args rets : List E} (h : SdPreAtC H sig cells rd args rets) :
    ∃ seed0 seed1 sigp da0 da1 dp d0 d1, args = [seed0, seed1, sigp, da0, da1, dp] ∧
      rets = [d0, d1] := by
  unfold SdPreAtC at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- At the deployed hash, `SdPreAtC` is `SdPreAt`. -/
theorem sdPreAtC_deployed (sig : Digest) (cells : List E) (rd : Reader) (args rets : List E) :
    SdPreAtC CompModel.deployed.H sig cells rd args rets ↔ SdPreAt sig cells rd args rets := by
  constructor
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ := sdPreAtC_shape h
    simpa only [SdPreAtC, SdPreAt, show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      stmtDigestOfWith, Option.some.injEq, exists_eq_left', stmtDigestOf_eq_bytes] using h
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩ := sdPreAt_shape h
    simpa only [SdPreAtC, SdPreAt, show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      stmtDigestOfWith, Option.some.injEq, exists_eq_left', stmtDigestOf_eq_bytes] using h

/-- **`statement_digest` is complete over the model, uniformly placed** (`sd_completeRelAtB`), at
pinned reads, by trees within `B`. -/
theorem sd_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (sig : Digest) (cells : List E) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "statement_digest" fun _ => B) :
    CompleteRelBS CM.sem fs cert κ "statement_digest" (SdPreAtC CM.H sig cells) B := by
  refine completeRel_casesBS fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨seed0, seed1, sigp, da0, da1, dp, d0, d1, rfl, rfl⟩ := sdPreAtC_shape (hpre rd1 hl1 hL1)
  obtain ⟨seed, da, hlen, hs, -, -, hda, -, pd, hpd, hd⟩ := hpre rd1 hl1 hL1
  have g0 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.1) hl1 hL1 hL
  have g1 := fun rd (hL : MemL rd Lin) =>
    forced_agree (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.1) hl1 hL1 hL
  have gc : ∀ k (hk : k < cells.length) rd, MemL rd Lin → LoadHolds rd dp k cells[k] :=
    fun k hk _ hL => forced_agree
      (fun rd hl hL => (hpre rd hl hL).choose_spec.choose_spec.2.2.2.2.2.1 k hk) hl1 hL1 hL
  exact LeanVM.Guest.B1.completeAtS_of_rel_pureBat sd_pure (List.mem_singleton_self _) (fun rd hL =>
    statement_digest_comp rd _ _ ⟨_, _, _, _, _, _, _, _, rfl, rfl, seed, sig, da, cells, hlen, hs,
      g0 rd hL, g1 rd hL, hda, fun k hk => gc k hk rd hL, pd, hpd, hd⟩) κ
    (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo)

/-- The deployed `sd_completeRelAtB` (at a constant bound), from the model's at
`CompModel.deployed`. -/
theorem sd_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (sig : Digest)
    (cells : List E) {B : ℕ} (hB : TotalLe coreProgram fs "statement_digest" fun _ => B) :
    CompleteRelB fs cert κ "statement_digest" (SdPreAt sig cells) B := by
  have h := sd_completeRelBS (CM := CompModel.deployed) fs cert (κ := κ) sig cells (B := B)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hB)
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  exact fun args rets Lin hpre =>
    h args rets Lin fun rd hl hL => (sdPreAtC_deployed sig cells rd args rets).mpr (hpre rd hl hL)

/-! ## `da_list_digest` -/

/-- `da_list_digest`'s precondition over `H` (`DaListPreAt`): the list's digest answered. -/
def DaListPreAtC (H : List UInt8 → Option Digest) (claims : List DaClaim) (rd : Reader) :
    List E → List E → Prop
  | [roots, ng], [d0, d1] => claims.length ≤ 16 ∧ ng = gen ^ claims.length ∧
      LeanVM.Guest.B1.DaClaimsAt rd roots claims ∧
        ∃ d, daListDigestWith H claims = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

theorem daListPreAtC_shape {H : List UInt8 → Option Digest} {claims : List DaClaim} {rd : Reader}
    {args rets : List E} (h : DaListPreAtC H claims rd args rets) :
    ∃ roots ng d0 d1, args = [roots, ng] ∧ rets = [d0, d1] := by
  unfold DaListPreAtC at h
  split at h
  · exact ⟨_, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- At the deployed hash, `DaListPreAtC` is `DaListPreAt`. -/
theorem daListPreAtC_deployed (claims : List DaClaim) (rd : Reader) (args rets : List E) :
    DaListPreAtC CompModel.deployed.H claims rd args rets ↔ DaListPreAt claims rd args rets := by
  constructor
  · intro h
    obtain ⟨_, _, _, _, rfl, rfl⟩ := daListPreAtC_shape h
    simp only [DaListPreAtC, show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      daListDigestWith, Option.some.injEq, exists_eq_left'] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · intro h
    obtain ⟨_, _, _, _, rfl, rfl⟩ := daListPreAt_shape h
    exact ⟨h.1, h.2.1, h.2.2.1, _, rfl, h.2.2.2⟩

/-- **`da_list_digest` is complete over the model, uniformly placed** (`dl_completeRelAtB`), at
pinned claims, by trees within `B`. -/
theorem dl_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (claims : List DaClaim) {B : ℕ}
    (hB : TotalLeB CM.sem coreProgram fs "da_list_digest" fun _ => B) :
    CompleteRelBS CM.sem fs cert κ "da_list_digest" (DaListPreAtC CM.H claims) B := by
  refine completeRel_casesBS fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, ng, d0, d1, rfl, rfl⟩ := daListPreAtC_shape (hpre rd1 hl1 hL1)
  obtain ⟨hlen, hng, -, d, hdd, hd⟩ := hpre rd1 hl1 hL1
  have g : ∀ i (h : i < claims.length) rd, MemL rd Lin →
      (LoadHolds rd roots (4 * i) (digestScalars claims[i].1).1 ∧
      LoadHolds rd roots (4 * i + 1) (digestScalars claims[i].1).2 ∧
      LoadHolds rd roots (4 * i + 2) (digestScalars claims[i].2).1 ∧
      LoadHolds rd roots (4 * i + 3) (digestScalars claims[i].2).2) := fun i h rd hL =>
    ⟨forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.1) hl1 hL1 hL,
      forced_agree (fun rd hl hL => ((hpre rd hl hL).2.2.1 i h).2.2.2) hl1 hL1 hL⟩
  exact LeanVM.Guest.B1.completeAtS_of_rel_pureBat dl_pure List.mem_cons_self (fun rd hL =>
    da_list_digest_comp rd _ _ ⟨_, _, _, _, rfl, rfl, claims, hlen, hng,
      fun i h => g i h rd hL, d, hdd, hd⟩) κ
    (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo)

/-- The deployed `dl_completeRelAtB` (at a constant bound), from the model's at
`CompModel.deployed`. -/
theorem dl_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (claims : List DaClaim) {B : ℕ} (hB : TotalLe coreProgram fs "da_list_digest" fun _ => B) :
    CompleteRelB fs cert κ "da_list_digest" (DaListPreAt claims) B := by
  have h := dl_completeRelBS (CM := CompModel.deployed) fs cert (κ := κ) claims (B := B)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hB)
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  exact fun args rets Lin hpre =>
    h args rets Lin fun rd hl hL => (daListPreAtC_deployed claims rd args rets).mpr (hpre rd hl hL)

/-! ## `cover_da_root` -/

/-- **`cover_da_root` is complete under any semantics, uniformly placed** (`cover_completeRelAtB`),
at the slot `i`, on a memory defined below `2^κ`, `κ ≥ 16`. -/
theorem cover_completeRelBS (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (i : ℕ) :
    CompleteRelBS S fs cert κ "cover_da_root" (CoverPreAt i) (fs "cover_da_root") := by
  refine completeRel_casesBS fun args rets Lin hpre rd1 hl1 hL1 => ?_
  obtain ⟨roots, cover, nslots, mark, r0, r1, r2, r3, rfl, rfl⟩ := coverPreAt_shape (hpre rd1 hl1 hL1)
  obtain ⟨M, hM, hi, rfl, -, -⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin →
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] := by
    intro rd hl hL
    obtain ⟨M', -, -, -, h1, h2⟩ := hpre rd hl hL
    exact ⟨h1, h2⟩
  obtain ⟨im, him, hRm⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1) hl1 hL1
  have hFc : ∀ r, ∃ ic, r < 4 → (roots * gen ^ (4 * i)).limb 0 * gpow r = gpow ic ∧ RegionL Lin ic := by
    intro r
    by_cases hr : r < 4
    · obtain ⟨ic, h⟩ := forced_load (p := roots * gen ^ (4 * i)) (k := r)
        (v := [r0, r1, r2, r3][r]'(by simp; omega))
        (fun rd hl hL => (hpre' rd hl hL).2 r (by simp; omega)) hl1 hL1
      exact ⟨ic, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose cidx hcidx using hFc
  have h := LeanVM.Guest.B1.completeAtS_leafB (S := S) (fs := fs) (cert := cert) find_cover_da_root
    (by rw [Program.loop_of_find? find_cover_da_root]; decide +kernel) κ Lin
    [roots, cover, gen ^ M, mark] [r0, r1, r2, r3] [] (fun _ => [])
    (fun _ => List.Forall₂.nil) (fun fp rd hl _ hL => ?_)
  · simpa using h
  obtain ⟨hmark, hroot⟩ := hpre' rd hl hL
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete_low (fun j hj => hl j (lt_of_lt_of_le hj
    (Nat.pow_le_pow_right (by norm_num) hκ))) (e := i) (e' := M - 1 - i) (by omega) (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  set σ := listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3] with hσ
  have hroot' := hroot
  rw [pow_mul', ← gen_pow_four_mul] at hroot'
  have hH : ∀ a ∈ coverAtoms, a.HoldsB S rd σ := by
    simp only [coverAtoms, List.forall_mem_cons, forall_mem_nil_iff, Atom.HoldsB, hσ, listVal,
      List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨⟨l1, hk', l2⟩, hmark, hroot'.1, hroot'.2.1, hroot'.2.2.1, hroot'.2.2.2⟩
  refine ⟨σ, _, [.n 14, .n 15, .n 16, .n 17], rfl, by rw [coverBody_eq]; exact walk_atoms _ _ _, rfl,
    fun e he => ?_, calls_atoms _, by rw [addrs_atoms]; rfl, allocs_atoms _ (by decide),
    by rw [allocDsts_atoms (by decide)]; rfl, fun A hA => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact hH a ha
  · rw [loadAddrs_atoms, show coverAtoms.filterMap atomLoad? = [(.n 10, 0), (.n 13, 0), (.n 13, 1),
      (.n 13, 2), (.n 13, 3)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g13 : σ (.n 13) = roots * gen ^ (4 * i) := by
      show roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)) = _
      rw [pow4_eq _ _ rfl]
    rcases hA with rfl | rfl | rfl | rfl | rfl
    · exact ⟨im, him, Or.inr hRm⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 0 (by omega)).1, Or.inr (hcidx 0 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 1 (by omega)).1, Or.inr (hcidx 1 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 2 (by omega)).1, Or.inr (hcidx 2 (by omega)).2⟩
    · exact ⟨_, by rw [g13]; exact (hcidx 3 (by omega)).1, Or.inr (hcidx 3 (by omega)).2⟩

/-- The deployed `cover_completeRelAtB`, from `cover_completeRelBS` at `blakeDeployed`. -/
theorem cover_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (i : ℕ) : CompleteRelB fs cert κ "cover_da_root" (CoverPreAt i) (fs "cover_da_root") :=
  completeRelBS_deployed.mp (cover_completeRelBS fs cert hκ i)

end
end LeanVM.Guest.B1.Digest
