/-
  LeanVM.Guest.B1.Comp.Sig.CompleteAtC

  The signature verifiers complete over a completeness model in the uniform placed form
  (`CompleteRelBS`): the model version of `B1/Sig/CompleteAt.lean`'s `CompleteRelB` lemmas.
-/

module

public import LeanVM.Guest.B1.Comp.CompleteAtB
public import LeanVM.Guest.B1.Sig.CompleteAt
public import LeanVM.Guest.Memory.GuestRelInB
public import LeanVM.Guest.Memory.SizeB
public import LeanVM.Guest.B1.Comp.Sig.Sphincs

/-!
# The signature verifiers placed, over a completeness model

`CompleteAt.lean` lifts `verify_lean_xmss_iff.mpr` and `verify_sig_lean_sphincs_iff.mpr` to the
uniform placed form on every memory defined below `2^κ` holding the caller's words: the relation
on one restricted memory (`lowLin`) is a `RelIn` loading only the claim
(`xmss_relIn`, `sphincs_relIn`), which transfers to every frame pointer and memory
(`lowLin_relAtInB`). Over a `CompModel` the same steps under `CM.sem`, from
`verify_lean_xmss_rel_comp` and `verify_sig_lean_sphincs_rel_comp` (the forest keys by
`fkCompleteC_relB`):

* `lowLin_relAtInBS`, `xmss_relInB`, `sphincs_relInB`: the steps over any semantics;
* `verify_lean_xmss_completeRelBS`, `verify_sig_lean_sphincs_completeRelBS`: `CompleteRelBS CM.sem`
  at the meanings with the model's answered hash (`Meaning_…With CM.H`), by trees within a bound;
* `completeRelBS_deployed` (`Comp/CompleteAtB.lean`): at `blakeDeployed`, `CompleteRelBS` is
  `CompleteRelB`, so the deployed
  `verify_lean_xmss_completeRelB`, `verify_sig_lean_sphincs_completeRelB` are recovered at
  `CompModel.deployed` (`…_completeRelB_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ}

namespace Sig

/-- **The relation on `lowLin` transfers, over any semantics** (`lowLin_relAtInB`). -/
theorem lowLin_relAtInBS {Sz : List String} (hS : coreProgram.PureIn Sz) {g : String} (hg : g ∈ Sz)
    {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL1 : MemL rd1 Lin) {args rets : List E}
    (h : coreProgram.RelInB S (lowLin rd1 κ Lin) (RegionL Lin) g args rets) {B : ℕ}
    (hB : ∀ rd (t : Tree), t.name = g → t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ B) :
    CompleteAtBS S fs cert κ g Lin args (Returns rets) B := by
  obtain ⟨n, hn⟩ := relAtInB_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg h
  intro fp
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp (lowLin rd1 κ Lin) (fun _ _ => rfl) (fun _ h => h)
    rw [← ht]; exact hB _ t hname hv hbo
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, hnB, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtInS_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, Main.restrict_of ⟨i, rfl, Or.inl hi⟩, Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := Main.restrict_supp' rd1 _ _ _ hv
    · rw [Main.memL_agree hL' hL1 i hi, ← Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- `verify_lean_xmss` loads only its claim, over any semantics (`xmss_relIn`). -/
theorem xmss_relInB {rd : Reader} {R : ℕ → Prop} {p : E}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i)
    (h : coreProgram.RelB S rd "verify_lean_xmss" [p] []) :
    coreProgram.RelInB S rd R "verify_lean_xmss" [p] [] := by
  refine relInB_of_inv (fun f args => f = "verify_lean_xmss" ∧ args = [p])
    (fun f args σ fn es vs hI hf hp hw _ => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  rw [find_verify_lean_xmss, Option.some.injEq] at hf
  subst hf
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  have hsig : Stmt.sigOkList claimLoad [] xBody = true := xBody_eq ▸ xBody_sigOk
  have hw' : walk σ xBody = .ret es vs := hw
  generalize xBody = B at hsig hw'
  have hall := walk_sigOk (σ := σ) B hsig
  rw [hw'] at hall
  refine ⟨fun A hA => ?_, fun c hc ht => absurd (calls_in hall hc ht) List.not_mem_nil⟩
  obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
  rw [hp]
  exact hreg off hoff

/-- `verify_sig_lean_sphincs` loads only its claim and calls only the forest keys, which load
nothing, over any semantics (`sphincs_relIn`). -/
theorem sphincs_relInB {rd : Reader} {R : ℕ → Prop} {p : E}
    (hreg : ∀ k < 4, ∃ i, p.limb 0 * gpow k = gpow i ∧ R i)
    (h : coreProgram.RelB S rd "verify_sig_lean_sphincs" [p] []) :
    coreProgram.RelInB S rd R "verify_sig_lean_sphincs" [p] [] := by
  refine relInB_of_inv (fun f args => (f = "verify_sig_lean_sphincs" ∧ args = [p]) ∨ f ∈ fkNames)
    (fun f args σ fn es vs hI hf hp hw _ => ?_) (Or.inl ⟨rfl, rfl⟩) h
  rcases hI with ⟨rfl, rfl⟩ | hI
  · rw [find_verify_sig_lean_sphincs, Option.some.injEq] at hf
    subst hf
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    have hsig : Stmt.sigOkList claimLoad fkNames sBody = true := sBody_eq ▸ sBody_sigOk
    have hw' : walk σ sBody = .ret es vs := hw
    generalize sBody = B at hsig hw'
    have hall := walk_sigOk (σ := σ) B hsig
    rw [hw'] at hall
    refine ⟨fun A hA => ?_, fun c hc ht => Or.inr (calls_in hall hc ht)⟩
    obtain ⟨off, hoff, rfl⟩ := loads_claim hall A hA
    rw [hp]
    exact hreg off hoff
  · obtain ⟨t, ht, rfl⟩ := mem_fkNames hI
    rw [find_fk ht, Option.some.injEq] at hf
    subst hf
    have hw' : walk σ (fkBody t) = .ret es vs := hw
    have hall := walk_sigOk (σ := σ) (fkBody t) (fkBody_sigOk t)
    rw [hw'] at hall
    exact ⟨fun A hA => (loads_none hall A hA).elim, fun c hc ht => absurd (calls_in hall hc ht) List.not_mem_nil⟩

end Sig

/-- **`verify_lean_xmss` is complete over the model, uniformly placed** (`verify_lean_xmss_completeRelB`):
on memories defined below `2^κ`, `κ ≥ 6`, at every claim some signature verifies with the model's
answered hash, by trees within `B`. -/
theorem verify_lean_xmss_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} {B : ℕ} (hB : TotalLeB CM.sem coreProgram fs "verify_lean_xmss" fun _ => B) (hκ : 6 ≤ κ) :
    CompleteRelBS CM.sem fs cert κ "verify_lean_xmss" (Meaning_verify_lean_xmssWith CM.H) B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.RelB CM.sem (lowLin rd1 κ Lin) "verify_lean_xmss" [p] [] :=
    verify_lean_xmss_rel_comp (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInBS xmss_pure (List.mem_singleton_self _) hL1
    (xmss_relInB (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0)
    (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo) fp

/-- **`verify_sig_lean_sphincs` is complete over the model, uniformly placed**
(`verify_sig_lean_sphincs_completeRelB`): on memories defined below `2^κ`, `κ ≥ 8`, at every claim
some signature verifies with the model's answered hash, by trees within `B`. -/
theorem verify_sig_lean_sphincs_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} {B : ℕ} (hB : TotalLeB CM.sem coreProgram fs "verify_sig_lean_sphincs" fun _ => B)
    (hκ : 8 ≤ κ) :
    CompleteRelBS CM.sem fs cert κ "verify_sig_lean_sphincs" (Meaning_verify_sig_lean_sphincsWith CM.H) B := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, rfl, rfl, pk, m, hc1, sig, hv⟩ := hpre rd1 hl1 hL1
  have hreg := claim_region hl1 hL1 (p := p) fun rd hl hL => by
    obtain ⟨p', hp', -, pk', m', hc', -⟩ := hpre rd hl hL
    rw [List.cons.injEq] at hp'
    exact ⟨pk'.root, pk'.parameter, m', hp'.1 ▸ hc'⟩
  have h0 : coreProgram.RelB CM.sem (lowLin rd1 κ Lin) "verify_sig_lean_sphincs" [p] [] :=
    verify_sig_lean_sphincs_rel_comp
      (lowLin_memOK hl1 (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)))
      ⟨p, rfl, rfl, pk, m, lowLin_claim hc1 hreg, sig, hv⟩
  exact lowLin_relAtInBS sphincs_pure (List.mem_cons_self ..) hL1
    (sphincs_relInB (fun k hk => let ⟨i, h1, h2⟩ := hreg k hk; ⟨i, h1, h2⟩) h0)
    (fun rd t hn hv hbo => hB rd t _ _ hn hv hbo) fp

/-- The deployed `verify_lean_xmss_completeRelB`, from the model's at `CompModel.deployed`. -/
theorem verify_lean_xmss_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {B : ℕ}
    (hB : TotalLe coreProgram fs "verify_lean_xmss" fun _ => B) (hκ : 6 ≤ κ) :
    CompleteRelB fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss B := by
  have h := verify_lean_xmss_completeRelBS (CM := CompModel.deployed) fs cert (B := B)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hB) hκ
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  intro args rets Lin hpre
  refine h args rets Lin fun rd hl hL => ?_
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := hpre rd hl hL
  exact ⟨p, ha, hr, pk, m, hc, sig, by
    rw [show CompModel.deployed.H = fun x ↦ some (LeanVM.Protocol.Blake2sHash.blake2sBytes x) from rfl,
      LeanVM.E2E.xmssVerifyWith_some_blake2s, hv]⟩

/-- The deployed `verify_sig_lean_sphincs_completeRelB`, from the model's at `CompModel.deployed`. -/
theorem verify_sig_lean_sphincs_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    {B : ℕ} (hB : TotalLe coreProgram fs "verify_sig_lean_sphincs" fun _ => B) (hκ : 8 ≤ κ) :
    CompleteRelB fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs B := by
  have h := verify_sig_lean_sphincs_completeRelBS (CM := CompModel.deployed) fs cert (B := B)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hB) hκ
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  intro args rets Lin hpre
  refine h args rets Lin fun rd hl hL => ?_
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := hpre rd hl hL
  exact ⟨p, ha, hr, pk, m, hc, sig, by
    rw [show CompModel.deployed.H = fun x ↦ some (LeanVM.Protocol.Blake2sHash.blake2sBytes x) from rfl,
      LeanVM.E2E.sphincsVerifyWith_some_blake2s, hv]⟩

end
end LeanVM.Guest.B1
