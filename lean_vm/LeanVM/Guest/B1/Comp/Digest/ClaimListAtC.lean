/-
  LeanVM.Guest.B1.Comp.Digest.ClaimListAtC

  `claim_list_digest` complete over a completeness model in the uniform placed form
  (`CompleteRelBS`): the model version of `B1/Digest/ClaimListAt.lean`'s `cld_completeRelAtB`.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.B1.Comp.Digest.ClaimList
public import LeanVM.Guest.B1.Comp.Digest.NodeAtC
public import LeanVM.Guest.Memory.SizeTotalB

/-!
# `claim_list_digest`, uniformly placed, over a completeness model

`ClaimListAt.lean`'s proof under `CM.sem`, the claims' digest the model's answer (`ClPreAtC CM.H`):
the windows' scratch table holds the model's chain states (`clSlotC`, `clScratchLC`, read back as
`ClScratchC`), `__loop86` holds by `windows_bwdC`, the tail by `claims_tail_compB`, the body by
`cld_holds_zeroC`/`cld_holds_posC`; the bounds are the callees' `TotalLeB CM.sem`/`TotalLeOnB
CM.sem` facts (`cld_completeRelBS`). At `CompModel.deployed` the deployed `cld_completeRelAtB`
(`cld_completeRelB_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAtBS CompleteRelBS CompleteRelB kidsBound DisjL disj_nil disj_append
  Within Returns Kid completeRelBS_deployed)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `claim_list_digest`'s precondition over `H` (`ClPreAt`): the claims' digest answered. -/
def ClPreAtC (H : List UInt8 → Option Digest) (cs : List E) (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
      cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        ∃ d, H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

theorem clPreAtC_shape {H : List UInt8 → Option Digest} {cs : List E} {rd : Reader} {args rets : List E}
    (h : ClPreAtC H cs rd args rets) : ∃ p ng gsq d0 d1, args = [p, ng, gsq] ∧ rets = [d0, d1] := by
  unfold ClPreAtC at h
  split at h
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- At the deployed hash, `ClPreAtC` is `ClPreAt`. -/
theorem clPreAtC_deployed (cs : List E) (rd : Reader) (args rets : List E) :
    ClPreAtC CompModel.deployed.H cs rd args rets ↔ ClPreAt cs rd args rets := by
  constructor
  · intro h
    obtain ⟨_, _, _, _, _, rfl, rfl⟩ := clPreAtC_shape h
    obtain ⟨hT, n, hn, hng, hlen, hc, hcan, d, hdd, hd⟩ := h
    simp only [show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      Option.some.injEq] at hdd
    exact ⟨hT, n, hn, hng, hlen, hc, hcan, by rw [hdd]; exact hd⟩
  · intro h
    have hsh : ∃ p ng gsq d0 d1, args = [p, ng, gsq] ∧ rets = [d0, d1] := by
      unfold ClPreAt at h
      split at h
      · exact ⟨_, _, _, _, _, rfl, rfl⟩
      · exact h.elim
    obtain ⟨_, _, _, _, _, rfl, rfl⟩ := hsh
    obtain ⟨hT, n, hn, hng, hlen, hc, hcan, hd⟩ := h
    exact ⟨hT, n, hn, hng, hlen, hc, hcan, _, rfl, hd⟩

/-! ## The scratch table over the model -/

/-- The windows' scratch slot `q` over the model (`clSlot`): the model's state after `32q` blocks. -/
def clSlotC (CM : CompModel) (p : E) (cs : List E) (q : ℕ) : List E :=
  [(CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).1,
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * q))).2, eOfNat (2 ^ 11 * q), p * gen ^ (128 * q)]

/-- The windows' scratch table at `g^cx` over the model (`clScratchL`). -/
def clScratchLC (CM : CompModel) (p : E) (cs : List E) (cx w : ℕ) : Layout :=
  (List.range (w + 1)).map fun q => (cx + 4 * q, clSlotC CM p cs q)

theorem clScratchC_of_memL {CM : CompModel} {rd : Reader} {L : Layout} (h : MemL rd L) {p : E}
    {cs : List E} {cx w : ℕ} (hs : ∀ q ∈ clScratchLC CM p cs cx w, q ∈ L) :
    ClScratchC CM rd p (gen ^ cx) cs w := fun q hq => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩))

theorem clScratchC_region {CM : CompModel} {p : E} {cs : List E} {cx w i : ℕ}
    (h : RegionL (clScratchLC CM p cs cx w) i) : cx ≤ i ∧ i < cx + 4 * (w + 1) := by
  obtain ⟨q, hq, h1, h2⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  simp only [clSlotC, List.length_cons, List.length_nil] at h1 h2
  have := List.mem_range.mp hj
  omega

theorem clScratchLC_within {CM : CompModel} {p : E} {cs : List E} {cx w : ℕ} :
    Within (clScratchLC CM p cs cx w) cx (4 * (w + 1)) := fun q hq => by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hj
  simp only [clSlotC, List.length_cons, List.length_nil]
  omega

theorem clScratchLC_disj {CM : CompModel} {p : E} {cs : List E} {cx w : ℕ} :
    DisjL (clScratchLC CM p cs cx w) := by
  unfold DisjL clScratchLC
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := w + 1)).imp fun {a b} h => Or.inl (by simp only [clSlotC]; simp; omega)

/-! ## `claim_list_digest`, placed over the model -/

/-- **`claim_list_digest` is complete over a completeness model, uniformly placed, at the claims
`cs`** (`cld_completeRelAtB`): on a memory defined below `2^κ`, `κ ≥ 16`, at claims whose digest the
model answers, by trees within `cldBound` of the callees' bounds under `CM.sem`. -/
theorem cld_completeRelBS {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) (cs : List E) (B86 : E → ℕ) (Bct : ℕ → ℕ) (Bsl6 : ℕ)
    (h86 : TotalLeOnB CM.sem coreProgram fs "__loop86" LoopPre fun a => B86 (a.getD 1 0))
    (hct : ∀ t, t < 32 → TotalLeB CM.sem coreProgram fs ctNames[t]! fun _ => Bct t)
    (hsl6 : TotalLeB CM.sem coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelBS CM.sem fs cert κ "claim_list_digest" (ClPreAtC CM.H cs)
      (cldBound fs B86 Bct Bsl6 (cs.length / 4)) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, ng, gsq, d0, d1, rfl, rfl⟩ := clPreAtC_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, n, hn, rfl, hlen, hcells1, hcan, d, hH, hd⟩ := hpre rd1 hl1 hL1
  rw [show cs.length / 4 = n by omega]
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin → SquaresAt rd gsq ∧ CellsAt rd p cs := by
    intro rd hl hL
    obtain ⟨hT, -, -, -, -, hc', -⟩ := hpre rd hl hL
    exact ⟨hT, hc'⟩
  -- the claims' and the squares' words are the caller's
  have hF : ∀ k, ∃ i, k < 4 * n → p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
    intro k
    by_cases hk : k < 4 * n
    · obtain ⟨i, hi⟩ := forced_load (v := cs[k]'(by omega))
        (fun rd hl hL => (hpre' rd hl hL).2 k (by omega)) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose idx hidx using hF
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hcellsR : ∀ rd, MemL rd Lin → CellsAt rd p cs := fun rd hL k hk =>
    load_agree hL hL1 (hidx k (by omega)).1 (hidx k (by omega)).2 (hcells1 k hk)
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- no claims: the empty digest
    obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      by unfold cldBound; omega, fun rd hl hL => ?_⟩
    have h4 : listVal (cldZeroListS p gsq d0 d1) (.n 4) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_cld_zero _ h4
    have hev := holdsB_of_holdsList find_claim_list_digest (cld_holds_zeroC (CM := CM) rd p gsq hH hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := cld_zero_events (listVal (cldZeroListS p gsq d0 d1))
    have h := relAtInB_of_walk (S := CM.sem) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd)
      coreProgram_wf (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0)
      find_claim_list_digest (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl)
      (by rw [e3]; simp) (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp)
      (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  -- the windows' scratch table, the tail, the last claim
  have hpK : IsInK p := (hcells1 0 (by omega)).1
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  obtain ⟨cx, hcx⟩ : ∃ cx, cx = fp + fs "claim_list_digest" := ⟨_, rfl⟩
  set KL : Layout := clScratchLC CM p cs cx w ++ pinL (fun k => cs.getD k 0) idx (4 * n) ++
    pinL (fun j => gen ^ 2 ^ j) sidx 16 with hKL
  have hKLmem : ∀ rd', MemL rd' KL →
      SquaresAt rd' gsq ∧ CellsAt rd' p cs ∧ ClScratchC CM rd' p (gen ^ cx) cs w := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1)
        (fun q hq => List.mem_append_right _ hq) j hj,
      fun k hk => ?_, clScratchC_of_memL h fun q hq => List.mem_append_left _ (List.mem_append_left _ hq)⟩
    have := pin_loads h hpK (fun k hk => (hidx k hk).1)
      (fun q hq => List.mem_append_left _ (List.mem_append_right _ hq)) k (by omega)
    rwa [List.getD_eq_getElem _ _ hk] at this
  have r86 : ∀ rd', MemL rd' KL → w ≠ 0 →
      coreProgram.RelB CM.sem rd' "__loop86" [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] := fun rd' h hw0 => by
    obtain ⟨hT', hc', hs'⟩ := hKLmem rd' h
    have hsteps := windows_bwdC hT' hlen (by omega) hn hH hc' hcan hs'
    rw [word_one, ← pow_zero gen]
    exact loopB_bwd (B := L86Step rd' (gen ^ cx) gsq (coreProgram.RelB CM.sem rd'))
      (fun x hB hK hnext => l86_step_bwdB rd' (gen ^ w) (gen ^ cx) gsq x hB hK hnext)
      (Nat.pos_of_ne_zero hw0) rfl (fun j _ h2 => hsteps j h2)
  have rct : ∀ rd', MemL rd' KL → coreProgram.RelB CM.sem rd' ctNames[t]! (clSlotC CM p cs w)
      [(CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).1,
        (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).2,
        p * gen ^ (128 * w) * gen ^ (4 * t)] := fun rd' h => by
    obtain ⟨-, hc', -⟩ := hKLmem rd' h
    rw [ctNames_getElem! ht32]
    refine claims_tail_compB t ht32 rd' _ _ ⟨_, _, _, _, _, _, _, rfl, rfl, rfl,
      sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hc' (by omega)
    · have := chainSteps_cells CM hlen hH hcan (k := 32 * w) (m := t) (by omega)
        (blocksOf_sliceOf cs (32 * w) t) (fun j hj => baseMd_eq w j (by omega))
      rwa [show 32 * w + t = n - 1 by omega] at this
  have rsl : ∀ rd', MemL rd' KL →
      coreProgram.RelB CM.sem rd' "scaled_log__L6" [gen ^ n, gsq] [eOfNat (2 ^ 6 * n)] :=
    fun rd' h => (scaled_log_6_iffB (hKLmem rd' h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  let ks : List Kid := [⟨"__loop86", decide (word 1 0 0 + gen ^ w ≠ 0), [word 1 0 0, gen ^ w, gen ^ cx, gsq],
      KL, Returns []⟩,
    ⟨ctNames[t]!, true, clSlotC CM p cs w, KL, Returns [(CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).1,
      (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1))).2, p * gen ^ (128 * w) * gen ^ (4 * t)]⟩,
    ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL, Returns [eOfNat (2 ^ 6 * n)]⟩]
  have hne := ct_ne t ht32
  let bd : Kid → ℕ := fun k => if k.f = "__loop86" then B86 (gen ^ w)
    else if k.f = "scaled_log__L6" then Bsl6 else Bct t
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtBS CM.sem fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk htk
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : w ≠ 0 := by
        intro hw0
        simp only [hw0, pow_zero, word_one, e_add_self, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true] at htk
      have hpre86 : LoopPre [word 1 0 0, gen ^ w, gen ^ cx, gsq] := by
        rw [word_one]
        exact loopPre_gen (Nat.pos_of_ne_zero hw0) (by omega) _
      exact LeanVM.Guest.B1.completeAtS_of_rel_pureBat cldKid_pure (by simp [cldKidSet])
        (fun rd' h => r86 rd' h hw0) κ
        fun rd t hn hv hb => h86 rd t [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] hn hpre86 hv hb
    · refine (LeanVM.Guest.B1.completeAtS_of_rel_pureB cldKid_pure (by
        rw [ctNames_getElem! ht32]; simp only [cldKidSet, List.mem_append]
        rw [List.getD_eq_getElem _ _ (by simp [ctNames]; omega)]
        exact Or.inr (List.getElem_mem _)) rct κ (hct t ht32)).mono le_rfl
        (by simp only [bd, hne.1, hne.2, ↓reduceIte, le_refl])
    · exact LeanVM.Guest.B1.completeAtS_of_rel_pureB cldKid_pure (by simp [cldKidSet]) rsl κ hsl6
  obtain ⟨N, LK, outs, hout, hWK, hDK, hNb, -, hK⟩ :=
    LeanVM.Guest.B1.kidsFromInS_of_kidsB (S := CM.sem) (fs := fs) (cert := cert) κ bd ks hok
      (cx + 4 * (w + 1))
  refine ⟨fs "claim_list_digest" + 4 * (w + 1) + N, clScratchLC CM p cs cx w ++ LK, [d0, d1], [],
    ⟨rfl, rfl⟩, ?_, ?_, ?_, fun rd hl hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨clScratchLC_within.mono (by omega) (by omega), hWK.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append clScratchLC_disj hDK clScratchLC_within hWK le_rfl
  · have hw' : w = (n - 1) / 32 := hw
    have e1 : ("scaled_log__L6" = "__loop86") = False := by decide
    simp only [kidsBound, ks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bd, hne.1, hne.2,
      e1, ↓reduceIte, Nat.add_zero] at hNb
    unfold cldBound
    rw [← hw', ← ht]
    split at hNb <;> omega
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLs, hLK⟩ := Main.memL_append.mp hLo
  have hT := (hpre' rd hl hLin).1
  have hscr : ClScratchC CM rd p (gen ^ cx) cs w := clScratchC_of_memL hLs fun q hq => hq
  obtain ⟨t1, t2, t3, t4, hh⟩ := cld_holds_posC (hlow rd hl) hT hn hn1 hlen (hcellsR rd hLin) hcan
    (by rw [← hw]; exact hscr) hH hd
  rw [← hw, ← ht] at hh
  set σ := listVal (cldListS p gsq (gen ^ cx) d0 d1 cs n w t t1 t2 t3 t4
    (CM.st (prefixAt (cs.flatMap cellBytes) (32 * w)))
    (CM.st (prefixAt (cs.flatMap cellBytes) (n - 1)))) with hσ
  have h4 : σ (.n 4) ≠ 0 := fun h' => by
    have h'' : gen ^ n + word 1 0 0 = 0 := h'
    rw [word_one] at h''
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
    omega
  have hw' := walk_cld_pos σ h4 ht32 (gen_pow_eq_ofK t)
  have hev := holdsB_of_holdsList find_claim_list_digest hh hw'
  obtain ⟨e1, e2, e3, e4, e5⟩ := cld_pos_events σ t
  have h35 : logG (σ (.n 35)) = 4 * (w + 1) := by
    rw [show σ (.n 35) = gen ^ (4 * (w + 1)) by
      show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
      rw [word_gen]; ring]
    exact logG_gen_pow (by omega)
  rw [h35] at e2
  have hown : ∀ i, cx ≤ i → i < cx + 4 * (w + 1) →
      ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" (allocs σ (cldEs σ t)) (cldEs σ t) i :=
    fun i h1 h2 => Or.inl ⟨(4 * (w + 1), cx), by rw [e2, hcx]; exact List.mem_singleton_self _, h1, by omega⟩
  have h := relAtInB_of_walk (S := CM.sem) (P := coreProgram) (fs := fs) (cert := cert) (rd := rd)
    coreProgram_wf (R := RegionL Lin) (D := RegionL [])
    (Dk := fun i => False ∨ LeanVM.Guest.B1.outRegion ks outs i) (fp := fp)
    (N := N) find_claim_list_digest (Or.inl (by decide +kernel)) rfl hw' rfl hev
    (by rw [e1, e2, ← hcx]; simp only [List.map_cons, List.map_nil, bases]; rw [← gen_pow_eq_ofK]; rfl)
    (by rw [e3]; simp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  · rw [e4, e2, List.sum_cons, List.sum_nil, Nat.add_zero, ← hcx]
    match outs, hout with
    | [o1, o2, o3], ⟨h1, h2, h3, _⟩ =>
      refine hK rd σ _ _ (fun _ => False) ⟨rfl, rfl, fun htk => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩,
        rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩ hl hLK ?_ ?_
      · rw [(h1 htk).1]; rfl
      · rw [(h2 rfl).1]; rfl
      · rw [(h3 rfl).1]; rfl
      · have hKLr : MemL rd KL := by
          rw [hKL, Main.memL_append, Main.memL_append]
          refine ⟨⟨hLs, pin_memL hLin hL1 (fun k hk => (hidx k hk).2) fun k hk => ?_⟩,
            pin_memL hLin hL1 (fun j hj => (hsidx j hj).2) fun j hj => ?_⟩
          · have := (hcells1 k (by omega)).2
            rw [(hidx k hk).1, ← List.getD_eq_getElem _ 0] at this
            exact this
          · have := (hT1 j hj).2
            rw [(hsidx j hj).1] at this
            exact this
        simp only [LeanVM.Guest.B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact Main.memL_append.mpr ⟨hKLr, Main.memL_append.mpr ⟨hKLr, hKLr⟩⟩
      · have hR : ∀ i, RegionL KL i → RegionL Lin i ∨
            ownData cert fp cx "claim_list_digest" [4 * (w + 1)] (cldEs σ t) i := by
          intro i hi
          obtain ⟨q, hq, hq1, hq2⟩ := hi
          rw [hKL, List.mem_append, List.mem_append] at hq
          rcases hq with (hq | hq) | hq
          · obtain ⟨h1, h2⟩ := clScratchC_region ⟨q, hq, hq1, hq2⟩
            exact Or.inr (Or.inl ⟨(4 * (w + 1), cx), List.mem_singleton_self _, h1, by omega⟩)
          · obtain ⟨k, hk, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hidx k hk).2
          · obtain ⟨j, hj, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hsidx j hj).2
        exact ⟨fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi),
          fun _ i hi => Or.inl (hR i hi), trivial⟩
  · intro A hA
    rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g36 : σ (.n 36) = gen ^ cx := rfl
    have g45 : σ (.n 45) = gen ^ (cx + 4 * w) := by
      show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
      ring
    have g52 : σ (.n 52) = p * gen ^ (128 * w) * gen ^ (4 * t) := rfl
    have hcl : ∀ k < 4, (σ (.n 52)).limb 0 * gpow k = gpow (idx (4 * (n - 1) + k)) := fun k hk => by
      rw [g52, addr_mul_gen_pow ((isInK_mul_gen_pow_iff _ _).mpr hpK), addr_mul_gen_pow hpK,
        show 128 * w + (4 * t + k) = 4 * (n - 1) + k by omega]
      exact (hidx _ (by omega)).1
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cx + 0, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 1, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 2, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 3, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 0, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 1, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 2, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 3, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨_, hcl 0 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 1 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 2 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 3 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩

/-- The deployed `cld_completeRelAtB`, from `cld_completeRelBS` at `CompModel.deployed`. -/
theorem cld_completeRelB_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (cs : List E) (B86 : E → ℕ) (Bct : ℕ → ℕ) (Bsl6 : ℕ)
    (h86 : TotalLeOn coreProgram fs "__loop86" LoopPre fun a => B86 (a.getD 1 0))
    (hct : ∀ t, t < 32 → TotalLe coreProgram fs ctNames[t]! fun _ => Bct t)
    (hsl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    CompleteRelB fs cert κ "claim_list_digest" (ClPreAt cs) (cldBound fs B86 Bct Bsl6 (cs.length / 4)) := by
  have h := cld_completeRelBS (CM := CompModel.deployed) fs cert hκ cs B86 Bct Bsl6
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeOnB_deployed]; exact h86)
    (fun t ht => by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hct t ht)
    (by rw [show CompModel.deployed.sem = blakeDeployed from rfl, totalLeB_deployed]; exact hsl6)
  rw [show CompModel.deployed.sem = blakeDeployed from rfl, completeRelBS_deployed] at h
  exact fun args rets Lin hpre =>
    h args rets Lin fun rd hl hL => (clPreAtC_deployed cs rd args rets).mpr (hpre rd hl hL)

end
end LeanVM.Guest.B1.Digest
