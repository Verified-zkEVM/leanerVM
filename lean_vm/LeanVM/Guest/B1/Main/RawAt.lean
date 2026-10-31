/-
  LeanVM.Guest.B1.Main.RawAt

  `main`'s raw-signature loops `__loop2` (leanXMSS) and `__loop3` (leanSPHINCS) in the uniform
  placed form (`CompleteAtD`), over the raw signatures' honest data.
-/

module

public import LeanVM.Guest.B1.Main.RawCChk
public import LeanVM.Guest.Lift.Sig
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Digest.CoverComplete

/-!
# The raw-signature loops, placed

`RawXData nrx X cv tb Lin`: per raw leanXMSS signature `i < nrx`, its slot below `X` (the
leanXMSS region's size), the public key, message and signature (verifying), and on every memory
defined below `2^16` holding the caller's words `Lin`: the coverage word at `cv + slot i` is
`g^i`, the claim's four cells at `tb + 4·slot i`; those words are among `Lin`'s.
`RawSData nrs Y X nrx cv tb bb Lin`: per raw leanSPHINCS signature `j < nrs`, its slot below `Y`,
the coverage word at `cv + X + slot j` is `g^(nrx + j)`, the claim at `tb + 4·slot j`, the byte
table at `bb`.

Both loops place nothing; on such a memory each runs by a tree loading from `Lin` only
(`rawX_relIn`, `rawS_relIn`, by induction from the last iteration, `relIn_of_walk` and the
verifiers' `…_relIn`), so they are `CompleteAtD` (`completeAtD_of_relIn`): `rawX_completeAt`,
`rawS_completeAt`, from every counter below the count, with the arguments `main` passes.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul)

@[expose] public section

/-! ## The data -/

/-- **The raw leanXMSS signatures' honest data.** -/
structure RawXData (nrx X cv tb : ℕ) (Lin : Layout) where
  slot : ℕ → ℕ
  pk : ℕ → HashSig.PublicKey
  msg : ℕ → HashSig.Message
  sig : ℕ → LeanXmss.Signature
  slot_lt : ∀ i < nrx, slot i < X
  verify : ∀ i < nrx, Node.xmssVerify (pk i) (msg i) (sig i) = true
  cover : ∀ rd, LowDef 16 rd → MemL rd Lin → ∀ i < nrx, LoadHolds rd (gen ^ cv) (slot i) (gen ^ i)
  claim : ∀ rd, LowDef 16 rd → MemL rd Lin → ∀ i < nrx,
    Sig.ClaimAt rd (gen ^ (tb + 4 * slot i)) (Sig.cellOf128 (pk i).root)
      (Sig.cellOf128 (pk i).parameter) (Sig.cellOf128 ((msg i).extractLsb' 0 128))
      (Sig.cellOf128 ((msg i).extractLsb' 128 128))
  regCover : ∀ i < nrx, RegionL Lin (cv + slot i)
  regClaim : ∀ i < nrx, ∀ k < 4, RegionL Lin (tb + 4 * slot i + k)

/-- **The raw leanSPHINCS signatures' honest data.** -/
structure RawSData (nrs Y X nrx cv tb bb : ℕ) (Lin : Layout) where
  slot : ℕ → ℕ
  pk : ℕ → Sphincs.PublicKey
  msg : ℕ → Sphincs.Message
  sig : ℕ → Sphincs.Signature
  slot_lt : ∀ j < nrs, slot j < Y
  verify : ∀ j < nrs, Node.sphincsVerify (pk j) (msg j) (sig j) = true
  cover : ∀ rd, LowDef 16 rd → MemL rd Lin → ∀ j < nrs,
    LoadHolds rd (gen ^ cv) (X + slot j) (gen ^ (nrx + j))
  claim : ∀ rd, LowDef 16 rd → MemL rd Lin → ∀ j < nrs,
    Sig.ClaimAt rd (gen ^ (tb + 4 * slot j)) (Sig.cellOf128 (pk j).root)
      (Sig.cellOf128 (pk j).parameter) (Sig.cellOf128 ((msg j).extractLsb' 0 128))
      (Sig.cellOf128 ((msg j).extractLsb' 128 128))
  bytes : ∀ rd, LowDef 16 rd → MemL rd Lin → Sig.ByteBits rd (gen ^ bb)
  regCover : ∀ j < nrs, RegionL Lin (cv + (X + slot j))
  regClaim : ∀ j < nrs, ∀ k < 4, RegionL Lin (tb + 4 * slot j + k)
  regBytes : ∀ v < 256, RegionL Lin (bb + v)

/-! ## Shared -/

theorem l3Pre_straight : l3Pre.all Main.Stmt.straight = true := rfl
theorem l4Pre_straight : l4Pre.all Main.Stmt.straight = true := rfl

theorem gen4 (s : ℕ) : gen ^ s * gen ^ s * (gen ^ s * gen ^ s) = gen ^ (4 * s) := by
  simp only [← pow_add]; congr 1; ring

theorem low_read {rd : Reader} (hl : LowDef 16 rd) {e : ℕ} (he : e < 2 ^ 16) :
    LoadHolds rd (gen ^ e) 0 ((rd (gpow e)).getD 0) := by
  rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl he

theorem guard_taken {i n : ℕ} (hn : n < 2 ^ 34) (hi : i + 1 ≤ n) :
    decide (gen ^ i * word 2 0 0 + gen ^ n ≠ 0) = decide (i + 1 ≠ n) := by
  rw [word_gen, gen_pow_mul_gen]
  refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h ?_⟩
  exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)

/-! ## `__loop2` -/

/-- `__loop2`'s valuation at the counter `g^i`. -/
noncomputable def l3σ (rd : Reader) (i nrx X cv tb s : ℕ) : Val :=
  Val.ofArgs [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb, gen ^ s, ginvW, gen ^ X * ginvW,
    gen ^ (X - 1 - s), (rd (gpow s)).getD 0, (rd (gpow (X - 1 - s))).getD 0, gen ^ cv * gen ^ s,
    gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), word 2 0 0, gen ^ i * word 2 0 0,
    gen ^ i * word 2 0 0 + gen ^ nrx, word 2 0 0, gen ^ i * word 2 0 0]

set_option maxRecDepth 20000 in
/-- **`__loop2` loads from the caller's words**, from every counter below the count. -/
theorem rawX_relIn (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 16) (hnrx : nrx < 2 ^ 34) {rd : Reader}
    (hl : LowDef 16 rd) (hL : MemL rd Lin) :
    ∀ i < nrx, coreProgram.RelIn rd (RegionL Lin) "__loop2"
      [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] [] := by
  have key : ∀ t i, i + 1 + t = nrx → coreProgram.RelIn rd (RegionL Lin) "__loop2"
      [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] [] := by
    intro t
    induction t with
    | zero => ?_
    | succ t ih => ?_
    all_goals
      intro i hi
      have hs := D.slot_lt i (by omega)
      set s := D.slot i with hsd
      set σ := l3σ rd i nrx X cv tb s with hσ
      have hw := Main.walk_straight σ [] l3Pre l3Pre_straight
      rw [← l3_body] at hw
      obtain ⟨-, -, -, hpc⟩ := Main.straight_parts σ _ l3Pre_straight
      refine relIn_of_walk coreProgram_wf l3_find (by rw [l3_params]; rfl) hw rfl
        (slEvs_holds fun st hst => ?_) (fun A hA => ?_) (fun c hcm ht => ?_)
      · simp only [l3Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
        rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
        all_goals simp only [SlOk, Atom.Holds, hσ, l3σ, ofArgs_n, List.getD_cons_succ,
          List.getD_cons_zero]
        · refine ⟨low_read hl (by omega), ?_, low_read hl (by omega)⟩
          rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
        · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact D.cover rd hl hL i (by omega)
        · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
      · rw [B1.loadAddrs_straight σ _ l3Pre_straight,
          show l3Pre.filterMap B1.Stmt.loadS = [(.n 11, 0)] from rfl] at hA
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA
        subst hA
        refine ⟨cv + s, ?_, D.regCover i (by omega)⟩
        show (gen ^ cv * gen ^ s).limb 0 * gpow 0 = _
        rw [← pow_add, limb0_gen_pow_mul]; rfl
      · rw [hpc, show l3Pre.filterMap Main.Stmt.callS = [(none, "verify_lean_xmss", [.n 14], []),
          (some (.n 17), "__loop2", [.n 19, .n 1, .n 2, .n 3, .n 4], [])] from rfl] at hcm
        simp only [List.map_cons, List.map_nil, Main.mkCall, List.mem_cons, List.not_mem_nil,
          or_false] at hcm
        rcases hcm with rfl | rfl
        · show coreProgram.RelIn rd (RegionL Lin) "verify_lean_xmss"
            [gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s))] []
          rw [gen4, ← pow_add]
          exact Lift.verify_lean_xmss_relIn hc (fun j hj => hl j (by omega))
            (D.claim rd hl hL i (by omega)) (D.verify i (by omega))
            (fun k hk => ⟨tb + 4 * s + k, limb0_gen_pow_mul _ _, D.regClaim i (by omega) k hk⟩)
        · simp only [decide_eq_true_eq] at ht
          change gen ^ i * word 2 0 0 + gen ^ nrx ≠ 0 at ht
          have ht' := of_decide_eq_true ((guard_taken hnrx (by omega)).symm.trans
            (decide_eq_true ht))
          show coreProgram.RelIn rd (RegionL Lin) "__loop2"
            [gen ^ i * word 2 0 0, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] []
          rw [word_gen, gen_pow_mul_gen]
          first
            | exact absurd hi (by omega)
            | exact ih (i + 1) (by omega)
  intro i hi
  exact key (nrx - i - 1) i (by omega)

/-- **`__loop2` is complete, placed**, from every counter below the count. -/
theorem rawX_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hc : Sig.verify_lean_xmss_complete_Spec) {nrx X cv tb : ℕ} {Lin : Layout}
    (D : RawXData nrx X cv tb Lin) (hX : X ≤ 2 ^ 16) (hnrx : nrx < 2 ^ 34) :
    ∀ i < nrx, CompleteAtD fs cert 16 "__loop2" Lin
      [gen ^ i, gen ^ nrx, gen ^ X, gen ^ cv, gen ^ tb] (Returns []) := fun i hi =>
  Lift.completeAtD_of_relIn raw3_pure (by simp) fun rd hl hL => rawX_relIn hc D hX hnrx hl hL i hi

/-! ## `__loop3` -/

/-- `__loop3`'s valuation at the counter `g^j`. -/
noncomputable def l4σ (rd : Reader) (j nrs Y cv X nrx tb bb s : ℕ) : Val :=
  Val.ofArgs [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb, gen ^ bb,
    gen ^ s, ginvW, gen ^ Y * ginvW, gen ^ (Y - 1 - s), (rd (gpow s)).getD 0,
    (rd (gpow (Y - 1 - s))).getD 0, gen ^ nrx * gen ^ j, gen ^ X * gen ^ s,
    gen ^ cv * (gen ^ X * gen ^ s), gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), word 2 0 0, gen ^ j * word 2 0 0,
    gen ^ j * word 2 0 0 + gen ^ nrs, word 2 0 0, gen ^ j * word 2 0 0]

set_option maxRecDepth 20000 in
/-- **`__loop3` loads from the caller's words**, from every counter below the count. -/
theorem rawS_relIn (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin)
    (hY : Y ≤ 2 ^ 16) (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 16 rd) (hL : MemL rd Lin) :
    ∀ j < nrs, coreProgram.RelIn rd (RegionL Lin) "__loop3"
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb, gen ^ bb] [] := by
  have key : ∀ t j, j + 1 + t = nrs → coreProgram.RelIn rd (RegionL Lin) "__loop3"
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb, gen ^ bb] [] := by
    intro t
    induction t with
    | zero => ?_
    | succ t ih => ?_
    all_goals
      intro j hj
      have hs := D.slot_lt j (by omega)
      set s := D.slot j with hsd
      set σ := l4σ rd j nrs Y cv X nrx tb bb s with hσ
      have hw := Main.walk_straight σ [] l4Pre l4Pre_straight
      rw [← l4_body] at hw
      obtain ⟨-, -, -, hpc⟩ := Main.straight_parts σ _ l4Pre_straight
      refine relIn_of_walk coreProgram_wf l4_find (by rw [l4_params]; rfl) hw rfl
        (slEvs_holds fun st hst => ?_) (fun A hA => ?_) (fun c hcm ht => ?_)
      · simp only [l4Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
        rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp only [SlOk, Atom.Holds, hσ, l4σ, ofArgs_n, List.getD_cons_succ,
          List.getD_cons_zero]
        · refine ⟨low_read hl (by omega), ?_, low_read hl (by omega)⟩
          rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
        · rw [show gen ^ cv * (gen ^ X * gen ^ s) = gen ^ cv * gen ^ (X + s) by rw [← pow_add],
            show gen ^ nrx * gen ^ j = gen ^ (nrx + j) by rw [← pow_add], loadHolds_mul_gen_pow,
            Nat.add_zero]
          exact D.cover rd hl hL j (by omega)
        · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
      · rw [B1.loadAddrs_straight σ _ l4Pre_straight,
          show l4Pre.filterMap B1.Stmt.loadS = [(.n 16, 0)] from rfl] at hA
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA
        subst hA
        refine ⟨cv + (X + s), ?_, D.regCover j (by omega)⟩
        show (gen ^ cv * (gen ^ X * gen ^ s)).limb 0 * gpow 0 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; rfl
      · rw [hpc, show l4Pre.filterMap Main.Stmt.callS =
          [(none, "verify_sig_lean_sphincs", [.n 19, .n 7], []),
          (some (.n 22), "__loop3", [.n 24, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [])]
          from rfl] at hcm
        simp only [List.map_cons, List.map_nil, Main.mkCall, List.mem_cons, List.not_mem_nil,
          or_false] at hcm
        rcases hcm with rfl | rfl
        · show coreProgram.RelIn rd (RegionL Lin) "verify_sig_lean_sphincs"
            [gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen ^ bb] []
          rw [gen4, ← pow_add]
          exact Lift.verify_sig_lean_sphincs_relIn hc (fun i hi => hl i (by omega))
            (D.bytes rd hl hL) (D.claim rd hl hL j (by omega)) (D.verify j (by omega))
            (fun k hk => ⟨tb + 4 * s + k, limb0_gen_pow_mul _ _, D.regClaim j (by omega) k hk⟩)
            (fun v hv => ⟨bb + v, limb0_gen_pow_mul _ _, D.regBytes v hv⟩)
        · simp only [decide_eq_true_eq] at ht
          change gen ^ j * word 2 0 0 + gen ^ nrs ≠ 0 at ht
          have ht' := of_decide_eq_true ((guard_taken hnrs (by omega)).symm.trans
            (decide_eq_true ht))
          show coreProgram.RelIn rd (RegionL Lin) "__loop3"
            [gen ^ j * word 2 0 0, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb,
              gen ^ bb] []
          rw [word_gen, gen_pow_mul_gen]
          first
            | exact absurd hj (by omega)
            | exact ih (j + 1) (by omega)
  intro j hj
  exact key (nrs - j - 1) j (by omega)

/-- **`__loop3` is complete, placed**, from every counter below the count. -/
theorem rawS_completeAt (fs : String → ℕ) (cert : String → V → ℕ)
    (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) {nrs Y X nrx cv tb bb : ℕ}
    {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 16) (hnrs : nrs < 2 ^ 34) :
    ∀ j < nrs, CompleteAtD fs cert 16 "__loop3" Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ cv, gen ^ X, gen ^ nrx, gen ^ tb, gen ^ bb]
      (Returns []) := fun j hj =>
  Lift.completeAtD_of_relIn raw4_pure (by simp) fun rd hl hL =>
    rawS_relIn hc D hY hnrs hl hL j hj

end
end LeanVM.Guest.B1.Main
