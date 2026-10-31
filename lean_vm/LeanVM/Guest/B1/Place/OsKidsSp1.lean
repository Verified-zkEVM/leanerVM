/-
  LeanVM.Guest.B1.Place.OsKidsSp1

  open_stacked's residual loops, placed on the honest trace; a callee's words widened.
-/

module

public import LeanVM.Guest.B1.Place.OsLkMem6
public import LeanVM.Guest.B1.Place.ResAt
public import LeanVM.Guest.B1.Whir.BrFin2
public import LeanVM.Guest.Memory.Size

/-!
# The residual loops, placed

* `completeAtD_lin_mono`: a callee complete on the words `Lin` is complete on any layout
  containing them.
* `osLk_fixed`: a memory holding `osLk` holds the fixed buffers' honest words (`FixedMem`).
* `qw_get`, `qpos_all`: the query weights and every decoded position, by level.
* `os_res_mem`: a memory holding `osLk` holds level `l`'s row words and every iteration's meaning.
* **`os_res_completeAtD`**: level `l`'s residual loop (`c.resLoop l`), at its honest arguments
  (`ResCallOk`'s, the pointers `osAtOf c b`), is `CompleteAtD` on `osLk c tr b Lin`;
  **`os_res_completeAtB`**: `CompleteAtB`, by a tree of at most `B` words, `B` bounding the loop's
  valid trees at those arguments (`os_res_completeAtB_of_totalLe`: from its `TotalLe`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A callee's words widened**: complete on `Lin`, complete on any layout containing it. -/
theorem completeAtD_lin_mono {κ : ℕ} {f : String} {Lin Lin' : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert κ f Lin args Out)
    (hsub : ∀ q ∈ Lin, q ∈ Lin') : CompleteAtD fs cert κ f Lin' args Out := fun fp ↦ by
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm ↦ ?_⟩
  obtain ⟨h1, h2⟩ := Main.memL_append.mp hm
  have h3 : MemL rd Lin := fun q hq ↦ h2 q (hsub q hq)
  exact (hr rd hl (Main.memL_append.mpr ⟨h1, h3⟩)).mono fun i ⟨q, hq, hq1, hq2⟩ ↦
    ⟨q, hsub q hq, hq1, hq2⟩

theorem osOwnL_getD_fixed (c : OsCfg) (tr : OsTr) (bp : ℕ → ℕ → E) :
    (osOwnL c tr bp).getD 2 [] = fmsgC c tr ∧ (osOwnL c tr bp).getD 3 [] = rootsC c tr ∧
      (osOwnL c tr bp).getD 4 [] = fchC c tr ∧ (osOwnL c tr bp).getD 5 [] = betasC c tr ∧
      (osOwnL c tr bp).getD 9 [] = oodzC c tr ∧ (osOwnL c tr bp).getD 10 [] = oodC c tr := by
  rw [osOwnL_eq6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The fixed buffers' honest words** on every memory holding `osLk`. -/
theorem osLk_fixed {c : OsCfg} {tr : OsTr} {b : ℕ} {Lin : Layout} {rd : Reader}
    (hm : MemL rd (osLk c tr b Lin)) : FixedMem rd (osAtOf c b).P c tr := by
  have r : ∀ j, j < 11 → j ≠ 8 → ReadsAt rd (osPtrAt c b j) ((osOwnL c tr fun _ _ ↦ 0).getD j []) :=
    fun j hj h8 ↦ osLk_reads hm _ (by omega) h8
  obtain ⟨g2, g3, g4, g5, g9, g10⟩ := osOwnL_getD_fixed c tr fun _ _ ↦ 0
  obtain ⟨-, -, g6, g7, -⟩ := osOwnL_getD_head6 c tr fun _ _ ↦ 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := r 4 (by omega) (by omega); rwa [g4] at this
  · have := r 3 (by omega) (by omega); rwa [g3] at this
  · have := r 5 (by omega) (by omega); rwa [g5] at this
  · have := r 6 (by omega) (by omega); rwa [g6] at this
  · have := r 7 (by omega) (by omega); rwa [g7] at this
  · have := r 9 (by omega) (by omega); rwa [g9] at this
  · have := r 10 (by omega) (by omega); rwa [g10] at this
  · have := r 2 (by omega) (by omega); rwa [g2] at this

section Honest

variable {c : OsCfg} {tr : OsTr}

/-- **Level `i`'s query weights.** -/
theorem qw_get (h : TrFit c tr) (hs : OsSizes c) {rd : Reader} {P : OsPtrs}
    (hm : FixedMem rd P c tr) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).queries) :
    LoadHolds rd P.qw (i * c.maxQ + j) (Wof tr.rs i j) := by
  have hq : (lvAt c i).queries ≤ c.maxQ := hs.q i hi
  have := readsAt_map_range hm.qw (k := i * c.maxQ + j) (by
    have h2 := Nat.mul_le_mul_right c.maxQ (show i + 1 ≤ c.levels.length by omega)
    rw [Nat.add_mul, one_mul] at h2
    omega)
  simp only [show (i * c.maxQ + j) / c.maxQ = i by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp,
    show (i * c.maxQ + j) % c.maxQ = j by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)],
    hj, ↓reduceIte] at this
  rw [Wof, rs_get h hi]
  exact this

/-- **Every decoded position of level `i`.** -/
theorem qpos_all (hs : OsSizes c) {rd : Reader} {P : OsPtrs}
    (hm : FixedMem rd P c tr) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes * (192 / (lvAt c i).depth)) :
    LoadHolds rd P.qpos ((lvAt c i).posOff + j) (posAt c tr i j) := by
  have hpos := hs.pos
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (c.levels.length - 1 - i) i
    (by omega)
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c i).posOff + j) = i := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (i := i)
      (k := (lvAt c i).posOff + j) (by omega) (by
      show (lvAt c i).posOff + j < (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth)
      omega) (c.levels.length - 1 - i) (by omega)
    rwa [show i + 1 + (c.levels.length - 1 - i) = c.levels.length by omega] at this
  have := readsAt_map_range hm.qpos (k := (lvAt c i).posOff + j) (by
    show (lvAt c i).posOff + j < c.posLen
    have : (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤ c.posLen := hend
    omega)
  simp only [hown, Nat.add_sub_cancel_left, hj, ↓reduceIte] at this
  exact this

theorem loadHolds_x2 {rd : Reader} {p : E} {po j k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ po * (gen ^ j) ^ 2) k w ↔ LoadHolds rd p (po + (2 * j + k)) w := by
  rw [← pow_mul, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow, Nat.mul_comm j 2]

theorem loadHolds_x1 {rd : Reader} {p : E} {j k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w := loadHolds_mul_gen_pow _ _ _ _ _

/-- **Level `l`'s residual loop's memory**: every memory holding `osLk` holds the row's `d` words
and every iteration's meaning. -/
theorem os_res_mem (h : TrFit c tr) (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length) (b : ℕ)
    (Lin : Layout) : ∀ rd, MemL rd (osLk c tr b Lin) →
      (∀ s < (lvAt c l).logCols,
        LoadHolds rd (osAtOf c b).BD (l * ligColsCap + s) (finD c tr l s)) ∧
      ∀ j < (lvAt c l).queries / 2, ResIter rd (finD c tr l) (lvAt c l).vanish (lvAt c l).logCols
        (lvAt c l).posOff (l * c.maxQ) (osAtOf c b).P.qpos (osAtOf c b).P.qw ((osAtOf c b).rc l)
        (gen ^ j) := by
  have hq : (lvAt c l).queries ≤ c.maxQ := hs.q l hl
  refine fun rd hm ↦ ⟨fun s hs' ↦ ?_, fun j hj ↦ ?_⟩
  · -- the row's `d` words
    obtain ⟨hBD, -⟩ := osOwnL_getD_fin6 c tr (fun _ _ ↦ 0) hl
    have hr := osLk_reads hm (fun _ _ ↦ 0) (j := osIxBD c) (by unfold osIxBD; omega)
      (by unfold osIxBD; omega)
    rw [hBD] at hr
    have hc : (lvAt c l).logCols ≤ 22 := hs.cols l hl
    have := readsAt_map_range hr (k := l * ligColsCap + s) (by simp only [ligColsCap]; nlinarith)
    simp only [ligColsCap] at this
    simp only [show (l * 22 + s) / 22 = l by omega, show (l * 22 + s) % 22 = s by omega] at this
    exact this
  · -- iteration `j`
    have hfix := osLk_fixed hm
    obtain ⟨-, hRC⟩ := osOwnL_getD_fin6 c tr (fun _ _ ↦ 0) hl
    have hr := osLk_reads hm (fun _ _ ↦ 0) (j := osIxRC c l) (by unfold osIxRC; omega)
      (by unfold osIxRC; omega)
    rw [hRC] at hr
    have hrc : ∀ m ≤ (lvAt c l).queries / 2, LoadHolds rd ((osAtOf c b).rc l) m
        (∑ t ∈ Finset.range (2 * m), Wof tr.rs l t * lvRes (lvAt c l) (finD c tr l) (Pof tr.rs l t)) :=
      fun m hm' ↦ by
        have := readsAt_map_range hr (k := m) (by omega)
        simp only [hm', ↓reduceIte] at this
        exact this
    refine ⟨Pof tr.rs l (2 * j), Pof tr.rs l (2 * j + 1), Wof tr.rs l (2 * j),
      Wof tr.rs l (2 * j + 1),
      ∑ t ∈ Finset.range (2 * j), Wof tr.rs l t * lvRes (lvAt c l) (finD c tr l) (Pof tr.rs l t),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [loadHolds_x2, show 2 * j + 0 = 2 * j by omega, ← posAt_eq h hl (by omega)]
      exact qpos_all hs hfix hl (by
        have := ceilDiv_mul_ge (a := (lvAt c l).queries) (h.lvb l hl).per
        rw [← (h.lvb l hl).squeezes] at this; omega)
    · rw [loadHolds_x2, ← posAt_eq h hl (by omega)]
      exact qpos_all hs hfix hl (by
        have := ceilDiv_mul_ge (a := (lvAt c l).queries) (h.lvb l hl).per
        rw [← (h.lvb l hl).squeezes] at this; omega)
    · rw [loadHolds_x2, show 2 * j + 0 = 2 * j by omega]
      exact qw_get h hs hfix hl (by omega)
    · rw [loadHolds_x2]
      exact qw_get h hs hfix hl (by omega)
    · rw [loadHolds_x1, Nat.add_zero]
      exact hrc j (by omega)
    · rw [loadHolds_x1]
      have := hrc (j + 1) (by omega)
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
        at this
      exact this

/-- **Level `l`'s residual loop, placed**, at its honest arguments. -/
theorem os_res_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c)
    {l : ℕ} (hl : l < c.levels.length) {fn : Fn} (hf : coreProgram.find? (c.resLoop l) = some fn)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody c l (lvAt c l) (c.resLoop l))
    (hne : 1 + gen ^ ((lvAt c l).queries / 2) ≠ 0) (b : ℕ) (Lin : Layout) :
    CompleteAtD fs cert κ (c.resLoop l) (osLk c tr b Lin)
      [1, gen ^ ((lvAt c l).queries / 2), (osAtOf c b).P.qpos, (osAtOf c b).P.qw, (osAtOf c b).BD,
        (osAtOf c b).rc l] (Returns []) := by
  have hst := hF.lv l hl
  have hq2 : 2 ≤ (lvAt c l).queries := hst.q2
  exact resLoop_completeAtD fs cert κ hf c l (lvAt c l) hps hb hst.ml1 hst.posOff hst.wo
    (by omega) hne (os_res_mem h hs hl b Lin)

/-- **Level `l`'s residual loop, placed, by a bounded tree**, at its honest arguments: by a tree of
at most `B` words, `B` bounding the loop's valid trees there (`TotalLe` at the call's arguments;
`os_res_completeAtB_of_totalLe`). -/
theorem os_res_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c)
    {l : ℕ} (hl : l < c.levels.length) {fn : Fn} (hf : coreProgram.find? (c.resLoop l) = some fn)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody c l (lvAt c l) (c.resLoop l))
    (hne : 1 + gen ^ ((lvAt c l).queries / 2) ≠ 0) (b : ℕ) (Lin : Layout) {B : ℕ}
    (hB : ∀ rd (t : Tree), t.name = c.resLoop l →
      t.Valid coreProgram rd [1, gen ^ ((lvAt c l).queries / 2), (osAtOf c b).P.qpos,
        (osAtOf c b).P.qw, (osAtOf c b).BD, (osAtOf c b).rc l] [] →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtB fs cert κ (c.resLoop l) (osLk c tr b Lin)
      [1, gen ^ ((lvAt c l).queries / 2), (osAtOf c b).P.qpos, (osAtOf c b).P.qw, (osAtOf c b).BD,
        (osAtOf c b).rc l] (Returns []) B := by
  have hst := hF.lv l hl
  have hq2 : 2 ≤ (lvAt c l).queries := hst.q2
  exact resLoop_completeAtB fs cert κ hf c l (lvAt c l) hps hb hst.ml1 hst.posOff hst.wo
    (by omega) hne (os_res_mem h hs hl b Lin) hB

end Honest

end
end LeanVM.Guest.B1
