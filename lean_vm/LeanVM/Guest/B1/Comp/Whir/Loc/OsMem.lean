/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsMem

  The buffers' reads over a total hash (`Whir/OsMem.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsMem
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsLay

/-!
# The buffers' reads over a total hash (`Whir/OsMem.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- What a memory holding the buffers reads at their pointers from `b`, the decoders' pointers
`Q`. -/
structure OsBufReadsW (Ht : Bytes → Digest) (rd : Reader) (cfg : OsCfg) (d : OsData) (b : ℕ) (Q : List E) : Prop where
  caps : ReadsAt rd (osPtrAt cfg b 0) (d.capsCW Ht cfg)
  flags : ReadsAt rd (osPtrAt cfg b 1) (d.flagsCW Ht cfg)
  fmsg : ReadsAt rd (osPtrAt cfg b 2) (d.fmsgCW Ht cfg)
  roots : ReadsAt rd (osPtrAt cfg b 3) (d.rootsCW Ht cfg)
  fch : ReadsAt rd (osPtrAt cfg b 4) (d.fchCW Ht cfg)
  betas : ReadsAt rd (osPtrAt cfg b 5) (d.betasCW Ht cfg)
  qw : ReadsAt rd (osPtrAt cfg b 6) (d.qwCW Ht cfg)
  qpos : ReadsAt rd (osPtrAt cfg b 7) (d.qposCW Ht cfg)
  qbp : ReadsAt rd (osPtrAt cfg b 8) Q
  oodz : ReadsAt rd (osPtrAt cfg b 9) (d.oodzCW Ht cfg)
  ood : ReadsAt rd (osPtrAt cfg b 10) (d.oodCW Ht cfg)
  sqz : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * l)) (d.sqzCW Ht cfg l)
  rew : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * l + 1)) (d.rewCW Ht cfg l)
  tch : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length)) (d.tchCW Ht cfg)
  pt : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 1)) (d.ptCW Ht cfg)
  ba : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)) (d.baCW Ht cfg)
  bb : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)) (d.bbCW Ht cfg)
  ich : ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 4)) (d.ichCW Ht cfg)
  chv : ∀ l < cfg.levels.length, ReadsAt rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l)) (d.chvCW Ht cfg l)

/-- **The buffers on a memory holding them.** -/
theorem os_bufReadsC {rd : Reader} {cfg : OsCfg} {d : OsData} {b : ℕ} {Q : List E}
    (hm : MemL rd (bufL b (osSizes cfg) (d.ownQW Ht cfg Q))) : OsBufReadsW Ht rd cfg d b Q := by
  set n := cfg.levels.length with hn
  set A : List (List E) := [d.capsCW Ht cfg, d.flagsCW Ht cfg, d.fmsgCW Ht cfg, d.rootsCW Ht cfg, d.fchCW Ht cfg, d.betasCW Ht cfg,
    d.qwCW Ht cfg, d.qposCW Ht cfg, Q, d.oodzCW Ht cfg, d.oodCW Ht cfg] with hA
  set F : List (List E) := (List.range n).flatMap fun l => [d.sqzCW Ht cfg l, d.rewCW Ht cfg l] with hF
  set T : List (List E) := [d.tchCW Ht cfg, d.ptCW Ht cfg, d.baCW Ht cfg, d.bbCW Ht cfg, d.ichCW Ht cfg] with hT
  set M : List (List E) := (List.range n).map (d.chvCW Ht cfg) with hM
  have lA : A.length = 11 := rfl
  have lF : F.length = 2 * n := by
    simp [hF, List.length_flatMap, List.map_const']; ring
  have lT : T.length = 5 := rfl
  have lM : M.length = n := by simp [hM]
  have hown : d.ownQW Ht cfg Q = A ++ (F ++ (T ++ M)) := by
    simp only [OsData.ownQW, List.append_assoc]; rfl
  have hS := os_length_osSizes cfg
  have hl : (d.ownQW Ht cfg Q).length = (osSizes cfg).length := by
    rw [hown, hS]; simp only [List.length_append, lA, lF, lT, lM]; omega
  have R : ∀ j, j < 11 + 2 * n + 5 + n → ReadsAt rd (osPtrAt cfg b j) ((d.ownQW Ht cfg Q).getD j []) := fun j hj =>
    os_memL_bufL hm hl (by rw [hS]; exact hj)
  have gA : ∀ j < 11, ReadsAt rd (osPtrAt cfg b j) (A.getD j []) := fun j hj => by
    have := R j (by omega)
    rwa [hown, oq_getD_app_lt (by rw [lA]; exact hj)] at this
  have gF : ∀ l < n, ReadsAt rd (osPtrAt cfg b (11 + 2 * l)) (d.sqzCW Ht cfg l) ∧
      ReadsAt rd (osPtrAt cfg b (11 + 2 * l + 1)) (d.rewCW Ht cfg l) := fun l hl' => by
    have h1 := R (11 + 2 * l) (by omega)
    have h2 := R (11 + 2 * l + 1) (by omega)
    have e := os_flatMap_pair_getD (fun i => d.sqzCW Ht cfg i) (fun i => d.rewCW Ht cfg i) [] n l hl'
    rw [hown, ← lA, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)] at h1
    rw [hown, ← lA, Nat.add_assoc, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)] at h2
    exact ⟨by rw [← e.1]; exact h1, by rw [← e.2]; exact h2⟩
  have gT : ∀ k < 5, ReadsAt rd (osPtrAt cfg b (11 + 2 * n + k)) (T.getD k []) := fun k hk => by
    have := R (11 + 2 * n + k) (by omega)
    have e : (d.ownQW Ht cfg Q).getD (11 + 2 * n + k) [] = T.getD k [] := by
      rw [hown, ← lA, ← lF, Nat.add_assoc, os_getD_skip, os_getD_skip, oq_getD_app_lt (by rw [lT]; exact hk)]
    rw [e] at this
    exact this
  have gM : ∀ l < n, ReadsAt rd (osPtrAt cfg b (11 + 2 * n + 5 + l)) (d.chvCW Ht cfg l) := fun l hl' => by
    have := R (11 + 2 * n + 5 + l) (by omega)
    have e : (d.ownQW Ht cfg Q).getD (11 + 2 * n + 5 + l) [] = d.chvCW Ht cfg l := by
      rw [hown, ← lA, ← lF, ← lT, Nat.add_assoc, Nat.add_assoc, os_getD_skip, os_getD_skip, os_getD_skip]
      simp [hM, List.getD_eq_getElem?_getD, hl']
    rw [e] at this
    exact this
  exact ⟨gA 0 (by omega), gA 1 (by omega), gA 2 (by omega), gA 3 (by omega), gA 4 (by omega), gA 5 (by omega),
    gA 6 (by omega), gA 7 (by omega), gA 8 (by omega), gA 9 (by omega), gA 10 (by omega),
    fun l hl' => (gF l hl').1, fun l hl' => (gF l hl').2, gT 0 (by omega), gT 1 (by omega), gT 2 (by omega),
    gT 3 (by omega), gT 4 (by omega), gM⟩

/-- Level `l`'s squeeze run's buffer's words. -/
theorem os_ownQ_getD_sqzC {cfg : OsCfg} {d : OsData} {Q : List E} {l : ℕ} (hl : l < cfg.levels.length) :
    (d.ownQW Ht cfg Q).getD (11 + 2 * l) [] = d.sqzCW Ht cfg l := by
  have lA : ([d.capsCW Ht cfg, d.flagsCW Ht cfg, d.fmsgCW Ht cfg, d.rootsCW Ht cfg, d.fchCW Ht cfg, d.betasCW Ht cfg, d.qwCW Ht cfg, d.qposCW Ht cfg,
      Q, d.oodzCW Ht cfg, d.oodCW Ht cfg] : List (List E)).length = 11 := rfl
  have lF : ((List.range cfg.levels.length).flatMap fun l => [d.sqzCW Ht cfg l, d.rewCW Ht cfg l]).length =
      2 * cfg.levels.length := by simp [List.length_flatMap, List.map_const']; ring
  unfold OsData.ownQW
  simp only [List.append_assoc]
  rw [← lA, os_getD_skip, oq_getD_app_lt (by rw [lF]; omega)]
  exact (os_flatMap_pair_getD _ _ _ _ l hl).1

end
end LeanVM.Guest.B1
