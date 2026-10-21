/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsRootDec

  `open_stacked`'s decoder at its node: level by level, the queries' calls, the openings chained.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsDecLv

/-!
# The root's decoding, level by level

`osLevelsOs_congr`: the root's decoder reads only the queries calls' values (`osLvsReads`).
`osLevelsOs_range`, `osLvsKOf_getElem`: the levels' decodings and frames at the levels' states
(`osStAt`). `osLvKOf_qcall`, `osLvKOf_capcall`: a level's queries and cap calls among its later
calls. `osp_flatten`: the levels' openings, chained, are the run's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The values the root's decoder reads: each level's queries call's argument and return values. -/
def osLvsReads (cfg : OsCfg) : ℕ → List OsLvl → OsSt → List V
  | _, [], _ => []
  | lvl, lv :: rest, s => (osQCall cfg lv lvl (osLevelQState cfg lvl lv s)).1 ++
      [.n (osQCall cfg lv lvl (osLevelQState cfg lvl lv s)).2] ++ osLvsReads cfg (lvl + 1) rest (osLevel cfg lvl lv s).2

/-- **The root's decoder reads only the queries calls' values.** -/
theorem osLevelsOs_congr (cfg : OsCfg) {σ σ' : Val} {wq : ℕ → List E → List E → List Opening} :
    ∀ (lvl : ℕ) (Ls : List OsLvl) (s : OsSt), (∀ v ∈ osLvsReads cfg lvl Ls s, σ' v = σ v) →
      osLevelsOs cfg lvl Ls s σ' wq = osLevelsOs cfg lvl Ls s σ wq
  | _, [], _, _ => rfl
  | lvl, lv :: rest, s, h => by
    simp only [osLevelsOs, osLevelOs, osQueriesOs]
    rw [osLevelsOs_congr cfg (lvl + 1) rest _ fun v hv => h v (by simp only [osLvsReads]; simp [hv])]
    congr 2
    · exact List.map_congr_left fun v hv => h v (by simp only [osLvsReads]; simp [hv])
    · rw [h _ (by simp [osLvsReads])]

/-- The levels' states: from `s` at level `lvl`, after `i` levels. -/
def osStAt (cfg : OsCfg) : ℕ → OsSt → ℕ → OsSt
  | _, s, 0 => s
  | lvl, s, i + 1 => osStAt cfg (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) s).2 i

theorem osLvsKOf_length (cfg : OsCfg) (σ : Val) : ∀ n lvl s, (osLvsKOf cfg σ lvl s n).length = n
  | 0, _, _ => rfl
  | n + 1, lvl, s => by simp [osLvsKOf, osLvsKOf_length cfg σ n]

/-- **The levels' frames at their states.** -/
theorem osLvsKOf_getElem (cfg : OsCfg) (σ : Val) : ∀ (n lvl : ℕ) (s : OsSt) (i : ℕ)
    (h : i < (osLvsKOf cfg σ lvl s n).length),
    (osLvsKOf cfg σ lvl s n)[i] = osLvKOf cfg σ (lvl + i) (osStAt cfg lvl s i)
  | 0, _, _, _, h => absurd h (by simp [osLvsKOf])
  | n + 1, lvl, s, 0, _ => by simp [osLvsKOf, osStAt]
  | n + 1, lvl, s, i + 1, h => by
    simp only [osLvsKOf, List.getElem_cons_succ]
    rw [osLvsKOf_getElem cfg σ n (lvl + 1) _ i (by simpa [osLvsKOf] using h), osStAt,
      show lvl + 1 + i = lvl + (i + 1) by omega]

/-- **The root's decoding, level by level.** -/
theorem osLevelsOs_range (cfg : OsCfg) (σ : Val) (wq : ℕ → List E → List E → List Opening) :
    ∀ (n lvl : ℕ) (s : OsSt), lvl + n = cfg.levels.length →
      osLevelsOs cfg lvl (cfg.levels.drop lvl) s σ wq =
        (List.range n).flatMap fun i => osLevelOs cfg (lvl + i) (cfg.lv (lvl + i)) (osStAt cfg lvl s i) σ (wq (lvl + i))
  | 0, lvl, s, h => by
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  | n + 1, lvl, s, h => by
    have hlt : lvl < cfg.levels.length := by omega
    have hdrop : cfg.levels.drop lvl = cfg.lv lvl :: cfg.levels.drop (lvl + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [OsCfg.lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [hdrop, osLevelsOs, osLevelsOs_range cfg σ wq n (lvl + 1) _ (by omega), List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, osStAt]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show lvl + 1 + i = lvl + (i + 1) by omega]

/-- **A level's queries call** among its later calls. -/
theorem osLvKOf_qcall (cfg : OsCfg) (σ : Val) (lvl : ℕ) (s : OsSt) :
    (⟨(cfg.lv lvl).queriesFn, (osQCall cfg (cfg.lv lvl) lvl (osLevelQState cfg lvl (cfg.lv lvl) s)).1,
      [.n (osQCall cfg (cfg.lv lvl) lvl (osLevelQState cfg lvl (cfg.lv lvl) s)).2], true⟩ : Call) ∈
      (osLvKOf cfg σ lvl s).B := by
  refine List.mem_map.mpr ⟨(none, (cfg.lv lvl).queriesFn,
    (osQCall cfg (cfg.lv lvl) lvl (osLevelQState cfg lvl (cfg.lv lvl) s)).1,
    [.n (osQCall cfg (cfg.lv lvl) lvl (osLevelQState cfg lvl (cfg.lv lvl) s)).2]),
    List.mem_filterMap.mpr ⟨.call _ _ _, ?_, rfl⟩, rfl⟩
  simp only [osLvRestB, osLvQ, osQueries, osQCall, osLevelQState, osLvSq, osLvG, osLvM, osLvF, List.mem_append,
    List.mem_cons]
  simp

/-- A level's cap call's argument and return values (`osQueries`'). -/
def osCapCallV (lv : OsLvl) (s : OsSt) : List V × List V :=
  let k := s.k
  let p := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) p.2.2
  let fp := osMat osFlags lv.capOff cp.2.2
  ([.n cp.2.1, .n fp.2.1], [.n fp.2.2, .n (fp.2.2 + 1)])

/-- **A level's cap call** among its later calls. -/
theorem osLvKOf_capcall (cfg : OsCfg) (σ : Val) (lvl : ℕ) (s : OsSt) :
    (⟨(cfg.lv lvl).verifyCap, (osCapCallV (cfg.lv lvl) (osLevelQState cfg lvl (cfg.lv lvl) s)).1,
      (osCapCallV (cfg.lv lvl) (osLevelQState cfg lvl (cfg.lv lvl) s)).2, true⟩ : Call) ∈
      (osLvKOf cfg σ lvl s).B := by
  refine List.mem_map.mpr ⟨(none, (cfg.lv lvl).verifyCap,
    (osCapCallV (cfg.lv lvl) (osLevelQState cfg lvl (cfg.lv lvl) s)).1,
    (osCapCallV (cfg.lv lvl) (osLevelQState cfg lvl (cfg.lv lvl) s)).2),
    List.mem_filterMap.mpr ⟨.call _ _ _, ?_, rfl⟩, rfl⟩
  simp only [osLvRestB, osLvQ, osQueries, osCapCallV, osLevelQState, osLvSq, osLvG, osLvM, osLvF, List.mem_append,
    List.mem_cons]
  simp

/-- **The levels' openings, chained, are the run's**: each level's openings its queries' followed
by the next level's, the last leaving none. -/
theorem osp_flatten (Ls : List OsLvP) (q : ℕ → ℕ) (n : ℕ)
    (hsplit : ∀ i < n, (Ls.getD i default).osp = (Ls.getD i default).osp.take (q i) ++ (Ls.getD i default).H.osq)
    (hnext : ∀ i, i + 1 < n → (Ls.getD (i + 1) default).osp = (Ls.getD i default).H.osq)
    (hlast : (Ls.getD (n - 1) default).H.osq = []) (hn : 1 ≤ n) :
    (Ls.getD 0 default).osp = (List.range n).flatMap fun i => (Ls.getD i default).osp.take (q i) := by
  have key : ∀ m, m + 1 ≤ n → (Ls.getD (n - 1 - m) default).osp =
      (List.range (m + 1)).flatMap fun i => (Ls.getD (n - 1 - m + i) default).osp.take (q (n - 1 - m + i)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Nat.zero_add, List.range_one, List.flatMap_singleton, Nat.add_zero]
      conv_lhs => rw [hsplit (n - 1) (by omega), hlast, List.append_nil]
    | succ m ih =>
      intro hm
      have e := ih (by omega)
      conv_lhs => rw [hsplit (n - 1 - (m + 1)) (by omega), ← hnext _ (by omega),
        show n - 1 - (m + 1) + 1 = n - 1 - m by omega, e]
      conv_rhs => rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      refine List.flatMap_congr fun i _ => ?_
      rw [show n - 1 - (m + 1) + (i + 1) = n - 1 - m + i by omega]
  have := key (n - 1) (by omega)
  rw [show n - 1 - (n - 1) = 0 by omega, show n - 1 + 1 = n by omega] at this
  simpa using this

/-- **A value the root's decoder reads is a level's queries call's.** -/
theorem osLvsReads_mem (cfg : OsCfg) : ∀ (n lvl : ℕ) (s : OsSt), lvl + n = cfg.levels.length →
    ∀ v ∈ osLvsReads cfg lvl (cfg.levels.drop lvl) s, ∃ i < n,
      v ∈ (osQCall cfg (cfg.lv (lvl + i)) (lvl + i) (osLevelQState cfg (lvl + i) (cfg.lv (lvl + i)) (osStAt cfg lvl s i))).1 ++
        [.n (osQCall cfg (cfg.lv (lvl + i)) (lvl + i) (osLevelQState cfg (lvl + i) (cfg.lv (lvl + i))
          (osStAt cfg lvl s i))).2]
  | 0, lvl, s, h, v, hv => by
    rw [List.drop_eq_nil_of_le (by omega)] at hv; simp [osLvsReads] at hv
  | n + 1, lvl, s, h, v, hv => by
    have hlt : lvl < cfg.levels.length := by omega
    have hdrop : cfg.levels.drop lvl = cfg.lv lvl :: cfg.levels.drop (lvl + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [OsCfg.lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [hdrop, osLvsReads, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ⟨0, by omega, by simpa [osStAt] using hv⟩
    · obtain ⟨i, hi, hv⟩ := osLvsReads_mem cfg n (lvl + 1) _ (by omega) v hv
      refine ⟨i + 1, by omega, ?_⟩
      rw [show lvl + (i + 1) = lvl + 1 + i by omega, osStAt]
      exact hv

/-- **An entered call's values are named** by the path. -/
theorem mem_named_call {params : List V} {es : List Memory.Ev} {vs : List V} {c : Call} (hc : c ∈ calls es)
    (ht : c.taken = true) {v : V} (hv : v ∈ c.args ++ c.rets) : v ∈ B2C.namedOf params es vs := by
  obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, ?_⟩))
  match e, hce with
  | .call f args rets, hce =>
    simp only [Memory.Ev.call?, Option.some.injEq] at hce
    subst hce
    simpa [Memory.Ev.uses] using hv
  | .skip f args, hce =>
    simp only [Memory.Ev.call?, Option.some.injEq] at hce
    subst hce
    simp at ht

theorem osLvsListW_getD_osp (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) :
    ∀ (Hs : List OsLvH) lvl cv p w osp roots, Hs ≠ [] →
      ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getD 0 default).osp = osp
  | [], _, _, _, _, _, _, h => absurd rfl h
  | _ :: _, _, _, _, _, _, _, _ => rfl

theorem osLvsListW_getD_succ (Ht : Bytes → Digest) (cfg : OsCfg) (xs : List E) :
    ∀ (Hs : List OsLvH) lvl cv p w osp roots i, i + 1 < Hs.length →
      ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getD (i + 1) default).osp =
        ((osLvsListW Ht cfg xs lvl cv p w osp roots Hs).getD i default).H.osq
  | [], _, _, _, _, _, _, _, h => absurd h (by simp)
  | [_], _, _, _, _, _, _, _, h => absurd h (by simp)
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, 0, _ => rfl
  | H :: H' :: Hs, lvl, cv, p, w, osp, roots, i + 1, h => by
    have := osLvsListW_getD_succ Ht cfg xs (H' :: Hs) (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
      (osHWEndW Ht cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) i (by simp at h ⊢; omega)
    rw [osLvsListW, List.getD_cons_succ, List.getD_cons_succ]
    exact this

end
end LeanVM.Guest.B1
