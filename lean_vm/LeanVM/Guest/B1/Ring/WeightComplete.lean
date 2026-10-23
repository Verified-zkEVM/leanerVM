/-
  LeanVM.Guest.B1.Ring.WeightComplete

  `ring_switch_weight` is complete in the uniform placed form (`CompleteAtD`): its chain at the
  bump allocator's position, row `0` its ones and row `⌈n/2⌉` `rs_eq_run`'s.
-/

module

public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Ring.TargetComplete
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `ring_switch_weight`, placed (TRIAGE G #66)

On the caller's words — `n < 64` coordinates `zs` at `g^bz`, `ps` (the point's `1 + r'`) at `g^bp`,
the 64 coefficients `cs` at `g^bc` — `ring_switch_weight` is complete at every frame pointer
(`rsw_completeAt`): its chain (`HeapBuf` of `64(n+1)` words, by `allocDyn`) holds the honest rows
`rswChain` (row `0` ones, row `h ≥ 1` `rs_eq_run`'s), `rs_eq_run` (pure, no range check) is
complete by `completeAt_of_rel_pureD` from its meaning (B1-a's `rs_eq_run_holds`), and it returns
`ringWeight zs (ps.map (1 + ·)) cs` (`ringWeight_eq`, `rwProd_eq_ringRow`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The honest chain -/

/-- The chain's last row: `⌈n/2⌉`. -/
def rswH (count : ℕ) : ℕ := (count + 1) / 2

/-- **The honest chain**: row `0` ones, row `h ≥ 1` the products over the first `min(2h, n)`
coordinates (`rs_eq_run`'s rows), up to row `⌈n/2⌉`. -/
def rswChain (zs ps : List E) (count : ℕ) : List E :=
  (List.range (64 * (rswH count + 1))).map fun t ↦
    if t / 64 = 0 then 1
    else ringRow 1 (zs.take (min (2 * (t / 64)) count)) (ps.take (min (2 * (t / 64)) count)) (t % 64)

theorem rswChain_length (zs ps : List E) (count : ℕ) :
    (rswChain zs ps count).length = 64 * (rswH count + 1) := by simp [rswChain]

theorem rswChain_get (zs ps : List E) (count : ℕ) {t : ℕ} (ht : t < (rswChain zs ps count).length) :
    (rswChain zs ps count)[t] = if t / 64 = 0 then 1
      else ringRow 1 (zs.take (min (2 * (t / 64)) count)) (ps.take (min (2 * (t / 64)) count))
        (t % 64) := by
  simp [rswChain]

theorem rswChain_le (zs ps : List E) (count : ℕ) :
    (rswChain zs ps count).length ≤ 64 * (count + 1) := by
  rw [rswChain_length, rswH]
  rcases Nat.eq_zero_or_pos count with rfl | h
  · simp
  · exact Nat.mul_le_mul_left _ (by omega)

/-- The chain read through `g^b`. -/
theorem rswChain_load {rd : Reader} {zs ps : List E} {count b : ℕ}
    (h : ReadsAt rd (ofK (gpow b)) (rswChain zs ps count)) {t : ℕ}
    (ht : t < 64 * (rswH count + 1)) :
    LoadHolds rd (ofK (gpow b)) t (if t / 64 = 0 then 1
      else ringRow 1 (zs.take (min (2 * (t / 64)) count)) (ps.take (min (2 * (t / 64)) count))
        (t % 64)) := by
  have := h t (by rw [rswChain_length]; exact ht)
  rwa [rswChain_get] at this

/-! ## `rs_eq_run`, placed -/

theorem rs_pure : coreProgram.PureIn ["rs_eq_run", "__loop6"] := by
  intro g hg fn hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [Program.find?_of_indexOf? (j := 5) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel
  · rw [Program.find?_of_indexOf? (j := 79) (by decide +kernel) rfl, Option.some.injEq] at hf
    subst hf; decide +kernel

/-- `rs_eq_run`'s words: the chain, the coordinates, the point. -/
def rsLin (bb bz bp count : ℕ) (zs ps : List E) : Main.Layout :=
  [(bb, rswChain zs ps count), (bz, zs), (bp, ps)]

theorem rs_rel {rd : Reader} {bb bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hL : MemL rd (rsLin bb bz bp count zs ps)) :
    coreProgram.Rel rd "rs_eq_run" [ofK (gpow bb), ofK (gpow bz), ofK (gpow bp), gen ^ count]
      [ofK (gpow bb) * gen ^ (64 * rswH count)] := by
  have hch : ReadsAt rd (ofK (gpow bb)) (rswChain zs ps count) :=
    hL (bb, rswChain zs ps count) (by simp [rsLin])
  have hzs : ReadsAt rd (ofK (gpow bz)) zs := hL (bz, zs) (by simp [rsLin])
  have hps : ReadsAt rd (ofK (gpow bp)) ps := hL (bp, ps) (by simp [rsLin])
  refine (rs_eq_run_holds rd _ _).2 ⟨count, hcount, rfl, zs, ps, List.replicate 64 1, hz, hp,
    by simp, hzs, hps, fun _ k hk ↦ ?_, fun h hh1 hh2 k hk ↦ ?_, rfl⟩
  · simp only [List.length_replicate] at hk
    have := rswChain_load hch (t := k) (by rw [rswH]; omega)
    simp only [List.getElem_replicate]
    rwa [ite_pos' (by omega : k / 64 = 0)] at this
  · have := rswChain_load hch (t := 64 * h + k) (by unfold rswH; omega)
    rw [ite_neg' (by omega : ¬ (64 * h + k) / 64 = 0), show (64 * h + k) / 64 = h by omega,
      show (64 * h + k) % 64 = k by omega] at this
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]
    exact this

/-! ## The body -/

theorem rsw_chk : chk 4 rswT = some 334 := by decide +kernel

theorem rsw_stores : storesOf 4 rswT =
    (List.range 64).map fun k => Atom.load (.n (13 + k)) (.n 12) k := by decide +kernel

/-- `ring_switch_weight`'s statements before its `ret`. -/
def rswPre : List Stmt :=
  [.atom (.const (.n 4) (word 2 0 0)), .atom (.mul (.n 5) (.n 3) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.hint (.allocDyn (.n 12) (.n 11)))] ++
  ((List.range 64).map rswInit).flatten ++ [.call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77]] ++
  ((List.range 64).map rswTerm).flatten ++ [.atom (.copy (.n 333) (.n 332))]

theorem rswT_split : rswT = rswPre ++ [.ret [.n 333]] := by
  simp only [rswT, rswPre, List.append_assoc, List.cons_append, List.nil_append]

theorem rsw_body' : Fn.body Data.core14 = rswPre ++ [.ret [.n 333]] := by
  rw [show Fn.body Data.core14 = rswT from rsw_body, rswT_split]

theorem rsw_flat : rswPre.all Stmt.flat = true := by decide +kernel

theorem rsw_addrs : rswPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem rsw_allocs : rswPre.filterMap Main.Stmt.allocSz = [(.n 12, .inr (.n 11))] := by
  decide +kernel

theorem rsw_not_loop : coreProgram.loop "ring_switch_weight" = false := by decide +kernel

/-- The loads `ring_switch_weight` makes: the coefficients (`2`), the chain's last row (`77`), the
chain's first row (`12`, stores). -/
def rswLoadOk : Atom → Bool
  | .load _ p off => decide (off < 64) &&
      (decide (p = .n 2) || decide (p = .n 77) || decide (p = .n 12))
  | _ => true

theorem rsw_loadOk : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all rswLoadOk = true := by decide +kernel

theorem rsw_canon : canonChk [] ((rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).filter (fun a => decide (a ∉ storesOf 4 rswT))) = true := by
  decide +kernel

theorem rsw_needs : (rswPre.filterMap fun s => match s with
    | .atom a => some a | _ => none).all (fun a => decide (a ∈ storesOf 4 rswT) || !needsSide a ||
      (match a with | .load _ p _ => decide (p = .n 2) || decide (p = .n 77) | _ => false)) = true := by
  decide +kernel

/-! ## The honest valuation -/

/-- The oracle of `ring_switch_weight`'s body: its chain's base, `rs_eq_run`'s return. -/
noncomputable def rswW (bb H : ℕ) : ℕ → E := fun i =>
  if i = 12 then ofK (gpow bb) else if i = 77 then ofK (gpow bb) * gen ^ (64 * H) else 0

/-- The evaluated valuation of `ring_switch_weight`'s body. -/
noncomputable def rswσ (rd : Reader) (args : List E) (bb H : ℕ) : Val :=
  B1.Val.ofArgs (ev rd (rswW bb H) args rswT)

/-- The atoms of `ring_switch_weight`'s statements. -/
def rswA : List Atom := rswPre.filterMap fun s => match s with | .atom a => some a | _ => none

theorem rsw_atom_mem {a : Atom} (h : Stmt.atom a ∈ rswPre) : a ∈ rswA :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem rsw_mem_atom {a : Atom} (h : a ∈ rswA) : Stmt.atom a ∈ rswPre := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem rswInit_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswInit k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rswInit k, ⟨k, hk, rfl⟩, hs⟩)))

theorem rswTerm_mem {k : ℕ} (hk : k < 64) (s : Stmt) (hs : s ∈ rswTerm k) : s ∈ rswPre := by
  simp only [rswPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨rswTerm k, ⟨k, hk, rfl⟩, hs⟩)

set_option maxHeartbeats 1000000 in
/-- **`ring_switch_weight`'s statements hold** on their evaluated valuation, over the honest
chain, the coordinates, the point and the coefficients. -/
theorem rsw_block {rd : Reader} {bz bp bc bb count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64)
    (hzs : ReadsAt rd (ofK (gpow bz)) zs) (hps : ReadsAt rd (ofK (gpow bp)) ps)
    (hcs : ReadsAt rd (ofK (gpow bc)) cs) (hch : ReadsAt rd (ofK (gpow bb)) (rswChain zs ps count)) :
    (∀ a ∈ rswA, a.Holds rd (rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb
      (rswH count))) ∧
    rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb (rswH count) (.n 11) =
      ofK (gpow (64 * (count + 1))) ∧
    rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb (rswH count) (.n 12) =
      ofK (gpow bb) ∧
    rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb (rswH count) (.n 77) =
      ofK (gpow bb) * gen ^ (64 * rswH count) ∧
    rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb (rswH count) (.n 333) =
      ringWeight zs (ps.map (1 + ·)) cs := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rswσ rd [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] bb
      (rswH count) := ⟨_, rfl⟩
  rw [← hσdef]
  set S : List Atom := (List.range 64).map fun k => Atom.load (.n (13 + k)) (.n 12) k with hS
  obtain ⟨-, -, hgs⟩ := ev_spec rd (rswW bb (rswH count)) rswT
    [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count] rsw_chk
  rw [show [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count].length = 4 from rfl,
    rsw_stores, ← hS, ← rswσ, ← hσdef] at hgs
  have hgS : ∀ s ∈ rswPre, GoodS rd S (rswW bb (rswH count)) σ s := fun s hs =>
    hgs s (by rw [rswT_split]; exact List.mem_append_left _ hs)
  have hg : ∀ a ∈ rswA, Good rd S (rswW bb (rswH count)) σ a := fun a ha => hgS _ (rsw_mem_atom ha)
  have e0 : σ (.n 0) = ofK (gpow bz) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count]) rsw_chk
      (by simp)
  have e1 : σ (.n 1) = ofK (gpow bp) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count]) rsw_chk
      (by simp)
  have e2 : σ (.n 2) = ofK (gpow bc) := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count]) rsw_chk
      (by simp)
  have e3 : σ (.n 3) = gen ^ count := by
    rw [hσdef]
    exact ev_params rd _ (l := [ofK (gpow bz), ofK (gpow bp), ofK (gpow bc), gen ^ count]) rsw_chk
      (by simp)
  have mulE : ∀ d u v : ℕ, u < d → v < d → Stmt.atom (.mul (.n d) (.n u) (.n v)) ∈ rswPre →
      σ (.n d) = σ (.n u) * σ (.n v) := by
    intro d u v hu hv hm
    have := hg _ (rsw_atom_mem hm)
    simp only [Good] at this
    rwa [ite_pos' ⟨hu, hv⟩] at this
  have constE : ∀ d : ℕ, ∀ c : E, Stmt.atom (.const (.n d) c) ∈ rswPre → σ (.n d) = c :=
    fun d c h ↦ hg _ (rsw_atom_mem h)
  have hmem : ∀ a, Stmt.atom a ∈ [Stmt.atom (.const (.n 4) (word 2 0 0)),
      .atom (.mul (.n 5) (.n 3) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 5)),
      .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 7) (.n 7)),
      .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 9)),
      .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.hint (.allocDyn (.n 12) (.n 11)))] →
      Stmt.atom a ∈ rswPre := fun a h ↦ by
    simp only [rswPre, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  have e4 := constE 4 (word 2 0 0) (hmem _ (by simp))
  have e5 := mulE 5 3 4 (by omega) (by omega) (hmem _ (by simp))
  have e6 := mulE 6 5 5 (by omega) (by omega) (hmem _ (by simp))
  have e7 := mulE 7 6 6 (by omega) (by omega) (hmem _ (by simp))
  have e8 := mulE 8 7 7 (by omega) (by omega) (hmem _ (by simp))
  have e9 := mulE 9 8 8 (by omega) (by omega) (hmem _ (by simp))
  have e10 := mulE 10 9 9 (by omega) (by omega) (hmem _ (by simp))
  have e11 := mulE 11 10 10 (by omega) (by omega) (hmem _ (by simp))
  have e12 : σ (.n 12) = ofK (gpow bb) := by
    have := hg _ (rsw_atom_mem (hmem _ (by simp)) : Atom.hint (.allocDyn (.n 12) (.n 11)) ∈ rswA)
    simpa [Good, rswW] using this
  have e77 : σ (.n 77) = ofK (gpow bb) * gen ^ (64 * rswH count) := by
    have := hgS (.call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77]) (by simp [rswPre])
    simpa [GoodS, rswW] using this
  have h11 : σ (.n 11) = ofK (gpow (64 * (count + 1))) := by
    rw [e11, e10, e9, e8, e7, e6, e5, e3, e4, word_gen, ← gen_pow_eq_ofK]
    ring
  -- the coefficients and the chain's last row
  have notS : ∀ d p off, p ≠ (.n 12 : V) → Atom.load d p off ∉ S := by
    intro d p off hp hm
    rw [hS] at hm
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hm
    simp only [Atom.load.injEq] at hk
    exact hp hk.2.1.symm
  have loadE : ∀ d p off, Stmt.atom (.load (.n d) p off) ∈ rswPre → p ≠ (.n 12 : V) →
      σ (.n d) = rdAt rd (σ p) off := by
    intro d p off hm hp
    rcases (hg _ (rsw_atom_mem hm) : Good rd S _ σ _) with h | h
    · exact absurd h (notS _ _ _ hp)
    · exact h
  have hrowH : ∀ k < 64, LoadHolds rd (σ (.n 77)) k (ringRow 1 zs ps k) := by
    intro k hk
    rw [e77, loadHolds_mul_gen_pow]
    have := rswChain_load hch (t := 64 * rswH count + k) (by omega)
    rcases Nat.eq_zero_or_pos count with h0 | hpos
    · subst h0
      have hz0 : zs = [] := List.length_eq_zero_iff.mp hz
      have hp0 : ps = [] := List.length_eq_zero_iff.mp hp
      subst hz0 hp0
      simp only [rswH, Nat.zero_add, Nat.reduceDiv, mul_zero, Nat.zero_add] at this ⊢
      rw [ite_pos' (by omega)] at this
      simpa [ringRow] using this
    · have hH : 1 ≤ rswH count := by unfold rswH; omega
      rw [ite_neg' (by omega), show (64 * rswH count + k) / 64 = rswH count by omega,
        show (64 * rswH count + k) % 64 = k by omega,
        show min (2 * rswH count) count = count by unfold rswH; omega,
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      exact this
  have hcsk : ∀ k < 64, LoadHolds rd (σ (.n 2)) k (cs.getD k 0) := by
    intro k hk
    rw [e2, List.getD_eq_getElem _ _ (by omega)]
    exact hcs k (by omega)
  have hterm : ∀ k < 64, σ (.n (rswC k)) = cs.getD k 0 ∧ σ (.n (rswP k)) = ringRow 1 zs ps k ∧
      σ (.n (rswM k)) = σ (.n (rswC k)) * σ (.n (rswP k)) ∧
      (k ≠ 0 → σ (.n (4 * k + 80)) = σ (.n (4 * (k - 1) + 80)) + σ (.n (rswM k))) := by
    intro k hk
    have mem := rswTerm_mem hk
    have hne2 : (.n 2 : V) ≠ .n 12 := by decide
    have hne77 : (.n 77 : V) ≠ .n 12 := by decide
    unfold rswTerm at mem
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte] at mem
      have l1 := loadE 78 (.n 2) 0 (mem _ (by simp)) hne2
      have l2 := loadE 79 (.n 77) 0 (mem _ (by simp)) hne77
      have m := mulE 80 78 79 (by omega) (by omega) (mem _ (by simp))
      refine ⟨?_, ?_, m, fun h ↦ absurd rfl h⟩
      · rw [show rswC 0 = 78 from rfl, l1, rt_rdAt_of_load (hcsk 0 (by omega))]
      · rw [show rswP 0 = 79 from rfl, l2, rt_rdAt_of_load (hrowH 0 (by omega))]
    · simp only [hk0, ↓reduceIte] at mem
      have l1 := loadE (4 * k + 77) (.n 2) k (mem _ (by simp)) hne2
      have l2 := loadE (4 * k + 78) (.n 77) k (mem _ (by simp)) hne77
      have m := mulE (4 * k + 79) (4 * k + 77) (4 * k + 78) (by omega) (by omega) (mem _ (by simp))
      have a := (hg _ (rsw_atom_mem (mem (.atom (.add (.n (4 * k + 80)) (.n (4 * k + 76))
        (.n (4 * k + 79)))) (by simp))) : σ (.n (4 * k + 80)) = σ (.n (4 * k + 76)) +
          σ (.n (4 * k + 79)))
      simp only [rswC, rswP, rswM, hk0, ↓reduceIte]
      refine ⟨by rw [l1, rt_rdAt_of_load (hcsk k hk)], by rw [l2, rt_rdAt_of_load (hrowH k hk)], m,
        fun _ ↦ ?_⟩
      rw [a, show 4 * (k - 1) + 80 = 4 * k + 76 by omega]
  -- the atoms
  have hside : ∀ a ∈ rswA, a ∉ S → needsSide a = true → a.Holds rd σ ∨ Side rd S σ a := by
    intro a ha haS hns
    right
    have hok := List.all_eq_true.mp rsw_needs a ha
    have hld := List.all_eq_true.mp rsw_loadOk a ha
    rw [rsw_stores, ← hS] at hok
    simp only [hns, Bool.not_true, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with h | h
    · exact absurd h haS
    · cases a with
      | load d p off =>
        simp only [rswLoadOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hld h
        simp only [Side, ite_neg' haS]
        rcases h with rfl | rfl
        · exact rt_side_of_load (hcsk off hld.1)
        · exact rt_side_of_load (hrowH off hld.1)
      | _ => simp at h
  have hat : ∀ a ∈ rswA, a.Holds rd σ := by
    have hσv : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσdef]; rfl
    refine atoms_holds_stores (S := S) (w := rswW bb (rswH count)) (A := []) hσv ?_ hg
      (fun i hi => absurd hi (by simp)) hside ?_
    · have := rsw_canon; rw [rsw_stores, ← hS] at this; exact this
    · intro _ a _ haS
      rw [hS] at haS
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp haS
      have hk' := List.mem_range.mp hk
      have hc1 := constE (13 + k) (word 1 0 0) (rswInit_mem hk' _ (by simp [rswInit]))
      show LoadHolds rd (σ (.n 12)) k (σ (.n (13 + k)))
      rw [e12, hc1, word_one]
      have := rswChain_load hch (t := k) (by unfold rswH; omega)
      rwa [ite_pos' (by omega : k / 64 = 0)] at this
  refine ⟨hat, h11, e12, e77, ?_⟩
  have hcopy : σ (.n 333) = σ (.n 332) :=
    hg _ (rsw_atom_mem (by simp [rswPre] : Stmt.atom (.copy (.n 333) (.n 332)) ∈ rswPre))
  rw [hcopy, show (332 : ℕ) = 4 * 63 + 80 from rfl,
    rsw_acc (fun k hk => (hterm k hk).2.2.2) 63 (by decide), ringWeight_eq, hc]
  refine gsum_congr fun k hk => ?_
  rw [(hterm k hk).2.2.1, (hterm k hk).1, (hterm k hk).2.1,
    rwProd_eq_ringRow k zs ps _ (by rw [hz, hp])]

end
end LeanVM.Guest.B1.VerifySub
