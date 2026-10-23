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

end
end LeanVM.Guest.B1.VerifySub
